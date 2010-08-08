/**
 * traer.js
 * A particle-based physics engine ported from Jeff Traer's Processing library to JavaScript. This version is intended for use with the HTML5 canvas element.
 *
 * @author Adam Saponara <saponara TA gmail TOD com> (JavaScript port)
 * @author Jeffrey Traer Bernstein <jeff TA traer TOD cc> (original Java library)
 * @version 0.2
 * @date August 8, 2010
 *
 */


/**
 * A 3-dimensional vector representation with common vector operations
 */
function Vector() {
	var argc = arguments.length;
	if (argc == 3) {
		this.x = arguments[0];
		this.y = arguments[1];
		this.z = arguments[2];
	}
	else if (argc == 1) {
		this.x = arguments[0].x;
		this.y = arguments[0].y;
		this.z = arguments[0].z;
	}
	else {
		this.x = 0;
		this.y = 0;
		this.z = 0;
	}
}
Vector.prototype.set = function() {
	var argc = arguments.length;
	if (argc == 3) {
		this.x = arguments[0];
		this.y = arguments[1];
		this.z = arguments[2];
	}
	else if (argc == 1) {
		this.x = arguments[0].x;
		this.y = arguments[0].y;
		this.z = arguments[0].z;
	}
}
Vector.prototype.add = function(v) {
	var argc = arguments.length;
	if (argc == 3) {
		this.x += arguments[0];
		this.y += arguments[1];
		this.z += arguments[2];
	}
	else if (argc == 1) {
		this.x += arguments[0].x;
		this.y += arguments[0].y;
		this.z += arguments[0].z;
	}
}
Vector.prototype.substract = function(v) {
	var argc = arguments.length;
	if (argc == 3) {
		this.x -= arguments[0];
		this.y -= arguments[1];
		this.z -= arguments[2];
	}
	else if (argc == 1) {
		this.x -= arguments[0].x;
		this.y -= arguments[0].y;
		this.z -= arguments[0].z;
	}
}
Vector.prototype.scale = function(f) { this.x *= f; this.y *= f; this.z *= f; }
Vector.prototype.distanceTo = function() { 
	var argc = arguments.length;
	if (argc == 3) {
		var dx = this.x - arguments[0];
		var dy = this.y - arguments[1];
		var dz = this.z - arguments[2];
		return Math.sqrt(dx*dx + dy*dy + dz*dz);
	}
	else if (argc == 1) {
		return Math.sqrt(this.distanceSquaredTo(v))
	}
}
Vector.prototype.distanceSquaredTo = function(v) {
	var dx = this.x - v.x;
	var dy = this.y - v.y;
	var dz = this.z - v.z;
	return dx*dx + dy*dy + dz*dz;
}
Vector.prototype.dot = function(v) { return this.x*v.x + this.y*v.y + this.z*v.z; }
Vector.prototype.length = function() { return Math.sqrt(this.x*this.x + this.y*this.y + this.z*this.z); }
Vector.prototype.lengthSquared = function() { return this.x*this.x + this.y*this.y + this.z*this.z; }
Vector.prototype.clear = function() { this.x = 0; this.y = 0; this.z = 0; }
Vector.prototype.toString = function() { return '('+this.x+','+this.y+','+this.z+')'; }
Vector.prototype.cross = function(v) {
	return new Vector(
		this.y*v.z - this.z*v.y,
		this.x*v.z - this.z*v.x,
		this.x*v.y - this.y*v.x
	);
}
Vector.prototype.isZero = function() {
	return this.x === 0 && this.y === 0 && this.z === 0;
}


/**
 * A particle with position, velocity, and force vectors and mass
 */
function Particle(mass) {
	this.position = new Vector();
	this.velocity = new Vector();
	this.force = new Vector();
	this.mass = mass;
	this.fixed = false;
	this.age = 0;
	this.dead = false;
}
Particle.prototype.distanceTo = function(p) { return this.position().distanceTo(p.position()); }
Particle.prototype.makeFixed = function() { this.fixed = true; this.velocity.clear(); }
Particle.prototype.reset = function() {
	this.age = 0;
	this.dead = false;
	this.position.clear();
	this.velocity.clear();
	this.force.clear();
	this.mass = 1.0;
}


/**
 * A force between two particles based on a spring constant
 */
function Spring(a, b, k, d, l) {
	this.constant = k;
	this.damping = d;
	this.length = l;
	this.a = a;
	this.b = b;
	this.on = true;
}
Spring.prototype.currentLength = function() { return this.a.position().distanceTo(this.b.position()); }
Spring.prototype.apply = function() {

	var a = this.a;
	var b = this.b;
	if (!(this.on && (!a.fixed || !b.fixed))) return;

	var a2bx = a.position.x - b.position.x;
	var a2by = a.position.y - b.position.y;
	var a2bz = a.position.z - b.position.z;

	var a2bd = Math.sqrt(a2bx*a2bx + a2by*a2by + a2bz*a2bz);
	if (a2bd == 0) {
		a2bx = 0;
		a2by = 0;
		a2bz = 0;
	}
	else {
		a2bx /= a2bd;
		a2by /= a2bd;
		a2bz /= a2bd;
	}

	var fspring = -1 * (a2bd - this.length) * this.constant;

	var va2bx = a.velocity.x - b.velocity.x;
	var va2by = a.velocity.y - b.velocity.y;
	var va2bz = a.velocity.z - b.velocity.z;

	var fdamping = -1 * this.damping * (a2bx*va2bx + a2by*va2by + a2bz*va2bz);

	var fr = fspring + fdamping;

	a2bx *= fr;
	a2by *= fr;
	a2bz *= fr;

	if (!a.fixed) a.force.add(a2bx, a2by, a2bz);
	if (!b.fixed) b.force.add(-1 * a2bx, -1 * a2by, -1 * a2bz);

}

/**
 * Applies physics rules to a collection of particles
 */
function ParticleSystem() {

	this.particles = [];
	this.springs = [];
	this.attractions = [];
	this.forces = [];
	this.integrator = new RungeKuttaIntegrator(this);
	this.hasDeadParticles = false;

	var argc = arguments.length;
	if (argc == 2) {
		this.gravity = new Vector(0, arguments[0], 0);
		this.drag = arguments[1];
	}
	else if (argc == 4) {
		this.gravity = new Vector(arguments[0], arguments[1], arguments[2]);
		this.drag = arguments[3];
	}
	else {
		this.gravity = new Vector(0, ParticleSystem.DEFAULT_GRAVITY, 0);
		this.drag = ParticleSystem.DEFAULT_DRAG;
	}
}
ParticleSystem.DEFAULT_GRAVITY = 0;
ParticleSystem.DEFAULT_DRAG = 0.001;
/**
 * @todo Implement other integrators

ParticleSystem.RUNGE_KUTTA = 0;
ParticleSystem.EULER = 1;
ParticleSystem.MODIFIED_EULER = 2;

ParticleSystem.prototype.setIntegrator = function(integrator) {
	switch (integrator) {
		case ParticleSystem.RUNGE_KUTTA:
			this.integrator = new RungeKuttaIntegrator(this);
			break;
		case ParticleSystem.EULER:
			this.integrator = new EulerIntegrator(this);
			break;
		case ParticleSystem.MODIFIED_EULER:
			this.integrator = new ModifiedEulerIntegrator(this);
			break;
	}
}
 */
ParticleSystem.prototype.setGravity = function () {
	var argc = arguments.length;
	if (argc == 1) {
		this.gravity.set(0, arguments[0], 0);
	}
	else if (argc == 3) {
		this.gravity.set(arguments[0], arguments[1], arguments[2]);
	}
}
ParticleSystem.prototype.tick = function() {
	this.integrator.step(arguments.length == 0 ? 1 : arguments[0]);
}
ParticleSystem.prototype.makeParticle = function() {
	var mass = 1.0;
	var x = 0;
	var y = 0;
	var z = 0;
	if (arguments.length == 4) {
		mass = arguments[0];
		x = arguments[1];
		y = arguments[2];
		z = arguments[3];
	}
	var p = new Particle(mass);
	p.position.set(x, y, z);
	this.particles.push(p);
	return p;
}
ParticleSystem.prototype.makeSpring = function(a, b, k, d, l) {
	var s = new Spring(a, b, k, d, l);
	this.springs.push(s);
	return s;
}
ParticleSystem.prototype.makeAttraction = function(a, b, k, d) {
	var m = new Attraction(a, b, k, d);
	this.attractions.push(m);
	return m;
}
ParticleSystem.prototype.clear = function() {
	this.particles.clear();
	this.springs.clear();
	this.attractions.clear();
}
ParticleSystem.prototype.applyForces = function() {

	var t;

	if (!this.gravity.isZero()) {
		for (var i = 0; i < this.particles.length; i++) {
			t = this.particles[i];
			t.force.add(this.gravity);
		}
	}

	for (var i = 0; i < this.particles.length; i++) {
		t = this.particles[i];
		t.force.add(t.velocity.x * -1 * this.drag, t.velocity.y * -1 * this.drag, t.velocity.z * -1 * this.drag);
	}

	for (var i = 0; i < this.springs.length; i++) {
		t = this.springs[i];
		t.apply();
	}

	for (var i = 0; i < this.attractions.length; i++) {
		t = this.attractions[i];
		t.apply();
	}

	for (var i = 0; i < this.forces.length; i++) {
		t = this.forces[i];
		t.apply();
	}

}
ParticleSystem.prototype.clearForces = function() {
	for (var i = 0; i < this.particles.length; i++) {
		this.particles[i].clear();
	}
}

/**
 * Fourth-order integration approximator
 */
function RungeKuttaIntegrator(s) {
	this.s = s;
	this.originalPositions = [];
	this.originalVelocities = [];
	this.k1Forces = [];
	this.k1Velocities = [];
	this.k2Forces = [];
	this.k2Velocities = [];
	this.k3Forces = [];
	this.k3Velocities = [];
	this.k4Forces = [];
	this.k4Velocities = [];
}
RungeKuttaIntegrator.prototype.allocateParticles = function() {
	while (this.s.particles.length > this.originalPositions.length) {
		this.originalPositions.push(new Vector());
		this.originalVelocities.push(new Vector());
		this.k1Forces.push(new Vector());
		this.k1Velocities.push(new Vector());
		this.k2Forces.push(new Vector());
		this.k2Velocities.push(new Vector());
		this.k3Forces.push(new Vector());
		this.k3Velocities.push(new Vector());
		this.k4Forces.push(new Vector());
		this.k4Velocities.push(new Vector());
	}
}
RungeKuttaIntegrator.prototype.step = function (deltaT) {
	var s = this.s;
	var p;

	this.allocateParticles();

	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			this.originalPositions[i].set(p.position);
			this.originalVelocities[i].set(p.velocity);
		}
		p.force.clear();	// and clear the forces
	}

	////////////////////////////////////////////////////////
	// get all the k1 values

	s.applyForces();

	// save the intermediate forces
	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			this.k1Forces[i].set(p.force);
			this.k1Velocities[i].set(p.velocity);
		}

		p.force.clear();
	}

	////////////////////////////////////////////////////////////////
	// get k2 values

	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			var originalPosition = this.originalPositions[i];
			var k1Velocity = this.k1Velocities[i];
			p.position.x = originalPosition.x + k1Velocity.x * 0.5 * deltaT;
			p.position.y = originalPosition.y + k1Velocity.y * 0.5 * deltaT;
			p.position.z = originalPosition.z + k1Velocity.z * 0.5 * deltaT;
			var originalVelocity = this.originalVelocities[i];
			var k1Force = this.k1Forces[i];
			p.velocity.x = originalVelocity.x + k1Force.x * 0.5 * deltaT / p.mass;
			p.velocity.y = originalVelocity.y + k1Force.y * 0.5 * deltaT / p.mass;
			p.velocity.z = originalVelocity.z + k1Force.z * 0.5 * deltaT / p.mass;
		}
	}

	s.applyForces();

	// save the intermediate forces
	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			this.k2Forces[i].set(p.force);
			this.k2Velocities[i].set(p.velocity);
		}
		p.force.clear();	// and clear the forces now that we are done with them
	}


	/////////////////////////////////////////////////////
	// get k3 values

	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			var originalPosition = this.originalPositions[i];
			var k2Velocity = this.k2Velocities[i];
			p.position.x = originalPosition.x + k2Velocity.x * 0.5 * deltaT;
			p.position.y = originalPosition.y + k2Velocity.y * 0.5 * deltaT;
			p.position.z = originalPosition.z + k2Velocity.z * 0.5 * deltaT;
			var originalVelocity = this.originalVelocities[i];
			var k2Force = this.k2Forces[i];
			p.velocity.x = originalVelocity.x + k2Force.x * 0.5 * deltaT / p.mass;
			p.velocity.y = originalVelocity.y + k2Force.y * 0.5 * deltaT / p.mass;
			p.velocity.z = originalVelocity.z + k2Force.z * 0.5 * deltaT / p.mass;
		}
	}

	s.applyForces();

	// save the intermediate forces
	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			this.k3Forces[i].set(p.force);
			this.k3Velocities[i].set(p.velocity);
		}
		p.force.clear();	// and clear the forces now that we are done with them
	}


	//////////////////////////////////////////////////
	// get k4 values
	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			var originalPosition = this.originalPositions[i];
			var k3Velocity = this.k3Velocities[i];
			p.position.x = originalPosition.x + k3Velocity.x * deltaT;
			p.position.y = originalPosition.y + k3Velocity.y * deltaT;
			p.position.z = originalPosition.z + k3Velocity.z * deltaT;
			var originalVelocity = this.originalVelocities[i];
			var k3Force = this.k3Forces[i];
			p.velocity.x = originalVelocity.x + k3Force.x * deltaT / p.mass;
			p.velocity.y = originalVelocity.y + k3Force.y * deltaT / p.mass;
			p.velocity.z = originalVelocity.z + k3Force.z * deltaT / p.mass;
		}
	}

	s.applyForces();

	// save the intermediate forces
	for (var i = 0; i < s.particles.length; i++) {
		p = s.particles[i];
		if (!p.fixed) {
			this.k4Forces[i].set(p.force);
			this.k4Velocities[i].set(p.velocity);
		}
	}

	/////////////////////////////////////////////////////////////
	// put them all together and what do you get?

	for (var i = 0; i < s.particles.length; i++) {

		p = s.particles[i];
		p.age += deltaT;
		if (p.fixed) continue;

		// update position
		var originalPosition = this.originalPositions[i];
		var k1Velocity = this.k1Velocities[i];
		var k2Velocity = this.k2Velocities[i];
		var k3Velocity = this.k3Velocities[i];
		var k4Velocity = this.k4Velocities[i];
		p.position.x = originalPosition.x + deltaT / 6.0 * (k1Velocity.x + 2.0*k2Velocity.x + 2.0*k3Velocity.x + k4Velocity.x);
		p.position.y = originalPosition.y + deltaT / 6.0 * (k1Velocity.y + 2.0*k2Velocity.y + 2.0*k3Velocity.y + k4Velocity.y);
		p.position.z = originalPosition.z + deltaT / 6.0 * (k1Velocity.z + 2.0*k2Velocity.z + 2.0*k3Velocity.z + k4Velocity.z);

		// update velocity
		var originalVelocity = this.originalVelocities[i];
		var k1Force = this.k1Forces[i];
		var k2Force = this.k2Forces[i];
		var k3Force = this.k3Forces[i];
		var k4Force = this.k4Forces[i];
		p.velocity.x = originalVelocity.x + deltaT / (6.0 * p.mass) * (k1Force.x + 2.0*k2Force.x + 2.0*k3Force.x + k4Force.x);
		p.velocity.y = originalVelocity.y + deltaT / (6.0 * p.mass) * (k1Force.y + 2.0*k2Force.y + 2.0*k3Force.y + k4Force.y);
		p.velocity.z = originalVelocity.z + deltaT / (6.0 * p.mass) * (k1Force.z + 2.0*k2Force.z + 2.0*k3Force.z + k4Force.z);
	}
}


/**
 * remove method of Array type
 * @param o    If a number, removes the corresponding index. Else, removes any elements that match parameter in type & value.
 */
Array.prototype.remove = function(o) {
	if (typeof o == 'number') {
		this.splice(o, 1);
	}
	else {
		var tokill = [];
		for (var i = 0; i < this.length; i++) {
			if (this[i] === o) {
				this.remove(i);
				i--;
			}
		}
	}

}
