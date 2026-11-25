# Constrained two-link pendulum

## Cartesian positions, rod constraints and the frame convention

- [Position of the first mass of the two-link pendulum](pos.md)
- [Position of the second mass of the two-link pendulum](pos-2.md)
- [For nonnegative lengths, the positions satisfy the rod constraints](pos-rod-constraints.md)
- [Embedding of the pendulum plane into three-dimensional coordinates](to-space.md)
- [Each link is a body frame rotated by its absolute angle](to-space-pos-eq-body-to-inertial.md)

## Velocities on actual angle trajectories

- [Velocity of the first mass at a given angular velocity](vel.md)
- [Velocity of the second mass at given angular velocities](vel-2.md)
- [Velocities of the masses along a differentiable angle trajectory](has-deriv-at-pos.md)

## Kinetic energy, potential energy and the Lagrangian

- [Kinetic energy of the two-link pendulum](kinetic-energy.md)
- [Gravitational potential energy of the two-link pendulum](potential-energy.md)
- [Lagrangian of the two-link pendulum in the link angles](lagrangian.md)
- [Reduced mass matrix of the two-link pendulum](mass-matrix.md)
- [The kinetic energy is half the mass-matrix quadratic form](kinetic-energy-eq-mass-matrix.md)
- [Kinetic energy of the actual velocities along an angle trajectory](kinetic-energy-actual.md)
- [Potential energy in terms of the link angles](potential-energy-eq.md)
- [Explicit Lagrangian of the coplanar double pendulum](lagrangian-eq.md)

## Determinant of the reduced mass matrix

- [Determinant of the reduced mass matrix](mass-matrix-det.md)
- [For positive masses and lengths, the determinant is positive](mass-matrix-det-pos.md)
- [For positive masses and lengths, kinetic energy is positive definite](kinetic-energy-pos.md)
- [With collinear links, the determinant is m₁ m₂ l₁² l₂²](mass-matrix-det-of-collinear.md)
- [A zero link length makes the mass matrix singular](mass-matrix-det-eq-zero-of-length-eq-zer.md)

## The rod constraints and their Jacobian

- [Map from link angles to the positions of the two masses](pos-map.md)
- [Rod constraint map on Cartesian configurations](rod-constraint.md)
- [Jacobian of the rod constraints](rod-jacobian.md)
- [Derivative of the angle-to-position map](angle-jacobian.md)
- [The angle-to-position map satisfies the rod constraints](rod-constraint-pos-map.md)
- [Formula for the rod constraint Jacobian](rod-jacobian-apply.md)
- [The rod Jacobian is the derivative of the constraint map](has-fderiv-at-rod-constraint.md)
- [The angle derivative gives the velocities of the masses](angle-jacobian-apply.md)
- [The angle derivative is the derivative of the position map](has-fderiv-at-pos-map.md)
- [For positive lengths, the rod Jacobian has rank two](rod-jacobian-rank-two.md)

## Velocities allowed by the rod constraints

- [For positive lengths, the angle derivative is injective](ker-angle-jacobian.md)
- [For positive lengths, the angle derivative maps onto the rod kernel](range-angle-jacobian.md)
- [Velocities of constrained curves lie in the rod kernel](rod-jacobian-velocity-eq-zero.md)
- [For positive lengths each kernel vector has a unique angular velocity](exists-unique-has-deriv-at-pos-map.md)

## Rod reactions and virtual work

- [Rod-normal reaction forces with given multipliers](rod-reaction.md)
- [Virtual work of a force pair along a velocity pair](virtual-work.md)
- [Rod-normal reactions do no virtual work along the rod kernel](virtual-work-rod-reaction-eq-zero.md)
- [Rod reactions do no work along velocities of the chain](virtual-work-rod-reaction-angle-jacobian.md)
- [For positive lengths, workless force pairs are rod reactions](exists-unique-rod-reaction.md)

## The reduced Euler–Lagrange equation

- [Two-link Lagrangian on angle and angular-velocity vectors](angle-lagrangian.md)
- [Generalized force of the two-link pendulum](generalized-force.md)
- [Reduced acceleration of the two-link pendulum by Cramer's rule](reduced-accel.md)
- [For positive masses and lengths, the reduced acceleration is M⁻¹ f](reduced-accel-eq-inv-mul-vec.md)
- [Euler–Lagrange operator of the two-link pendulum](euler-lagrange-op-angle-lagrangian.md)
- [For positive masses and lengths, Euler–Lagrange is the reduced ODE](euler-lagrange-op-angle-lagrangian-eq-ze.md)

## Newton's equations with rod reactions

- [Cartesian motion of the masses along an angle trajectory](cartesian-motion.md)
- [Gravity forces on the two masses](gravity-force.md)
- [For m, l > 0, Newton admits some rod reaction iff the reduced ODE](exists-rod-reaction-newton-iff.md)
- [For m, l > 0, Newton admits a unique rod reaction iff the reduced ODE](exists-unique-rod-reaction-newton-iff.md)

## Local regularity and the local initial value problem

- [First-order field of the reduced two-link equations](reduced-field.md)
- [For positive masses and lengths, the reduced field is smooth](cont-diff-reduced-field.md)
- [Positive masses and lengths make the reduced field locally Lipschitz](locally-lipschitz-reduced-field.md)
- [For positive masses and lengths, the reduced field has local solutions](exists-forall-mem-ioo-has-deriv-at-reduc.md)
- [Positive masses and lengths give local Euler–Lagrange solutions](exists-euler-lagrange-op-angle-lagrangia.md)
