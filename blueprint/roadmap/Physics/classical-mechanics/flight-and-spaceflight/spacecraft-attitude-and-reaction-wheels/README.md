# Spacecraft attitude and reaction wheels

## Quaternion kinematics and the rotation matrix

- [Pure quaternion with given imaginary coordinates](pure-quat.md)
- [Rate of a rotated vector under body-rate quaternion kinematics](has-deriv-at-rot-matrix-mul-vec.md)
- [Rotation-matrix kinematics from body-rate quaternion kinematics](has-deriv-at-rot-matrix.md)
- [For a unit quaternion the vee of Rᵀ R' is the body rate](cross-product-vee-transpose-mul-deriv-ro.md)
- [Body-rate quaternion kinematics keep a unit quaternion unit](norm-eq-one-of-has-deriv-at.md)
- [Rotation-matrix kinematics with the rate multiplied on the left](has-deriv-at-rot-matrix-of-left.md)

## Reaction-wheel momentum and admissibility

- [Admissible reaction-wheel command on a finite horizon](wheel-admissible.md)
- [Rate of the total angular momentum of a body with a reaction wheel](has-deriv-at-wheel-total-momentum.md)
- [Without external torque, wheel and body exchange angular momentum](wheel-momentum-exchange.md)
- [Wheel admissibility as a condition on the command and initial momentum](wheel-admissible-iff-integral.md)
- [A momentum reserve makes every bounded wheel command admissible](wheel-admissible-of-reserve.md)
- [A constant wheel command is admissible iff the endpoint limits hold](const-command-admissible-iff.md)
- [A nonzero constant wheel command saturates the momentum in finite time](const-command-momentum-limit.md)

## Saturated rate feedback and a feasible trajectory

- [Saturation to a symmetric interval](clip.md)
- [Body torque of the saturated rate feedback](body-torque.md)
- [Wheel command taking the reaction of the body torque](wheel-command.md)
- [Exponentially decaying body-rate trajectory](rate-trajectory.md)
- [Wheel momentum along the decaying rate trajectory](wheel-momentum.md)
- [The trajectory stays in the unclipped interval](rate-trajectory-unsaturated.md)
- [The trajectory solves the reduced wheel plant](trajectory-reduced-plant.md)
- [The wheel command along the trajectory stays within its limit](abs-wheel-command-le.md)
- [A momentum reserve bounds the wheel momentum at all later times](abs-wheel-momentum-le.md)
- [A feasible trajectory for the reduced wheel plant](trajectory-wheel-admissible.md)
- [Outside the unclipped interval the exponential fails the closed loop](rate-trajectory-not-closed-loop.md)

## Residual tracking

- [The clipped feedback field is globally Lipschitz](lipschitz-with-body-torque-div.md)
- [Residual tracking against the feasible trajectory](abs-sub-rate-trajectory-le-gronwall-boun.md)
- [The finite-horizon rate error in physical units](abs-sub-rate-trajectory-le.md)
