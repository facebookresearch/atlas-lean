# Angle Jacobian

The angle derivative of the position map at `q`, the derivative of `posMap`
(`hasFDerivAt_posMap`): angular velocities `w = (w₁, w₂)` go to the Cartesian velocities
`(vel₁ l₁ q₁ w₁, vel₂ l₁ l₂ q₁ q₂ w₁ w₂)` (`angleJacobian_apply`).
