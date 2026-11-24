# Has Deriv At rot Matrix mul Vec

Derivative of the action along the body-rate kinematics: if `q' = (1/2) q (0, ω_B)` at `t`,
then for every vector `v`, `(R v)' = R (ω_B ⨯₃ v)` with `R = rotMatrix q`. This is the form
`R' v = R (ω_B × v)` of Physlib's rigid-body angular velocity.
