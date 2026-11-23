# Buoyancy deriv rewrite

Algebraic rewrite of the buoyancy law: if `v` has derivative
`g * (theta0 - (theta0 + a * zeta t)) / theta0` at `t`, it has derivative
`-(g * a / theta0) * zeta t`. This only rewrites the derivative value. It
does not relate `v` to the derivative of `zeta`, so it is not an
oscillator equation; `static_stability_oscillator` adds that relation.
