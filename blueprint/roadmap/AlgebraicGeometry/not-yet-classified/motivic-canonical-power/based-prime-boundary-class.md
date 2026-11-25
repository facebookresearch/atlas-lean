# Based Prime Boundary Class

The based class $c$ (Voevodsky, Theorem 6.14): over a perfect field $k$, for a prime $ℓ$
invertible in $k$, the given motivic interface data and canonical affine source, a base point
`point` of the geometric approximation of $BS_ℓ$, a universal Thom class `t` of its permutation
bundle diagram and the given integral Bockstein data `delta`, there is a class
$c ∈ \tilde H^{2ℓ-3, ℓ-1}(BS_ℓ, \mathbb Z/ℓ)$ whose integral Bockstein is the integral Euler class
(the pullback of `t` along the zero section, whose reduction mod $ℓ$ is $d$) and whose pullback to
the base point vanishes (`BasedIntegralLift`).
