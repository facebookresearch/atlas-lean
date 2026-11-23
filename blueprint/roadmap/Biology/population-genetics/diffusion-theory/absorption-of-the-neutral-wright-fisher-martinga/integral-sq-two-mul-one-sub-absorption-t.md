# Forward squared-heterozygosity functional

For a solution of the neutral
Wright-Fisher martingale problem started at frequency `x`, the expected squared
heterozygosity accumulated until absorption, in diffusion units (multiples of `2N`
generations), is `(2/3) x(1-x)(1+x-x^2)`. This is a derived corollary of the
Maruyama-Kimura functional machinery with `K = g`, `g(y) = (2y(1-y))^2` and boundary
values `0` at both endpoints, in the repository scaling. It is the occupation of the
squared integrand, not the second moment of the accumulated heterozygosity functional.
