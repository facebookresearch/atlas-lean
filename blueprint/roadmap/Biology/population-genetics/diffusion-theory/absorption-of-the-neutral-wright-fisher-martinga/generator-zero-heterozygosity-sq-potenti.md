# Generator zero heterozygosity Sq Potential

Neutral generator applied to the squared-heterozygosity potential: for every real `y`
(no restriction to the unit interval),
`generator 0 (fun z => (2/3) z(1-z)(1+z-z^2)) y = -((2y(1-y))^2)`, pointwise in `y`. The
potential vanishes at both endpoints, `u(0) = u(1) = 0`, with `u''(y) = -8y(1-y)`; time is
in diffusion units (multiples of `2N` generations). This is a pointwise
ordinary-differential-equation identity and makes no claim about any process.
