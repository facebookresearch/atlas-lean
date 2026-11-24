# Paris Crack Pow

Paris-law crack-growth solution, power branch. With growth exponent
`m ≠ 2` and coefficient `K > 0` in `da/dN = K * a ^ (m / 2)`, writing
`r = 1 - m / 2 ≠ 0`, the solution with `a(0) = a0` is
`a(N) = (a0 ^ r + r * K * N) ^ (1 / r)`. It is valid only while the base
`a0 ^ r + r * K * N` stays positive; for `r < 0` (that is, `m > 2`) that
is a finite cycle interval. Real powers are `Real.rpow`.
