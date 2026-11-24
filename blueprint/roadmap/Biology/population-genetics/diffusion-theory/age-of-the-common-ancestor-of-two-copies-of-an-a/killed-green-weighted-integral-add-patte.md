# Weighted integral of the killed Green's function plus a₁ is y

For `0 < y < 1`,

`y (1 - y) ∫₀¹ G_C(x, y) / (x (1 - x)) dx + a₁(y) = y`,

where [`G_C`](killed-green.md) is the killed Green's function and [`a₁`](patterson-aux1.md)
Patterson's first solution, with `a₁(y) = y (1 - y) lim_{ε → 0⁺} G_C(1 - ε, y) / (2ε)`
([boundary ratio](tendsto-killed-green-one-sub-div.md)). Integrating Patterson's Equation 14 over
time writes the expected age of the most recent common ancestor of two copies at unknown ancestry as
`y (1 - y) [∫₀¹ G_C(x, y) / (x (1 - x)) dx + lim_{ε → 0⁺} G_C(1 - ε, y) / (2ε)]`, so the identity is
the analytic content of his Theorem 5(2): that age is `y` in units of `2N` generations, that is
`2Ny` generations. His own proof is a martingale argument.

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
