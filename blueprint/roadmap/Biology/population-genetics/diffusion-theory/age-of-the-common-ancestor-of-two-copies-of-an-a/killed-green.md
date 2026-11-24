# Green's function of the diffusion killed at coalescence

For real numbers `x` and `y`, let

`G_C(x, y) = -2 (x² + 2x log(1 - x) - 2x - 2 log(1 - x)) / (y² x)` if `x ≤ y`,

`G_C(x, y) = 2 (1 - x) (2y - y² + 2 log(1 - y) - 2y log(1 - y)) / ((1 - y) y² x)` if `x > y`,

with the conventions `u / 0 = 0`, `log u = log |u|` and `log 0 = 0`; for instance `G_C(x, y) = 0`
when `x = 0`, when `y = 0`, and when `x > y = 1`. The intended domain is `0 < x, y < 1`. There `G_C`
is Patterson's Theorem 4: the Green's function of the neutral Wright–Fisher diffusion killed at rate
`1 / x` (coalescence of the two copies), which he identifies with `∫₀^∞ C(x, y; t) dt` for the
transition density `C` of the killed diffusion (his Equation 4), with `y` the present-day frequency
and `x` the frequency backward in time. In terms of [`a₁`](patterson-aux1.md) and
[`a₂`](patterson-aux2.md) the two branches are `2 a₁(x) / y²`
([below the diagonal](killed-green-eq-aux-left.md)) and `2 a₁(y) a₂(x) / ((1 - y) y)`
([above it](killed-green-eq-aux-right.md)).

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
