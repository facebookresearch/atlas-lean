# Patterson's first appendix solution a₁

For a real number `x`, let

`a₁(x) = 2 - x + 2 (1 - x) log(1 - x) / x`,

with the conventions `u / 0 = 0`, `log u = log |u|` and `log 0 = 0`. Thus `a₁(0) = 2`, whereas
`a₁(x) → 0` as `x → 0⁺` ([limit at 0](tendsto-patterson-aux1-nhds-gt-zero.md)); `a₁(1) = 1`, which
is also the limit from below; and for `x > 1` the logarithm is `log(x - 1)`. The intended domain is
`0 < x ≤ 1`. There `a₁` is Patterson's first solution (his Equation A3) of
`x² (1 - x) w''(x) / 2 = w(x)` (his Equation A2), which it
[solves on `(0, 1)`](patterson-aux1-ode.md).

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
