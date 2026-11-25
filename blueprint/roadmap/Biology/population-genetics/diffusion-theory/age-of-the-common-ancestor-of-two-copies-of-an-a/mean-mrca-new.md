# Patterson's MRCA-age function M₁ for a new allele

For a real number `y`, let

`M₁(y) = -4 + 2 log y + (2π² - 12 dilog(y)) / (3y) + 2 log y / (1 - y)`,

where [`dilog`](patterson-dilog.md) is Patterson's dilogarithm, with the conventions `u / 0 = 0`,
`log u = log |u|` and `log 0 = 0`. Thus `M₁(0) = -4` and `M₁(1) = 2π²/3 - 4`, which is `2` more than
the limit `2 (π² - 9) / 3` of `M₁(y)` as `y → 1⁻` ([limit](tendsto-mean-mrca-new-one.md)). The
intended domain is `0 < y < 1`. There `M₁` is Patterson's Equation 16 (his Theorem 6(2)): in his
diffusion model, the expected age, in units of `2N` generations, of the most recent common ancestor
of two copies of an allele known to be new (nonancestral) and now at frequency `y`. On `(0, 1)` it
[equals `y ∫₀¹ G_C(x, y) / x dx`](mean-mrca-new-eq-integral.md).

## Sources

- N. J. Patterson, *How old is the most recent ancestor of two copies of an allele?*, Genetics 169
  (2005), 1093–1104.
