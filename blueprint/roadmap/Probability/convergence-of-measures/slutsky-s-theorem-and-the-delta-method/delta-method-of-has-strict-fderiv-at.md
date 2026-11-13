# Delta method with a moving centre

Let `r n → ∞`, let the deterministic centres
`c n → θ`, and suppose `r n • (X n - c n)` converges in distribution to `Z`. If `g` is
*strictly* differentiable at `θ` with derivative `L`, then `r n • (g (X n) - g (c n))`
converges in distribution to `L Z`.

Strict differentiability (`HasStrictFDerivAt`) is the right hypothesis here: the increment
`g (X n) - g (c n)` is taken between two points that both move towards `θ`, and plain
differentiability at `θ` only controls increments based at `θ` itself. This is the form used
for the bootstrap, where `X n` is the bootstrap statistic and `c n` the observed one.
