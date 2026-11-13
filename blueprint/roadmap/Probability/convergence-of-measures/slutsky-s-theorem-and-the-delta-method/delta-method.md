# The delta method

Let `r n → ∞` and suppose `r n • (X n - θ)` converges in distribution
to `Z`. If `g` has Fréchet derivative `L` at `θ`, then `r n • (g (X n) - g θ)` converges in
distribution to `L Z`.

This is the first-order statement only. When `L = 0` the limit is the constant `0`, and no
second-order limit law is asserted.

The measurability hypotheses `hX` and `hgX` are needed because `g` is only assumed
differentiable at `θ` and `X n` cannot be recovered from `r n • (X n - θ)` when `r n = 0`;
both hold automatically for measurable `X n` and continuous `g`.
