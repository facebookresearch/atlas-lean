# Holding time read off the residual clocks of a two-channel chain

For a [two-channel chain](two-channel.md), a state `x` and residual clocks `r = (r₁, r₂)`, any real
numbers, write `a = rate₁ x` and `b = rate₂ x`. The holding time is

- `r₁ / a` if `b r₁ < a r₂` (channel `1` rings first);
- `r₂ / b` if `a r₂ < b r₁` (channel `2` rings first);
- `r₁ / a` if `a r₂ = b r₁` (a tie),

with the convention `t / 0 = 0`; in particular it is `0` at a state where `a = b = 0`. For
nonnegative rates that are not both `0` and positive residuals, it is the earliest ring time
`r₁ / a` or `r₂ / b` among the channels with a positive rate.
