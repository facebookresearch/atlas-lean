# State after the next jump of a two-channel chain

For a [two-channel chain](two-channel.md), a state `x` and residual clocks `r = (r₁, r₂)`, any real
numbers, write `a = rate₁ x` and `b = rate₂ x`. The next state is `x` itself if `a + b = 0`.
Otherwise it is

- `target₁ x` if `b r₁ < a r₂` (channel `1` rings first);
- `target₂ x` if `a r₂ < b r₁` (channel `2` rings first);
- `target₁₂ x` if `a r₂ = b r₁` (both ring at the same instant).

For a [valid](is-valid.md) chain, `a + b = 0` means that neither channel is active; for arbitrary
real rates it also holds when `b = -a ≠ 0`.
