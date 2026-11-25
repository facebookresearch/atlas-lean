# One jump of a two-channel chain with its clocks

For a [two-channel chain](two-channel.md), the step map sends a state `x` and a
[clock configuration](clock-config.md) `c = ((r₁, r₂), (u₁, u₂))` to the pair formed by the
[next state](next.md) from `x` with residuals `(r₁, r₂)` and the
[clock configuration after the next jump](next-clock.md) from `x` and `c`. When
`rate₁ x + rate₂ x = 0` it leaves `(x, c)` unchanged.
