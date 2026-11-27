# Clock configuration after the next jump

For a [two-channel chain](two-channel.md), a state `x` and a
[clock configuration](clock-config.md) `c = ((r₁, r₂), (u₁, u₂))`, write `a = rate₁ x`,
`b = rate₂ x`, and `h` for the [holding time](hold.md) from `x` with residuals
`(r₁, r₂)`, defined with the convention `t / 0 = 0`. The clock configuration after the next jump
is `c` itself if `a + b = 0`. Otherwise it is

- `((u₁ 0, r₂ - b h), (tail u₁, u₂))` if `b r₁ < a r₂` (channel `1` fires; here `h = r₁ / a`);
- `((r₁ - a h, u₂ 0), (u₁, tail u₂))` if `a r₂ < b r₁` (channel `2` fires; here `h = r₂ / b`);
- `((u₁ 0, u₂ 0), (tail u₁, tail u₂))` if `a r₂ = b r₁` (both fire),

where the [tail](seq-tail.md) of a sequence drops its first term. So a channel that fires takes
its next interarrival time as its new residual, and the residual of a channel that does not fire
decreases by the internal time `b h` or `a h` it has consumed.
