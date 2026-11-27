# The χ²₁ tail at 10 is at most 0.05

With the [`χ²₁` tail](chi-sq-one-tail.md) read as a real number,

`P(χ²₁ > 10) ≤ 0.05`,

since the [Chernoff bound](chi-sq-one-tail-to-real-le.md) at `x = 10` is `2 e^{-5} ≤ 0.05`. So a
statistic of `10` has `χ²₁` p-value at most `0.05`, and the level-`0.05` `χ²₁` test rejects it.
