# Sound intensity level in decibels against a reference intensity

For real `I_ref` and `I`, the sound intensity level of `I` against the reference intensity
`I_ref` is `L = 10 log₁₀ (I / I_ref)` decibels, with `log₁₀` the base-10 logarithm; the reference
is an argument, not a fixed value. Levels are meant for positive `I` and `I_ref` in the same unit.
With the conventions `x / 0 = 0`, `log 0 = 0` and `log x = log |x|`, the value is `0` when `I = 0`
or `I_ref = 0`, and `10 log₁₀ |I / I_ref|` when the ratio is negative.
