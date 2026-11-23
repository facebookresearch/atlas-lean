# Exponential moment of the score sum

For real weights `q` and scores `f` on a finite alphabet, every real `θ` and every natural number
`n`, the [weighted average](score-expect.md) of `e^{θ Sₙ}`, where `Sₙ` is the sum of the `n` scores,
is the `n`-th power of the [moment generating function](score-mgf.md):
`E[e^{θ Sₙ}] = (∑_b q_b e^{θ f(b)})ⁿ`. At a root `θ` of `∑_b q_b e^{θ f(b)} = 1` it is `1` for every
`n`; for a probability vector `q` this is the constant mean of the exponential martingale
`e^{θ Sₙ}`.
