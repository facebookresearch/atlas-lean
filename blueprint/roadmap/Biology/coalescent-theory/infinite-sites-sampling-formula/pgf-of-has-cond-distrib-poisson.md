# Generating function of a conditionally Poisson count

Let `μ` be a probability measure on `Ω`, let `X` be a function from `Ω` to a measurable space `𝓧`,
let `ρ` be a measurable function from `𝓧` to `[0, ∞)`, and let `N` be a natural-number-valued
function on `Ω` whose conditional law given `X` is Poisson with mean `ρ(X)`: the pair `(X, N)` is
`μ`-almost everywhere measurable, and the image of `μ` under `(X, N)` is the composition product of
the image of `μ` under `X` with the kernel `x ↦ Po(ρ(x))`. Then for every real `s` with `|s| ≤ 1`,
with natural powers and `0^0 = 1` (so that at `s = 0` the left side is `P(N = 0)`),

`E[s^N] = E[exp(-ρ(X) (1 - s))]`.
