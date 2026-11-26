# Slutsky equation: substitution effect equals price plus income effect

For finitely many goods, a utility `u`, a consumption set `X` and a target utility `ū`, let
`e(p) = inf {p · y | y ∈ X, u(y) ≥ ū}` be the expenditure function, and let `x(p, w)` (Marshallian
demand) and `h(p)` (compensated demand) be functions, linked only as follows. Suppose that

- for every price vector `p` near `p₀`, the costs `{p · y | y ∈ X, u(y) ≥ ū}` are bounded below;
- `h(p₀)` is a Hicksian demand at `p₀`: it lies in `X`, reaches `ū`, and costs at most every bundle
  of `X` reaching `ū`;
- the duality `h(p) = x(p, e(p))` holds for `p` near `p₀`;
- `e` is differentiable at `p₀`, `(p, w) ↦ x(p, w)` has derivative `Dx` at `(p₀, w₀)` with
  `w₀ = e(p₀)`, and `h` has derivative `Dh` at `p₀`.

Then for all goods `i, j`, `(Dh eⱼ) i = (Dx (eⱼ, 0)) i + (Dx (0, 1)) i · x(p₀, w₀) j`, where `eⱼ` is
the `j`-th unit price vector: the substitution effect `∂hᵢ/∂pⱼ` equals the price effect `∂xᵢ/∂pⱼ`
plus the income effect `∂xᵢ/∂w · xⱼ`, all at `(p₀, w₀)`.
