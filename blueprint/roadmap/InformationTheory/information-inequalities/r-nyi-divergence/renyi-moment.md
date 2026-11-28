# Rényi moment

**Rényi moment** of order `α` of `μ` with respect to `ν`: `∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν`
when `μ ≪ ν` and `1 < α`, and `∞` otherwise. For absolutely continuous probability laws this
is the moment in Mironov, arXiv:1702.07476v3, Definition 3. For arbitrary measures the formula
uses Mathlib's total `rnDeriv`, which is zero without a Lebesgue decomposition. The value `∞`
at `α ≤ 1` is a convention of this formula, not part of the cited definition.
