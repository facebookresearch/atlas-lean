# C² polynomial approximation on a compact set

Let `K ⊆ U ⊆ ℝⁿ` with `K` compact and `U` open, and let `f` be `C²` on `U`. For every `ε > 0`
there is a real polynomial `p` in `n` variables such that at every point `x ∈ K`,
`|p(x) - f(x)| ≤ ε`, `|∂ᵢ p(x) - ∂ᵢ f(x)| ≤ ε` for every `i`, and
`|∂ᵢ ∂ⱼ p(x) - ∂ᵢ ∂ⱼ f(x)| ≤ ε` for all `i, j`. So
`f` is approximated uniformly on `K` by a polynomial together with all its first and second
partial derivatives. On the polynomial side these are the formal partial derivatives, which
[agree with the analytic ones](has-fderiv-at-mv-polynomial-eval.md).
