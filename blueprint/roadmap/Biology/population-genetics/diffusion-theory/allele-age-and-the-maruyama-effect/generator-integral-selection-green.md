# Green's representation with selection

**Green's representation with selection** (Ewens 2004, Chapter 4; the integrated form of the
paper's `-δ(x - p) = s p (1 - p) ∂Ψ/∂p + p (1 - p) / (4N) ∂²Ψ/∂p²`). For continuous `g` and
`p ∈ (0, 1)`, `v(q) = ∫₀¹ Ψ(q, x) g(x) dx` solves `L_σ v = -g` at `p`; with
`integral_selectionGreen_left` and `integral_selectionGreen_right` (`v(0) = v(1) = 0`) this
generalizes `generator_integral_neutralGreen` to `σ ≠ 0`. In the diffusion reading (not
formalized here), `v(p)` is the expected value of `∫₀^T g(X_t) dt` up to absorption.
