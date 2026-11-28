# A theta series majorant

Let `τ` be a complex `g × g` matrix whose imaginary part
`Y = Im(τ)` is positive definite, let `z ∈ ℂ^g`, `y = Im(z)`, and let `b ∈ ℝ^g` with `Y b = y`
(that is, `b = Y⁻¹ y`). Then
`exp(-π ᵗy Y⁻¹ y) |ϑ(z; τ)| ≤ ∑_{n ∈ ℤ^g} exp(-π ᵗ(n + b) Y (n + b))`,
and the series on the right converges (`Javanpeykar.summable_exp_neg_pi_quadForm`).
The source takes `τ` symmetric; that is not needed here.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), proof of Lemma 2.4.2, p. 100, the inequality after equation (6) (where the
exponent on the left is printed as `-π ᵗg (Im(τ))⁻¹ y`, with `ᵗg` standing for `ᵗy`), with `ϑ` as
in §2.1, p. 94.
