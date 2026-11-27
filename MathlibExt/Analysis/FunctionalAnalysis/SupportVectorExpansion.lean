/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem

/-!
# The support vector expansion

The soft-margin support vector machine with a kernel `k` and an offset `b` minimizes, over
`f` in the RKHS `H` of `k` and `b ∈ ℝ`,

  `(1/λ) ∑ᵢ max(0, 1 - yᵢ (f(xᵢ) + b)) + ‖f‖²`

(Schölkopf, Herbrich and Smola, Example 2). By the representer theorem every minimizer has
`f = ∑ᵢ αᵢ k(·, xᵢ)`, the *SV expansion*; the offset plays the role of the extra function
`ψ₁ = 1` of their semiparametric representer theorem. This file derives the expansion from
`RepresenterTheorem.exists_eq_kernelExpansion_of_isMinimizer`: for a fixed offset the hinge
term is a loss of the values `f(xᵢ)` alone.

## Main results

* `svmRisk`: the soft-margin SVM objective with offset.
* `exists_eq_kernelExpansion_of_isMinimizer_svmRisk`: every minimizer `(f, b)` of `svmRisk`
  has `f` a kernel expansion at the training inputs.

## References

* B. Schölkopf, R. Herbrich and A. J. Smola, "A generalized representer theorem",
  *COLT 2001*, LNCS **2111** (2001), 416–426, Theorem 1, Theorem 2 and Example 2.
-/

@[expose] public section

open RKHS

namespace MathlibExt.Analysis.FunctionalAnalysis.SupportVectorExpansion

open MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem

variable {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [RKHS ℝ H X ℝ] {m : ℕ}

/-- **Soft-margin support vector machine objective with offset** (Schölkopf, Herbrich and
Smola, *A generalized representer theorem*, COLT 2001, Example 2, equation (28) with
`g(‖f‖) = ‖f‖²`). For inputs `xᵢ`, labels `yᵢ`, a parameter `λ`, a function `f` in the RKHS and
an offset `b`, it is `(1/λ) ∑ᵢ max(0, 1 - yᵢ (f(xᵢ) + b)) + ‖f‖²`. -/
noncomputable def svmRisk (x : Fin m → X) (y : Fin m → ℝ) (lam : ℝ) (f : H) (b : ℝ) : ℝ :=
  lam⁻¹ * ∑ i, max 0 (1 - y i * (f (x i) + b)) + ‖f‖ ^ 2

variable {H}

/-- **The support vector expansion** (Schölkopf, Herbrich and Smola, *A generalized
representer theorem*, COLT 2001, Theorem 1 and Example 2). If `(f, b)` minimizes the
soft-margin SVM objective `(1/λ) ∑ᵢ max(0, 1 - yᵢ (f(xᵢ) + b)) + ‖f‖²` over all functions `g`
of the RKHS and all offsets `c`, then `f = ∑ᵢ αᵢ k(·, xᵢ)` for some coefficients `αᵢ`. -/
theorem exists_eq_kernelExpansion_of_isMinimizer_svmRisk {x : Fin m → X} {y : Fin m → ℝ}
    {lam : ℝ} {f : H} {b : ℝ}
    (hf : ∀ (g : H) (c : ℝ), svmRisk H x y lam f b ≤ svmRisk H x y lam g c) :
    ∃ α : Fin m → ℝ, f = kernelExpansion H x α := by
  refine exists_eq_kernelExpansion_of_isMinimizer
    (L := fun v => lam⁻¹ * ∑ i, max 0 (1 - y i * (v i + b))) (Ω := fun t => t ^ 2)
    ?_ fun g => hf g b
  intro s hs t ht hst
  exact pow_lt_pow_left₀ hst hs two_ne_zero

end MathlibExt.Analysis.FunctionalAnalysis.SupportVectorExpansion
