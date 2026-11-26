/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.SupportVectorExpansion

@[expose] public section

/-!
# Tests for the support vector expansion
-/

set_option autoImplicit false

open MathlibExt.Analysis.FunctionalAnalysis.RepresenterTheorem
open MathlibExt.Analysis.FunctionalAnalysis.SupportVectorExpansion

namespace MathlibExtTest.Analysis.FunctionalAnalysis.SupportVectorExpansion

/-- A concrete RKHS: the rank-one kernel `k(a, b) = f a * f b` on two points. -/
abbrev H₁ (f : Fin 2 → ℝ) := RKHS.OfKernel (RKHS.outerKernel ℝ f)

/-- The support vector expansion on a concrete RKHS. -/
example (f : Fin 2 → ℝ) (x : Fin 2 → Fin 2) (y : Fin 2 → ℝ) (g : H₁ f) (b : ℝ)
    (hg : ∀ (h : H₁ f) (c : ℝ), svmRisk (H₁ f) x y 1 g b ≤ svmRisk (H₁ f) x y 1 h c) :
    ∃ α : Fin 2 → ℝ, g = kernelExpansion (H₁ f) x α :=
  exists_eq_kernelExpansion_of_isMinimizer_svmRisk hg

/-- Non-vacuity of the minimizer hypothesis: with no training data the objective is `‖f‖²`,
minimized by `f = 0` with any offset. -/
example (f : Fin 2 → ℝ) (y : Fin 0 → ℝ) (b : ℝ) :
    ∀ (h : H₁ f) (c : ℝ), svmRisk (H₁ f) (fun i : Fin 0 => i.elim0) y 1 0 b ≤
      svmRisk (H₁ f) (fun i : Fin 0 => i.elim0) y 1 h c := by
  intro h c
  simp only [svmRisk, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, zero_add, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  positivity

end MathlibExtTest.Analysis.FunctionalAnalysis.SupportVectorExpansion
