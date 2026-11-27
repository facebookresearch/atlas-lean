/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Regression.LeastSquaresMinimizers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Regressions for the least-squares minimizer set -/

set_option autoImplicit false

namespace Cslib.MachineLearning.LeastSquares.Tests

open Matrix

private noncomputable def design : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]
private noncomputable def response : Fin 2 → ℝ := ![3, 5]
private noncomputable def first : Fin 2 → ℝ := ![3, 0]
private noncomputable def second : Fin 2 → ℝ := ![0, 3]

private theorem first_normal : designᵀ *ᵥ (design *ᵥ first) = designᵀ *ᵥ response := by
  funext i
  fin_cases i <;> norm_num [design, first, response, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem first_fit : design *ᵥ first = ![3, 0] := by
  funext i
  fin_cases i <;> norm_num [design, first, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem second_fit : design *ᵥ second = ![3, 0] := by
  funext i
  fin_cases i <;> norm_num [design, second, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- Distinct minimizers for a rank-deficient design give the same projection, which is not `y`.
example : first ≠ second ∧ first ∈ rssMinimizers design response ∧
    second ∈ rssMinimizers design response ∧
    (LinearMap.range design.toEuclideanLin).starProjection (WithLp.toLp 2 response) =
      WithLp.toLp 2 (![3, 0] : Fin 2 → ℝ) := by
  have hfirst := (mem_rssMinimizers_iff_fit_eq first_normal first).mpr rfl
  have hsecond : second ∈ rssMinimizers design response := by
    rw [rssMinimizers_eq_translate_ker first_normal]
    refine ⟨second - first, ?_, ?_⟩
    · change design *ᵥ (second - first) = 0
      rw [mulVec_sub, first_fit, second_fit, sub_self]
    · change first + (second - first) = second
      rw [add_sub_cancel]
  refine ⟨?_, hfirst, hsecond, ?_⟩
  · intro he
    have h := congrFun he (0 : Fin 2)
    norm_num [first, second] at h
  · rw [← fit_eq_starProjection_of_mem_rssMinimizers hsecond, second_fit]

-- An identity design gives a singleton at the observed response.
example : rssMinimizers (1 : Matrix (Fin 2) (Fin 2) ℝ) response = {response} := by
  rw [rssMinimizers_eq_singleton_of_injective]
  · simp
  · intro a b h
    simpa only [one_mulVec] using h

-- With no rows all predictions coincide, and every coefficient vector minimizes.
example (X : Matrix (Fin 0) (Fin 2) ℝ) (y : Fin 0 → ℝ) :
    rssMinimizers X y = Set.univ := by
  obtain ⟨θ₀, h₀⟩ := exists_normal X y
  ext θ
  exact ⟨fun _ => Set.mem_univ _, fun _ =>
    (mem_rssMinimizers_iff_fit_eq h₀ θ).mpr (Subsingleton.elim _ _)⟩

-- With no columns the coefficient space is a singleton, even for a nonzero response.
example (X : Matrix (Fin 2) (Fin 0) ℝ) : ∃! θ, θ ∈ rssMinimizers X response :=
  (existsUnique_rssMinimizer_iff_injective X response).mpr (fun _ _ _ => Subsingleton.elim _ _)

end Cslib.MachineLearning.LeastSquares.Tests
