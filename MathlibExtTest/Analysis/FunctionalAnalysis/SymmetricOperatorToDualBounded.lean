/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctional
import MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBounded
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Tests for `MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBounded` -/

set_option autoImplicit false

namespace MathlibExtTest.SymmetricOperatorToDualBounded

open MathlibExt.Analysis.FunctionalAnalysis.SymmetricOperatorToDualBoundedWanted
open MathlibExt.Analysis.FunctionalAnalysis.DiscontinuousLinearFunctional

-- Test section: the Hellinger–Toeplitz theorem. A symmetric linear operator `A` on a real
-- Hilbert space is bounded: `x ↦ ⟪A x, ·⟫` is a symmetric linear map into the dual, and
-- `‖⟪A x, ·⟫‖ = ‖A x‖`.
example {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ[ℝ] H) (hA : A.IsSymmetric) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : H, ‖A x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_of_symmetric_linearMap_to_strongDual
    ((innerSL ℝ : H →L[ℝ] StrongDual ℝ H).toLinearMap ∘ₗ A)
    (fun x y => by simp [innerSL_apply_apply, hA x y, real_inner_comm])
  exact ⟨C, hC, fun x => by simpa [innerSL_apply_norm] using hbound x⟩

-- Test section: the bilinear form `(x, y) ↦ (T x) y` of a symmetric linear map `T` into the
-- dual is bounded.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : E →ₗ[ℝ] StrongDual ℝ E) (hsym : ∀ x y : E, (T x) y = (T y) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E, |(T x) y| ≤ C * ‖x‖ * ‖y‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_of_symmetric_linearMap_to_strongDual T hsym
  refine ⟨C, hC, fun x y => ?_⟩
  calc |(T x) y| = ‖(T x) y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖T x‖ * ‖y‖ := (T x).le_opNorm y
    _ ≤ C * ‖x‖ * ‖y‖ := mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg y)

-- Test section: the symmetry hypothesis cannot be dropped. On an infinite-dimensional real
-- Banach space, take a discontinuous linear functional `f` and a functional `φ` of norm `1`;
-- the linear map `x ↦ f x • φ` into the dual is not bounded (so, by the theorem, not symmetric).
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hE : ¬ FiniteDimensional ℝ E) :
    ∃ T : E →ₗ[ℝ] StrongDual ℝ E, ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  obtain ⟨f, hf⟩ := exists_discontinuous_linearMap_of_not_finiteDimensional hE
  have : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hE inferInstance
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  obtain ⟨φ, hφ, -⟩ := exists_dual_vector ℝ x₀ (norm_ne_zero_iff.2 hx₀)
  refine ⟨f.smulRight φ, fun ⟨C, _, hbound⟩ => hf ?_⟩
  refine AddMonoidHomClass.continuous_of_bound f C fun x => ?_
  simpa [norm_smul, hφ] using hbound x

end MathlibExtTest.SymmetricOperatorToDualBounded
