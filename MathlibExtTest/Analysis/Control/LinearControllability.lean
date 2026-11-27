/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Control.LinearControllability

@[expose] public section

open MathlibExt.Analysis.Control

namespace MathlibExtTest.Analysis.Control.LinearControllability

/-- Fully actuated systems (`B = id`) are controllable on every `[0, T]`, `T > 0`: the Kalman
subspace contains `B u = u` for every `u`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] (A : E →L[ℝ] E) {T : ℝ} (hT : 0 < T) :
    IsControllableOn A (ContinuousLinearMap.id ℝ E) T := by
  rw [isControllableOn_iff_kalman A _ hT, eq_top_iff]
  intro x _
  exact Submodule.subset_span ⟨0, Module.finrank_pos, x, by simp⟩

/-- With zero input matrix a nontrivial system is not controllable (the Kalman subspace is
`⊥`), so the hypotheses `T > 0` and controllability are not jointly vacuous only when `B ≠ 0`. -/
example {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (A : E →L[ℝ] E) {T : ℝ} (hT : 0 < T) : ¬ IsControllableOn A (0 : U →L[ℝ] E) T := by
  rw [isControllableOn_iff_kalman A _ hT, kalmanSubspace_eq_top_iff]
  intro h
  obtain ⟨η, hη⟩ := exists_ne (0 : E)
  exact hη (h η fun k v => by simp)

/-- At `T = 0` nothing nontrivial is controllable: the endpoint equals the starting point. The
hypothesis `0 < T` of the criteria is therefore needed. -/
example {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) : ¬ IsControllableOn A B 0 := by
  intro h
  obtain ⟨η, hη⟩ := exists_ne (0 : E)
  obtain ⟨u, -, x, hx0, -, hxT⟩ := h 0 η
  exact hη (hxT.symm.trans hx0)

/-- The Gramian quadratic form is nonnegative for `T ≥ 0`. -/
example {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) {T : ℝ} (hT : 0 ≤ T) (η : E) :
    0 ≤ @inner ℝ _ _ η (gramian A B T η) := by
  rw [inner_gramian_apply]
  exact intervalIntegral.integral_nonneg hT fun s _ => sq_nonneg _

end MathlibExtTest.Analysis.Control.LinearControllability
