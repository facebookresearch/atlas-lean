/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1
import Mathlib.Tactic.Linarith

/-! # Tests for the negative answer to Scottish Book Problem 15.1 -/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook15Point1

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted

-- Recover a single space and sphere satisfying all the counterexample properties.
example : ∃ (E : Type) (_ : TopologicalSpace E) (_ : AddCommGroup E) (_ : Module ℝ E),
    IsTypeF E ∧ ∃ K : Set E, IsSphere E K ∧ IsBoundedSet E K ∧ ¬ AdmitsBanachNorm E := by
  classical
  by_contra h
  apply boundedSphereFImpliesB_refuted
  intro E t g m hF ⟨K, hK, hB⟩
  by_contra hN
  exact h ⟨E, t, g, m, hF, K, hK, hB, hN⟩

-- The usual distance on ℝ satisfies the completeness condition in the two definitions.
private lemma real_complete (x : ℕ → ℝ)
    (hx : ∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (x m) (x n) < ε) :
    ∃ y, ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) y < ε := by
  have hc : CauchySeq x := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := hx ε hε
    exact ⟨N, fun m hm n hn => hN m n hm hn⟩
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨y, Metric.tendsto_atTop.1 hy⟩

example : IsTypeF ℝ :=
  ⟨dist, fun _ _ => dist_nonneg, fun _ _ => dist_eq_zero, dist_comm, dist_triangle,
    fun _ _ _ => by simp [Real.dist_eq], fun _ => Metric.isOpen_iff, real_complete,
    continuous_add, continuous_smul⟩

example : AdmitsBanachNorm ℝ :=
  ⟨abs, abs_nonneg, fun _ => abs_eq_zero, abs_add_le, abs_mul, fun _ => Metric.isOpen_iff,
    real_complete⟩

-- Both real rays have a unique positive rescaling to absolute value one.
example : IsSphere ℝ {1, -1} := by
  refine ⟨by norm_num, fun x hx => ?_⟩
  have hmem (t : ℝ) (ht : 0 < t) : t • x ∈ ({1, -1} : Set ℝ) ↔ t * |x| = 1 := by
    rw [← abs_of_pos ht, ← abs_mul, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    simp [abs_of_pos ht]
  refine ⟨|x|⁻¹, ⟨inv_pos.mpr (abs_pos.mpr hx), (hmem _ (by positivity)).2 ?_⟩, ?_⟩
  · exact inv_mul_cancel₀ (abs_ne_zero.mpr hx)
  · rintro t ⟨ht, htx⟩
    exact eq_inv_of_mul_eq_one_left ((hmem t ht).1 htx)

-- A set meeting just the positive half of the real line misses the opposite ray.
example : ¬ IsSphere ℝ {1} := by
  intro h
  obtain ⟨t, ⟨ht, hmem⟩, _⟩ := h.2 (-1) (by norm_num)
  change t * (-1) = 1 at hmem
  linarith

end MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook15Point1
