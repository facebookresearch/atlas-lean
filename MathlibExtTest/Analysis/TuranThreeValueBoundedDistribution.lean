/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.TuranThreeValueBoundedDistribution

open MathlibExt.Analysis.TuranThreeValueBoundedDistributionWanted

-- A counterexample remains after forgetting the three distinguished values.
example : ∃ f : ℂ → ℂ, MeromorphicOn f Set.univ ∧ ¬ IsBoundedValueDistribution f := by
  by_contra! h
  apply conjecture_refuted
  intro f hf _ _
  exact h f hf

-- The negative answer persists when the three distinguished values must be the finite
-- values `0`, `1`, `2`.
example : ¬ ∀ f : ℂ → ℂ, MeromorphicOn f Set.univ →
    (∀ w : ℂ, ∃ z : ℂ, meromorphicOrderAt (fun t => f t - w) z ≠ ⊤) →
    (∀ r : ℝ, r > 0 → ∃ C : ℕ, ∀ (c w : ℂ), w ∈ ({0, 1, 2} : Set ℂ) →
      ∀ s : Finset ℂ, ↑s ⊆ Metric.ball c r → ∑ z ∈ s, rootMultSph f (some w) z ≤ (C : ℕ∞)) →
    IsBoundedValueDistribution f := by
  intro h
  obtain ⟨f, hf, hnc, hb, hnot⟩ := exists_bounded_each_value_not_isBoundedValueDistribution
  refine hnot (h f hf hnc fun r hr => ?_)
  obtain ⟨A, hA⟩ := hb (some 0) r hr
  obtain ⟨B, hB⟩ := hb (some 1) r hr
  obtain ⟨D, hD⟩ := hb (some 2) r hr
  refine ⟨A + B + D, fun c w hw s hs => ?_⟩
  rcases hw with rfl | rfl | hw
  · exact (hA c s hs).trans (by norm_cast; omega)
  · exact (hB c s hs).trans (by norm_cast; omega)
  · obtain rfl : w = 2 := hw
    exact (hD c s hs).trans (by norm_cast; omega)

-- An identically attained finite value has infinite multiplicity.
example (w z : ℂ) : rootMultSph (fun _ => w) (some w) z = ⊤ := by
  simp [rootMultSph, rootMult, meromorphicOrderAt_const]

-- At the pole of the reciprocal, the germ contributes only to the fibre at infinity.
example : rootMultSph (fun z : ℂ => z⁻¹) none 0 = 1 ∧
    rootMultSph (fun z : ℂ => z⁻¹) (some 0) 0 = 0 := by
  have ho : meromorphicOrderAt (fun z : ℂ => z⁻¹) 0 = -1 := by
    change meromorphicOrderAt ((id : ℂ → ℂ)⁻¹) 0 = -1
    simp [meromorphicOrderAt_inv]
  have hneg : WithTop.untopD (0 : ℤ) (-1) = -1 := rfl
  simp [rootMultSph, rootMult, poleMult, ho, hneg]
