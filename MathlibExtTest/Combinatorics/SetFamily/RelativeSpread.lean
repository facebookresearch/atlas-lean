/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.RelativeSpread
import Mathlib.Tactic.NormNum

/-!
# Tests for relative spread

On the two-point ground set, the two singleton edges with one occurrence each meet the
`κ = 2` bound, whereas duplicating just one edge changes its upper-event probability from
`1/2` to `2/3`. This biased law is still spread at the nonintegral parameter `3/2`.
A second example detects a violation that only appears on testing a pair of vertices.
-/

open MeasureTheory SetFamily

private def two : Set.Ioi (1 : ℝ) := ⟨2, by norm_num⟩
private def balanced : Multiset (Finset Bool) := {false} ::ₘ {true} ::ₘ 0
private def biased : Multiset (Finset Bool) := {false} ::ₘ balanced

private theorem four_subsets : ∀ S : Finset Bool,
    S = ∅ ∨ S = {false} ∨ S = {true} ∨ S = {false, true} := by decide

private theorem balanced_spread : IsRelSpread balanced two := by
  intro S
  rcases four_subsets S with rfl | rfl | rfl | rfl <;>
    norm_num [balanced, two, -Multiset.cons_zero, Multiset.countP_cons, Finset.subset_iff]

private theorem biased_not_spread : ¬ IsRelSpread biased two := by
  intro h
  have bad := h {false}
  norm_num [biased, balanced, two, -Multiset.cons_zero, Multiset.countP_cons, Finset.subset_iff] at bad

/-- The two families differ only in multiplicity. -/
example : balanced.toFinset = biased.toFinset := by decide

/-- Each singleton has probability exactly `1/2` under the balanced law. -/
example (b : Bool) : (uniformOccurrenceMeasure balanced (by decide) {T | ({b} : Finset Bool) ⊆ T} :
    ℝ) = 1 / 2 := by
  rw [uniformOccurrenceMeasure_superset]
  cases b <;> norm_num [balanced, -Multiset.cons_zero, Multiset.countP_cons, Finset.subset_iff]

/-- Sampling from the balanced family satisfies every upper-event bound at `κ = 2`. -/
example : IsRelSpreadMeasure (uniformOccurrenceMeasure balanced (by decide)) two :=
  (isRelSpread_iff_uniformOccurrenceMeasure _ _ _).mp balanced_spread

/-- Sampling from the biased family breaks the upper-event bound at `κ = 2`. -/
example : ¬ IsRelSpreadMeasure (uniformOccurrenceMeasure biased (by decide)) two :=
  fun h => biased_not_spread ((isRelSpread_iff_uniformOccurrenceMeasure _ _ _).mpr h)

/-- The duplicated edge has upper-event probability `2/3`, rather than `1/2`. -/
example : (uniformOccurrenceMeasure biased (by decide) {T | ({false} : Finset Bool) ⊆ T} : ℝ) =
    2 / 3 := by
  rw [uniformOccurrenceMeasure_superset]
  norm_num [biased, balanced, -Multiset.cons_zero, Multiset.countP_cons, Finset.subset_iff]

/-- The same biased family attains the weaker singleton bound at `κ = 3/2`. -/
example : IsRelSpread biased ⟨3 / 2, by norm_num⟩ := by
  intro S
  rcases four_subsets S with rfl | rfl | rfl | rfl <;>
    norm_num [biased, balanced, -Multiset.cons_zero, Multiset.countP_cons, Finset.subset_iff]

/-- With one full and one empty edge, both singleton events have mass `1/2`, but the
upper event of the whole pair also has mass `1/2`, greater than `(1/2)^2`. -/
example : ¬ IsRelSpread (({false, true} : Finset Bool) ::ₘ ∅ ::ₘ 0) two := by
  intro h
  have bad := h {false, true}
  norm_num [two, -Multiset.cons_zero, Multiset.countP_cons, Finset.subset_iff] at bad

/-- The empty test set gives the whole event for every empirical law. -/
example {α : Type*} (F : Multiset (Finset α)) (hF : F ≠ 0) :
    uniformOccurrenceMeasure F hF {T | (∅ : Finset α) ⊆ T} = 1 := by simp

/-- No occurrences satisfy any test in the empty family, so its count bound holds. -/
example {α : Type*} (κ : Set.Ioi (1 : ℝ)) : IsRelSpread (0 : Multiset (Finset α)) κ := by
  intro S
  simp

/-- A single empty edge is spread: only the empty test set has positive mass. -/
example {α : Type*} (κ : Set.Ioi (1 : ℝ)) : IsRelSpread ({∅} : Multiset (Finset α)) κ := by
  classical
  intro S
  by_cases h : S = ∅
  · simp [h]
  · have hk : 0 ≤ κ.val := le_of_lt (lt_trans zero_lt_one κ.2)
    simpa [Multiset.countP_eq_card_filter, Multiset.filter_singleton, h] using
      inv_nonneg.mpr (pow_nonneg hk S.card)

/-- The unnormalised zero multiset has zero mass, not a uniform probability draw. -/
example {α : Type*} : ¬ IsProbabilityMeasure (Measure.ofMultiset (0 : Multiset (Finset α))) := by
  intro h
  simpa [Measure.ofMultiset] using h.measure_univ

/-- The strict endpoint is excluded from the parameter domain. -/
example : ¬ ∃ κ : Set.Ioi (1 : ℝ), κ.val = 1 := by
  rintro ⟨⟨k, hk⟩, rfl⟩
  exact lt_irrefl _ hk
