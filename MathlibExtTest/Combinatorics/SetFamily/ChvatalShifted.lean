/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Powerset
import MathlibExt.Combinatorics.SetFamily.ChvatalShifted

/-! # Tests for Chvátal's theorem for shifted down-sets -/

namespace MathlibExt.Combinatorics.ChvatalShifted

/-- The subsets of `{0, 1, 2}` with at most two elements: a shifted down-set. -/
private def smallFamily : Finset (Finset ℕ) := (Finset.range 3).powerset.filter (·.card ≤ 2)

private lemma isLowerSet_smallFamily : IsLowerSet (smallFamily : Set (Finset ℕ)) := by
  intro A B hBA hA
  simp only [smallFamily, Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hA ⊢
  exact ⟨Finset.Subset.trans hBA hA.1, (Finset.card_le_card hBA).trans hA.2⟩

private lemma shift_smallFamily :
    ∀ A ∈ smallFamily, ∀ j ∈ A, ∀ i < j, i ∉ A → insert i (A.erase j) ∈ smallFamily := by
  decide

-- Chvátal's bound in `smallFamily`: the star of `0` has three members, so every intersecting
-- subfamily has at most three members.
example (𝓐 : Finset (Finset ℕ)) (h𝓐 : 𝓐 ⊆ smallFamily)
    (hint : (𝓐 : Set (Finset ℕ)).Intersecting) : 𝓐.card ≤ 3 := by
  have hbound := card_le_card_star_zero_of_isLowerSet_of_shifted
    isLowerSet_smallFamily shift_smallFamily h𝓐 hint
  rwa [show (smallFamily.filter (0 ∈ ·)).card = 3 by decide] at hbound

-- The bound is also attained by the triangle `{{0, 1}, {0, 2}, {1, 2}}`, which is not a star.
example : (({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)) : Set (Finset ℕ)).Intersecting ∧
    ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)) ⊆ smallFamily ∧
    ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)).card = 3 := by
  refine ⟨?_, by decide, by decide⟩
  simp only [Set.Intersecting, Finset.mem_coe]
  decide

end MathlibExt.Combinatorics.ChvatalShifted
