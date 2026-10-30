/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerWeightInjection

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerWeightInjection`

* `rpw_pairDoubleCover_false`: the pair-witness butterfly fails for `rbi_A`, `rbi_B`.
* `rpw_reimer_wprob_of_weightInjection` instantiated with an empty disjoint occurrence
  (`rpw_weightInjection_of_box_empty`) and the uniform weight on `Fin 2`.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerWeightInjection

/-- The uniform weight on `Fin 2`. -/
noncomputable def w2 : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

lemma w2_nonneg : ∀ i b, 0 ≤ w2 i b := fun _ _ => by norm_num [w2]

lemma w2_prob : ∀ i, w2 i false + w2 i true = 1 := fun _ => by norm_num [w2]

example : ¬ rpw_PairDoubleCover rbi_A rbi_B := rpw_pairDoubleCover_false

example (B : Set (ConfigSpace (Fin 2))) :
    wprob w2 (disjointOccurrence (∅ : Set (ConfigSpace (Fin 2))) B) ≤
      wprob w2 (∅ : Set (ConfigSpace (Fin 2))) * wprob w2 B := by
  apply rpw_reimer_wprob_of_weightInjection w2 w2_nonneg w2_prob
  apply rpw_weightInjection_of_box_empty
  ext ω
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun h => (disjointOccurrence_subset_inter _ _ h).1

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerWeightInjection
