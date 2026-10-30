/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerButterflyDoubleCover

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyDoubleCover`

* `bglue` evaluated on constant configurations.
* `rdc_reimer_wprob_of_doubleCover` instantiated with the empty left event, which has a butterfly
  double cover (`rdc_doubleCover_empty_left`), and the uniform weight on `Fin 2`.
* The universal hypothesis is refuted elsewhere (`rbi_doubleCoverAll_false`); no test assumes it.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyDoubleCover

/-- The uniform weight on `Fin 2`. -/
noncomputable def w2 : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

lemma w2_nonneg : ∀ i b, 0 ≤ w2 i b := fun _ _ => by norm_num [w2]

lemma w2_prob : ∀ i, w2 i false + w2 i true = 1 := fun _ => by norm_num [w2]

example : bglue (fun _ : Fin 2 => true) (fun _ => true) (fun _ => false) = fun _ => true := rfl

example (B : Set (ConfigSpace (Fin 2))) :
    wprob w2 (disjointOccurrence (∅ : Set (ConfigSpace (Fin 2))) B) ≤
      wprob w2 (∅ : Set (ConfigSpace (Fin 2))) * wprob w2 B :=
  rdc_reimer_wprob_of_doubleCover w2 w2_nonneg w2_prob (rdc_doubleCover_empty_left B)

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyDoubleCover
