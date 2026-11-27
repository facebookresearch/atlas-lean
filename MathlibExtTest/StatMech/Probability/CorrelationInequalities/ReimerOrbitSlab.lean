/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerOrbitSlab

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerOrbitSlab`

* `poc_flip` on small inputs.
* `poc_reimerCardForm_rbi`: the counting form of Reimer's theorem for `rbi_A`, `rbi_B`.
* `poc_witnessInjection_rbi_false`: the witness swap selector is not injective for them.
* `reimer_wprob_of_slabCard` instantiated with `poc_slabCard_rbi`.
-/

@[expose] public section

open StatMech Finset

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerOrbitSlab

/-- The uniform weight on `Fin 2`. -/
noncomputable def w2 : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

lemma w2_nonneg : ∀ i b, 0 ≤ w2 i b := fun _ _ => by norm_num [w2]

lemma w2_prob : ∀ i, w2 i false + w2 i true = 1 := fun _ => by norm_num [w2]

example : poc_flip (fun _ : Fin 2 => true) (fun _ => false) = fun _ => true := by
  funext a; simp [poc_flip]

example : poc_ReimerCardForm rbi_A rbi_B := poc_reimerCardForm_rbi

example : ¬ poc_WitnessInjection rbi_A rbi_B := poc_witnessInjection_rbi_false

example : wprob w2 (disjointOccurrence rbi_A rbi_B) ≤ wprob w2 rbi_A * wprob w2 rbi_B :=
  reimer_wprob_of_slabCard w2 w2_nonneg w2_prob poc_slabCard_rbi

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerOrbitSlab
