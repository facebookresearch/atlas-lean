/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthQSupportPhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! A finite original quotient-and-central injection bounds the actual full-axis extraspecial
  stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual original extraspecial intersection of the full-axis local stabilizer. -/
def generatedTwelfthAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedTwelfthAxis).comap inclQ

/-- Original free quotient bits and the central sign retain each actual full-axis Q fixer. -/
def generatedTwelfthQSupportFixerCoordinates (q : generatedTwelfthAxisQStabilizer) :
    (Fin 1 → ZMod 2) × ZMod 2 :=
  (generatedTwelfthQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.val.base,
    Multiplicative.toAdd q.val.coeff)

/-- The entire original full-axis extraspecial stabilizer embeds in its literal remaining bits. -/
theorem generatedTwelfth_Q_support_fixer_coordinates_injective :
    Function.Injective generatedTwelfthQSupportFixerCoordinates := by
  intro q r h
  have hq : rhoLocal (inclQ q.val) generatedTwelfthAxis = generatedTwelfthAxis := q.property
  have hr : rhoLocal (inclQ r.val) generatedTwelfthAxis = generatedTwelfthAxis := r.property
  have hb := congrArg (fun w : Fin 1 → ZMod 2 =>
      generatedTwelfthQSupportFreeProjection *ᵥ w) (congrArg Prod.fst h)
  change generatedTwelfthQSupportFreeProjection *ᵥ
      (generatedTwelfthQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.val.base) =
    generatedTwelfthQSupportFreeProjection *ᵥ
      (generatedTwelfthQSupportFreeMatrix *ᵥ Multiplicative.toAdd r.val.base) at hb
  rw [generatedTwelfth_Q_support_free_quotient q.val hq,
    generatedTwelfth_Q_support_free_quotient r.val hr] at hb
  apply Subtype.ext
  apply NormalizedCocycleExtension.Extension.ext
  · exact Multiplicative.toAdd.injective hb
  · exact Multiplicative.toAdd.injective (congrArg Prod.snd h)

/-- Every genuine original full-axis Q fixer is bounded by the remaining free and central bits. -/
theorem generatedTwelfth_axis_Q_stabilizer_upper :
    Nat.card generatedTwelfthAxisQStabilizer ≤ 4 := by
  have h := Nat.card_le_card_of_injective generatedTwelfthQSupportFixerCoordinates
    generatedTwelfth_Q_support_fixer_coordinates_injective
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
