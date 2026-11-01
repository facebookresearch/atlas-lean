/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQSupportPhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! A finite original quotient-and-central injection bounds the actual full-axis extraspecial
  stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual original extraspecial intersection of the full-axis local stabilizer. -/
def generatedTenthAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedTenthAxis).comap inclQ

/-- Original free quotient bits and the central sign retain each actual full-axis Q fixer. -/
def generatedTenthQSupportFixerCoordinates (q : generatedTenthAxisQStabilizer) :
    (Fin 1 → ZMod 2) × ZMod 2 :=
  (generatedTenthQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.val.base,
    Multiplicative.toAdd q.val.coeff)

/-- The entire original full-axis extraspecial stabilizer embeds in its literal remaining bits. -/
theorem generatedTenth_Q_support_fixer_coordinates_injective :
    Function.Injective generatedTenthQSupportFixerCoordinates := by
  intro q r h
  have hq : rhoLocal (inclQ q.val) generatedTenthAxis = generatedTenthAxis := q.property
  have hr : rhoLocal (inclQ r.val) generatedTenthAxis = generatedTenthAxis := r.property
  have hb := congrArg (fun w : Fin 1 → ZMod 2 =>
      generatedTenthQSupportFreeProjection *ᵥ w) (congrArg Prod.fst h)
  change generatedTenthQSupportFreeProjection *ᵥ
      (generatedTenthQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.val.base) =
    generatedTenthQSupportFreeProjection *ᵥ
      (generatedTenthQSupportFreeMatrix *ᵥ Multiplicative.toAdd r.val.base) at hb
  rw [generatedTenth_Q_support_free_quotient q.val hq,
    generatedTenth_Q_support_free_quotient r.val hr] at hb
  apply Subtype.ext
  apply NormalizedCocycleExtension.Extension.ext
  · exact Multiplicative.toAdd.injective hb
  · exact Multiplicative.toAdd.injective (congrArg Prod.snd h)

/-- Every genuine original full-axis Q fixer is bounded by the remaining free and central bits. -/
theorem generatedTenth_axis_Q_stabilizer_upper :
    Nat.card generatedTenthAxisQStabilizer ≤ 4 := by
  have h := Nat.card_le_card_of_injective generatedTenthQSupportFixerCoordinates
    generatedTenth_Q_support_fixer_coordinates_injective
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
