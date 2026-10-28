/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQSupportPhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairOrbit

/-! A finite original quotient-and-central injection bounds the actual full-axis extraspecial
  stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual original extraspecial intersection of the full-axis local stabilizer. -/
def generatedFifthRootEightAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedFifthRootEightAxis).comap inclQ

/-- Original free quotient bits and the central sign retain each actual full-axis Q fixer. -/
def generatedFifthRootEightQSupportFixerCoordinates (q : generatedFifthRootEightAxisQStabilizer) :
    (Fin 2 → ZMod 2) × ZMod 2 :=
  (generatedFifthRootEightQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.val.base,
    Multiplicative.toAdd q.val.coeff)

/-- The entire original full-axis extraspecial stabilizer embeds in its literal remaining bits. -/
theorem generatedFifthRootEight_Q_support_fixer_coordinates_injective :
    Function.Injective generatedFifthRootEightQSupportFixerCoordinates := by
  intro q r h
  have hq : rhoLocal (inclQ q.val) generatedFifthRootEightAxis =
      generatedFifthRootEightAxis := q.property
  have hr : rhoLocal (inclQ r.val) generatedFifthRootEightAxis =
      generatedFifthRootEightAxis := r.property
  have hb := congrArg (fun w : Fin 2 → ZMod 2 =>
      generatedFifthRootEightQSupportFreeProjection *ᵥ w) (congrArg Prod.fst h)
  change generatedFifthRootEightQSupportFreeProjection *ᵥ
      (generatedFifthRootEightQSupportFreeMatrix *ᵥ Multiplicative.toAdd q.val.base) =
    generatedFifthRootEightQSupportFreeProjection *ᵥ
      (generatedFifthRootEightQSupportFreeMatrix *ᵥ Multiplicative.toAdd r.val.base) at hb
  rw [generatedFifthRootEight_Q_support_free_quotient q.val hq,
    generatedFifthRootEight_Q_support_free_quotient r.val hr] at hb
  apply Subtype.ext
  apply NormalizedCocycleExtension.Extension.ext
  · exact Multiplicative.toAdd.injective hb
  · exact Multiplicative.toAdd.injective (congrArg Prod.snd h)

/-- Every genuine original full-axis Q fixer is bounded by the remaining free and central bits. -/
theorem generatedFifthRootEight_axis_Q_stabilizer_upper :
    Nat.card generatedFifthRootEightAxisQStabilizer ≤ 8 := by
  have h := Nat.card_le_card_of_injective generatedFifthRootEightQSupportFixerCoordinates
    generatedFifthRootEight_Q_support_fixer_coordinates_injective
  norm_num [Nat.card_eq_fintype_card] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
