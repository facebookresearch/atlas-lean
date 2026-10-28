/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-sixteen tensor transport to sixteen actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeSixteenForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeSixteenForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeSixteenForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeSixteenInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeSixteenInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeSixteenInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSixteenForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeSixteenForwardTensorIndex (i, 0) =
      monsterNortonCodeSixteenForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeSixteenForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeSixteenInverseTensorIndex (i, 0) =
      monsterNortonCodeSixteenInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeSixteenInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeSixteenForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeSixteenForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeSixteenForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeSixteen_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeSixteenInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSixteenInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeSixteenInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeSixteenInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeSixteenInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeSixteen_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from sixteen original supported entries. -/
theorem monsterNortonCodeSixteenSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i)) =
          (monsterNortonCodeSixteenInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeSixteenInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeSixteenForwardSpin_norm]
  have hp :
    spinPairing x (nortonUIntegerEmbed monsterNortonCodeSixteenInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeSixteenInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeSixteenInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeSixteenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeSixteenInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeSixteen_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeSixteenInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
