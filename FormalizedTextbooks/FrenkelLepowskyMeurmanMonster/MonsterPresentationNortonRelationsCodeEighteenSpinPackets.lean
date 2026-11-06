/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-eighteen tensor transport to sixteen actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeEighteenForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeEighteenForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeEighteenForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeEighteenInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeEighteenInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeEighteenInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeEighteenForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeEighteenForwardTensorIndex (i, 0) =
      monsterNortonCodeEighteenForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeEighteenForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeEighteenInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeEighteenInverseTensorIndex (i, 0) =
      monsterNortonCodeEighteenInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeEighteenInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeEighteenForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeEighteenForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeEighteenForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeEighteenForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeEighteenForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeEighteen_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeEighteenInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeEighteenInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeEighteenInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeEighteenInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeEighteenInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeEighteen_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from sixteen original supported entries. -/
theorem monsterNortonCodeEighteenSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeEighteenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeEighteenInverseSpinLabel i)) =
          (monsterNortonCodeEighteenInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
      monsterNortonCodeEighteenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeEighteenInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeEighteenForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeEighteenForwardSpin_norm]
  have hp :
    spinPairing x (nortonUIntegerEmbed monsterNortonCodeEighteenInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeEighteenInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeEighteenInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeEighteenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeEighteenInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeEighteen_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeEighteenInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
