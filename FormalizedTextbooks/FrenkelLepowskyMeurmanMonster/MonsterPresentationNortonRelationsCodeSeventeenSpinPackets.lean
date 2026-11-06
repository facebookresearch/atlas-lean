/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-seventeen tensor transport to seventeen actual
  coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeSeventeenForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeSeventeenForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeSeventeenForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeSeventeenInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeSeventeenInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeSeventeenInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSeventeenForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeSeventeenForwardTensorIndex (i, 0) =
      monsterNortonCodeSeventeenForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeSeventeenForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeSeventeenInverseTensorIndex (i, 0) =
      monsterNortonCodeSeventeenInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeSeventeenInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeSeventeenForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSeventeenForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeSeventeenForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeSeventeenForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeSeventeenForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeSeventeen_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeSeventeenInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSeventeenInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeSeventeenInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeSeventeenInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeSeventeenInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeSeventeen_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from seventeen original supported entries. -/
theorem monsterNortonCodeSeventeenSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeSeventeenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i)) =
          (monsterNortonCodeSeventeenInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
      monsterNortonCodeSeventeenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeSeventeenInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeSeventeenForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeSeventeenForwardSpin_norm]
  have hp :
    spinPairing x (nortonUIntegerEmbed monsterNortonCodeSeventeenInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeSeventeenInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeSeventeenInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeSeventeenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeSeventeenInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeSeventeen_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeSeventeenInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
