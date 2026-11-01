/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-nineteen tensor transport to nineteen actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeNineteenForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeNineteenForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeNineteenForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeNineteenInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeNineteenInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeNineteenInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeNineteenForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeNineteenForwardTensorIndex (i, 0) =
      monsterNortonCodeNineteenForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeNineteenForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeNineteenInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeNineteenInverseTensorIndex (i, 0) =
      monsterNortonCodeNineteenInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeNineteenInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeNineteenForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeNineteenForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeNineteenForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeNineteenForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeNineteenForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeNineteen_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeNineteenInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeNineteenInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeNineteenInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeNineteenInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeNineteenInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeNineteen_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from nineteen original supported entries. -/
theorem monsterNortonCodeNineteenSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeNineteenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeNineteenInverseSpinLabel i)) =
          (monsterNortonCodeNineteenInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
      monsterNortonCodeNineteenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeNineteenInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeNineteenForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeNineteenForwardSpin_norm]
  have hp :
    spinPairing x (nortonUIntegerEmbed monsterNortonCodeNineteenInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeNineteenInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeNineteenInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeNineteenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeNineteenInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeNineteen_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeNineteenInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
