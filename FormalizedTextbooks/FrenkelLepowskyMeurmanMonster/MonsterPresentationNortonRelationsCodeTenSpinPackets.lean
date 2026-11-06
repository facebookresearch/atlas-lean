/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce preferred-basis-ten tensor transport to four actual
coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeTenForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 64, monsterNortonCodeTenForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeTenForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeTenInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 4, monsterNortonCodeTenInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeTenInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTenForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTenForwardTensorIndex (i, 0) =
      monsterNortonCodeTenForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTenForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTenInverseTensorIndex (i, 0) =
      monsterNortonCodeTenInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTenInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTenForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeTenForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 64, (monsterNortonCodeTenForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeTen_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTenInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeTenInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 4, (monsterNortonCodeTenInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeTen_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from four original supported entries. -/
theorem monsterNortonCodeTenSpin_transport_of_coefficients
    (hc : ∀ i : Fin 4,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i)) =
          (monsterNortonCodeTenInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeTenForwardSpin_norm]
  have hp : spinPairing x (nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeTenInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 4, (monsterNortonCodeTenInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeTenInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeTen_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeTenInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
