/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-seven tensor transport to sixteen actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeSevenForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 64, monsterNortonCodeSevenForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeSevenForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeSevenInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeSevenInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeSevenInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSevenForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeSevenForwardTensorIndex (i, 0) =
      monsterNortonCodeSevenForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeSevenForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSevenInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeSevenInverseTensorIndex (i, 0) =
      monsterNortonCodeSevenInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeSevenInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeSevenForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeSevenForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 64, (monsterNortonCodeSevenForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeSeven_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeSevenInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSevenInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeSevenInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeSevenInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeSevenInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeSeven_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from sixteen original supported entries. -/
theorem monsterNortonCodeSevenSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeSevenInverseSpinLabel i)) =
          (monsterNortonCodeSevenInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeSevenInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeSevenForwardSpin_norm]
  have hp : spinPairing x (nortonUIntegerEmbed monsterNortonCodeSevenInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeSevenInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeSevenInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeSevenForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeSevenInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeSeven_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeSevenInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
