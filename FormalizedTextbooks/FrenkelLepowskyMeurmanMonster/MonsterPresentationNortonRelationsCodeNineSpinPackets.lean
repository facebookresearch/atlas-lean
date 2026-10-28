/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-nine tensor transport to sixteen actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeNineForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 64, monsterNortonCodeNineForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeNineForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeNineInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeNineInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeNineInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeNineForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeNineForwardTensorIndex (i, 0) =
      monsterNortonCodeNineForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeNineForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeNineInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeNineInverseTensorIndex (i, 0) =
      monsterNortonCodeNineInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeNineInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeNineForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeNineForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 64, (monsterNortonCodeNineForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeNine_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeNineInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeNineInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeNineInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeNine_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from sixteen original supported entries. -/
theorem monsterNortonCodeNineSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeNineInverseSpinLabel i)) =
          (monsterNortonCodeNineInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeNineForwardSpin_norm]
  have hp : spinPairing x (nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeNineInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeNineInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeNineInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeNine_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeNineInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
