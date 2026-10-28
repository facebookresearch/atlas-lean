/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-five tensor transport to sixteen actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeFiveForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 64, monsterNortonCodeFiveForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeFiveForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeFiveInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeFiveInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeFiveInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeFiveForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeFiveForwardTensorIndex (i, 0) =
      monsterNortonCodeFiveForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeFiveForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeFiveInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeFiveInverseTensorIndex (i, 0) =
      monsterNortonCodeFiveInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeFiveInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeFiveForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeFiveForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 64, (monsterNortonCodeFiveForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeFive_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeFiveInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeFiveInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeFiveInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeFive_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from sixteen original supported entries. -/
theorem monsterNortonCodeFiveSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeFiveInverseSpinLabel i)) =
          (monsterNortonCodeFiveInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeFiveForwardSpin_norm]
  have hp : spinPairing x (nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeFiveInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeFiveInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeFiveInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeFive_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeFiveInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
