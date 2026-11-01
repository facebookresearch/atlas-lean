/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-twenty tensor transport to twenty actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeTwentyForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeTwentyForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeTwentyForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeTwentyInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeTwentyInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeTwentyInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTwentyForwardTensorIndex (i, 0) =
      monsterNortonCodeTwentyForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTwentyForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTwentyInverseTensorIndex (i, 0) =
      monsterNortonCodeTwentyInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTwentyInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeTwentyForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeTwenty_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeTwentyInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeTwentyInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeTwenty_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from twenty original supported entries. -/
theorem monsterNortonCodeTwentySpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i)) =
          (monsterNortonCodeTwentyInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeTwentyInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeTwentyForwardSpin_norm]
  have hp :
    spinPairing x (nortonUIntegerEmbed monsterNortonCodeTwentyInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeTwentyInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeTwentyInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTwentyForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeTwentyInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeTwenty_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeTwentyInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
