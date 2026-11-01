/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce code-twentyone tensor transport to twentyone actual
  coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeTwentyOneForwardSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeTwentyOneForwardSpinCoefficient i *
    (Pi.single (monsterNortonCodeTwentyOneForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeTwentyOneInverseSpinInteger : NortonUIntegerVector := fun n =>
  ∑ i : Fin 16, monsterNortonCodeTwentyOneInverseSpinCoefficient i *
    (Pi.single (monsterNortonCodeTwentyOneInverseSpinLabel i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyOneForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTwentyOneForwardTensorIndex (i, 0) =
      monsterNortonCodeTwentyOneForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTwentyOneForwardTensorIndex_injective hi)

private theorem inverse_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyOneInverseSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTwentyOneInverseTensorIndex (i, 0) =
      monsterNortonCodeTwentyOneInverseTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTwentyOneInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyOneForwardSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyOneForwardSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeTwentyOneForwardSpinInteger) = 64 := by
  unfold monsterNortonCodeTwentyOneForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyOneForwardSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeTwentyOne_forward_spin_sq
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyOneInverseSpin_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyOneInverseSpinInteger)
      (nortonUIntegerEmbed monsterNortonCodeTwentyOneInverseSpinInteger) = 64 := by
  unfold monsterNortonCodeTwentyOneInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ inverse_label_injective]
  have hs : (∑ i : Fin 16, (monsterNortonCodeTwentyOneInverseSpinCoefficient i : ℝ) ^ 2) = 64 := by
    exact_mod_cast monsterNortonCodeTwentyOne_inverse_spin_sq
  exact hs

/-- Orthogonality determines the complete actual image from twentyone original supported entries. -/
theorem monsterNortonCodeTwentyOneSpin_transport_of_coefficients
    (hc : ∀ i : Fin 16,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeTwentyOneForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeTwentyOneInverseSpinLabel i)) =
          (monsterNortonCodeTwentyOneInverseSpinCoefficient i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
      monsterNortonCodeTwentyOneForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeTwentyOneInverseSpinInteger := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed monsterNortonCodeTwentyOneForwardSpinInteger)
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, monsterNortonCodeTwentyOneForwardSpin_norm]
  have hp :
    spinPairing x (nortonUIntegerEmbed monsterNortonCodeTwentyOneInverseSpinInteger) = 64 := by
    unfold monsterNortonCodeTwentyOneInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 16, (monsterNortonCodeTwentyOneInverseSpinCoefficient i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        monsterNortonCodeTwentyOneForwardSpinInteger)
        (golayLabelCoefficients (monsterNortonCodeTwentyOneInverseSpinLabel i))) = 64
    simp_rw [hc, ← pow_two]
    exact_mod_cast monsterNortonCodeTwentyOne_inverse_spin_sq
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, monsterNortonCodeTwentyOneInverseSpin_norm]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
