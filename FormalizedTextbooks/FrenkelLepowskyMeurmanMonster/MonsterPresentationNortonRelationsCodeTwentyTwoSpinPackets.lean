/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact spin packet norms reduce each basis22 physical column to four actual coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The complete original integer forward spin candidate. -/
def monsterNortonCodeTwentyTwoForwardSpinInteger (k : Fin 16) : NortonUIntegerVector := fun n =>
  ∑ i : Fin 64, monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k i *
    (Pi.single (monsterNortonCodeTwentyTwoForwardSpinLabel i) 1 : NortonUIntegerVector) n

/-- The complete original integer inverse spin candidate. -/
def monsterNortonCodeTwentyTwoInverseSpinInteger (k : Fin 16) : NortonUIntegerVector := fun n =>
  ∑ i : Fin 4, monsterNortonCodeTwentyTwoInverseTensorTable k i *
    (Pi.single (monsterNortonCodeTwentyTwoInverseSpinLabel k i) 1 : NortonUIntegerVector) n

private theorem forward_label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyTwoForwardSpinLabel i)) := by
  intro i j h
  have hi : monsterNortonCodeTwentyTwoForwardTensorIndex (i, 0) =
      monsterNortonCodeTwentyTwoForwardTensorIndex (j, 0) := Prod.ext h rfl
  exact congrArg Prod.fst (monsterNortonCodeTwentyTwoForwardTensorIndex_injective hi)

private theorem inverse_label_injective (k : Fin 16) : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel k i)) := by
  intro i j h
  have hi : monsterNortonCodeTwentyTwoInverseTensorIndex (k, i) =
      monsterNortonCodeTwentyTwoInverseTensorIndex (k, j) := Prod.ext h rfl
  exact congrArg Prod.snd (monsterNortonCodeTwentyTwoInverseTensorIndex_injective hi)

/-- The full forward spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyTwoForwardSpin_norm (k : Fin 16) :
    spinPairing (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k))
      (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k)) = 64 := by
  unfold monsterNortonCodeTwentyTwoForwardSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ forward_label_injective]
  have hs :
      (∑ i : Fin 64, (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k i : ℝ) ^ 2) = 64 := by
    have h : (∑ i : Fin 64, monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k i ^ 2) = 64 := by
      revert k
      decide +kernel
    exact_mod_cast h
  exact hs

/-- The full inverse spin candidate has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyTwoInverseSpin_norm (k : Fin 16) :
    spinPairing (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k))
      (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k)) = 64 := by
  unfold monsterNortonCodeTwentyTwoInverseSpinInteger
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ (inverse_label_injective k)]
  have hs : (∑ i : Fin 4, (monsterNortonCodeTwentyTwoInverseTensorTable k i : ℝ) ^ 2) = 64 := by
    have h : (∑ i : Fin 4, monsterNortonCodeTwentyTwoInverseTensorTable k i ^ 2) = 64 := by
      revert k
      decide +kernel
    exact_mod_cast h
  exact hs

/-- Orthogonality determines each whole image from four original supported entries. -/
theorem monsterNortonCodeTwentyTwoSpin_transport_of_coefficients (k : Fin 16)
    (hc : ∀ i : Fin 4,
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        (monsterNortonCodeTwentyTwoForwardSpinInteger k))
        (golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel k i)) =
          (monsterNortonCodeTwentyTwoInverseTensorTable k i : ℝ)) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
      (monsterNortonCodeTwentyTwoForwardSpinInteger k)) =
      nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k) := by
  let x := monsterNortonUFiber.val.1.val
    (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k))
  have hn : spinPairing x x = 64 := by
    rw [monsterNortonUFiber.val.1.property.2, (monsterNortonCodeTwentyTwoForwardSpin_norm k)]
  have hp : spinPairing x (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k)) =
    64 := by
    unfold monsterNortonCodeTwentyTwoInverseSpinInteger
    rw [monsterNortonUIntegerEmbed_packet,
      monsterNortonSpin_sparse_pairing]
    change (∑ i : Fin 4, (monsterNortonCodeTwentyTwoInverseTensorTable k i : ℝ) *
      monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
        (monsterNortonCodeTwentyTwoForwardSpinInteger k))
        (golayLabelCoefficients (monsterNortonCodeTwentyTwoInverseSpinLabel k i))) = 64
    simp_rw [hc, ← pow_two]
    have h : (∑ i : Fin 4, monsterNortonCodeTwentyTwoInverseTensorTable k i ^ 2) = 64 := by
      have hf : ∀ k : Fin 16,
          (∑ i : Fin 4, monsterNortonCodeTwentyTwoInverseTensorTable k i ^ 2) = 64 := by
        decide +kernel
      exact hf k
    exact_mod_cast h
  apply monsterNortonSpin_eq_of_pairing
  · rw [hn, (monsterNortonCodeTwentyTwoInverseSpin_norm k)]
  · rw [hp, hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
