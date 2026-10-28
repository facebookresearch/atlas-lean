/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorCircuitData

/-! Genuine monomial action and paired Fourier factorization for the corrected mover spin circuit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The genuine combined correction and compact Pauli, including its full original central product. -/
def generatedRootEightMoverTensorPostPauli : Q :=
  generatedRootEightMoverMateCorrection 0 * generatedRootEightCompactPauli 10

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedRootEightMoverTensorPre : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 10)) *
      monsterMonomialPermutationHolomorph (generatedRootEightCompactRight 10)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedRootEightMoverTensorPost : SpinHolomorph :=
  spinHolomorphIncl (generatedRootEightMoverTensorPostPauli) *
    monsterMonomialPermutationHolomorph (generatedRootEightCompactLeft 10) *
      monsterMonomialDiagonalHolomorph
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 10))

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedRootEightMoverTensorAddressCondition (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedRootEightMoverTensorPreLabel n =
      nortonUIntegerLabel ((generatedRootEightCompactRight 10).symm t) ∧
    generatedRootEightMoverTensorPreSign n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 10))
          t) ∧
    generatedRootEightMoverTensorPostLabel n = nortonUIntegerLabel
      ((generatedRootEightCompactLeft 10).symm
        (t + spinTranslation (generatedRootEightMoverTensorPostPauli))) ∧
    generatedRootEightMoverTensorPostSign n =
      nortonUIntegerSign (spinPhase (generatedRootEightMoverTensorPostPauli) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 10))
            ((generatedRootEightCompactLeft 10).symm
              (t + spinTranslation (generatedRootEightMoverTensorPostPauli))))

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedRootEight_mover_tensor_pre_embed
    (h : ∀ n, generatedRootEightMoverTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightMoverTensorPre).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightMoverTensorPreInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightMoverTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 10)) t) *
      (v (nortonUIntegerLabel ((generatedRootEightCompactRight 10).symm t)) : ℝ) =
        (generatedRootEightMoverTensorPreSign (nortonUIntegerLabel t) *
          v (generatedRootEightMoverTensorPreLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedRootEight_mover_tensor_post_embed
    (h : ∀ n, generatedRootEightMoverTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightMoverTensorPost).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightMoverTensorPostInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightMoverTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedRootEightMoverTensorPostPauli) t) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 10))
        ((generatedRootEightCompactLeft 10).symm
          (t + spinTranslation (generatedRootEightMoverTensorPostPauli)))) *
      ((v (nortonUIntegerLabel ((generatedRootEightCompactLeft 10).symm
        (t + spinTranslation (generatedRootEightMoverTensorPostPauli))))) : ℝ)) =
      (generatedRootEightMoverTensorPostSign (nortonUIntegerLabel t) *
        v (generatedRootEightMoverTensorPostLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- The paired Fourier word is exactly the original six-factor word. -/
theorem generatedRootEight_mover_tensor_pair_word :
    generatedRootEightCompactHadamardWord 10 =
      generatedRootEightMoverTensorPairWord.reverse.flatMap (fun p => [p.1, p.2]) := by
  decide +kernel

private theorem pair_prod (pairs : List (Fin 12 × Fin 12)) :
    ((pairs.flatMap (fun p => [p.1, p.2])).map generatedNinthLowerSpinHadamard).prod =
      (pairs.map generatedNinthLowerSpinTensorPair).prod := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih]
    rfl

/-- The compact spin operator is the genuine pre action, all three pairs and the post action. -/
theorem generatedRootEight_mover_tensor_compact_factorization :
    generatedRootEightMoverCorrectedFiber.val.1 = generatedRootEightMoverTensorPost *
      ((generatedRootEightMoverTensorPairWord.reverse.map
        generatedNinthLowerSpinTensorPair).prod) * generatedRootEightMoverTensorPre := by
  rw [generatedRootEight_mover_corrected_spin, generatedRootEightCompactSpin, generatedRootEight_mover_tensor_pair_word,
    pair_prod]
  simp only [generatedRootEightMoverTensorPostPauli, map_mul, generatedRootEightMoverTensorPre, generatedRootEightMoverTensorPost, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
