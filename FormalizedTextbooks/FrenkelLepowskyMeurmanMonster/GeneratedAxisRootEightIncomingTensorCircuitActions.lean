/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitData

/-! Genuine monomial action and paired Fourier factorization for the incoming spin circuit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedRootEightIncomingTensorPre : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactSecondPhaseRows 0)) *
      monsterMonomialPermutationHolomorph (generatedRootEightIncomingCompactRight 0)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedRootEightIncomingTensorPost : SpinHolomorph :=
  spinHolomorphIncl (generatedRootEightIncomingCompactPauli 0) *
    monsterMonomialPermutationHolomorph (generatedRootEightIncomingCompactLeft 0) *
      monsterMonomialDiagonalHolomorph
        (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactFirstPhaseRows 0))

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedRootEightIncomingTensorAddressCondition (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedRootEightIncomingTensorPreLabel n =
      nortonUIntegerLabel ((generatedRootEightIncomingCompactRight 0).symm t) ∧
    generatedRootEightIncomingTensorPreSign n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactSecondPhaseRows 0))
          t) ∧
    generatedRootEightIncomingTensorPostLabel n = nortonUIntegerLabel
      ((generatedRootEightIncomingCompactLeft 0).symm
        (t + spinTranslation (generatedRootEightIncomingCompactPauli 0))) ∧
    generatedRootEightIncomingTensorPostSign n =
      nortonUIntegerSign (spinPhase (generatedRootEightIncomingCompactPauli 0) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactFirstPhaseRows 0))
            ((generatedRootEightIncomingCompactLeft 0).symm
              (t + spinTranslation (generatedRootEightIncomingCompactPauli 0))))

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedRootEight_incoming_tensor_pre_embed
    (h : ∀ n, generatedRootEightIncomingTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightIncomingTensorPre).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightIncomingTensorPreInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightIncomingTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactSecondPhaseRows 0)) t) *
      (v (nortonUIntegerLabel ((generatedRootEightIncomingCompactRight 0).symm t)) : ℝ) =
        (generatedRootEightIncomingTensorPreSign (nortonUIntegerLabel t) *
          v (generatedRootEightIncomingTensorPreLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedRootEight_incoming_tensor_post_embed
    (h : ∀ n, generatedRootEightIncomingTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightIncomingTensorPost).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightIncomingTensorPostInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightIncomingTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedRootEightIncomingCompactPauli 0) t) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactFirstPhaseRows 0))
        ((generatedRootEightIncomingCompactLeft 0).symm
          (t + spinTranslation (generatedRootEightIncomingCompactPauli 0)))) *
      ((v (nortonUIntegerLabel ((generatedRootEightIncomingCompactLeft 0).symm
        (t + spinTranslation (generatedRootEightIncomingCompactPauli 0))))) : ℝ)) =
      (generatedRootEightIncomingTensorPostSign (nortonUIntegerLabel t) *
        v (generatedRootEightIncomingTensorPostLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- The paired Fourier word is exactly the original eight-factor word. -/
theorem generatedRootEight_incoming_tensor_pair_word :
    generatedRootEightIncomingCompactHadamardWord 0 =
      generatedRootEightIncomingTensorPairWord.reverse.flatMap (fun p => [p.1, p.2]) := by
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

/-- The compact spin operator is the genuine pre action, all four pairs and the post action. -/
theorem generatedRootEight_incoming_tensor_compact_factorization :
    generatedRootEightIncomingCompactSpin 0 = generatedRootEightIncomingTensorPost *
      ((generatedRootEightIncomingTensorPairWord.reverse.map
        generatedNinthLowerSpinTensorPair).prod) * generatedRootEightIncomingTensorPre := by
  rw [generatedRootEightIncomingCompactSpin, generatedRootEight_incoming_tensor_pair_word,
    pair_prod]
  simp only [generatedRootEightIncomingTensorPre, generatedRootEightIncomingTensorPost, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
