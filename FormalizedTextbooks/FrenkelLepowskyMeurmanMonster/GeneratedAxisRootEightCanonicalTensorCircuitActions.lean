/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCircuitData

/-! Genuine monomial action and paired Fourier factorization for the canonical spin circuit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedRootEightCanonicalTensorPre : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 12)) *
      monsterMonomialPermutationHolomorph (generatedRootEightCompactRight 12)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedRootEightCanonicalTensorPost : SpinHolomorph :=
  spinHolomorphIncl (generatedRootEightCompactPauli 12) *
    monsterMonomialPermutationHolomorph (generatedRootEightCompactLeft 12) *
      monsterMonomialDiagonalHolomorph
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 12))

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedRootEightCanonicalTensorAddressCondition (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedRootEightCanonicalTensorPreLabel n =
      nortonUIntegerLabel ((generatedRootEightCompactRight 12).symm t) ∧
    generatedRootEightCanonicalTensorPreSign n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 12))
          t) ∧
    generatedRootEightCanonicalTensorPostLabel n = nortonUIntegerLabel
      ((generatedRootEightCompactLeft 12).symm
        (t + spinTranslation (generatedRootEightCompactPauli 12))) ∧
    generatedRootEightCanonicalTensorPostSign n =
      nortonUIntegerSign (spinPhase (generatedRootEightCompactPauli 12) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 12))
            ((generatedRootEightCompactLeft 12).symm
              (t + spinTranslation (generatedRootEightCompactPauli 12))))

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedRootEight_canonical_tensor_pre_embed
    (h : ∀ n, generatedRootEightCanonicalTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightCanonicalTensorPre).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightCanonicalTensorPreInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightCanonicalTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 12)) t) *
      (v (nortonUIntegerLabel ((generatedRootEightCompactRight 12).symm t)) : ℝ) =
        (generatedRootEightCanonicalTensorPreSign (nortonUIntegerLabel t) *
          v (generatedRootEightCanonicalTensorPreLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedRootEight_canonical_tensor_post_embed
    (h : ∀ n, generatedRootEightCanonicalTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightCanonicalTensorPost).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightCanonicalTensorPostInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightCanonicalTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedRootEightCompactPauli 12) t) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 12))
        ((generatedRootEightCompactLeft 12).symm
          (t + spinTranslation (generatedRootEightCompactPauli 12)))) *
      ((v (nortonUIntegerLabel ((generatedRootEightCompactLeft 12).symm
        (t + spinTranslation (generatedRootEightCompactPauli 12))))) : ℝ)) =
      (generatedRootEightCanonicalTensorPostSign (nortonUIntegerLabel t) *
        v (generatedRootEightCanonicalTensorPostLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- The paired Fourier word is exactly the original eight-factor word. -/
theorem generatedRootEight_canonical_tensor_pair_word :
    generatedRootEightCompactHadamardWord 12 =
      generatedRootEightCanonicalTensorPairWord.reverse.flatMap (fun p => [p.1, p.2]) := by
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
theorem generatedRootEight_canonical_tensor_compact_factorization :
    generatedRootEightCompactSpin 12 = generatedRootEightCanonicalTensorPost *
      ((generatedRootEightCanonicalTensorPairWord.reverse.map
        generatedNinthLowerSpinTensorPair).prod) * generatedRootEightCanonicalTensorPre := by
  rw [generatedRootEightCompactSpin, generatedRootEight_canonical_tensor_pair_word,
    pair_prod]
  simp only [generatedRootEightCanonicalTensorPre, generatedRootEightCanonicalTensorPost, mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
