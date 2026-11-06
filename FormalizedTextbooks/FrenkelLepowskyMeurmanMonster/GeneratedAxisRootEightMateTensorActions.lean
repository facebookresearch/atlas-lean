/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorData

/-! Genuine monomial action and paired Fourier factorization for the corrected mate spin circuit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 110000

/-- The genuine combined correction and compact Pauli, including its full original central product. -/
def generatedRootEightMateTensorPostPauli : Q :=
  generatedRootEightMoverMateCorrection 1 * generatedRootEightCompactPauli 11

/-- Genuine right monomial followed by the actual second quadratic diagonal. -/
def generatedRootEightMateTensorPre : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph
    (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 11)) *
      monsterMonomialPermutationHolomorph (generatedRootEightCompactRight 11)

/-- Genuine first quadratic diagonal, left monomial and complete central Pauli. -/
def generatedRootEightMateTensorPost : SpinHolomorph :=
  spinHolomorphIncl (generatedRootEightMateTensorPostPauli) *
    monsterMonomialPermutationHolomorph (generatedRootEightCompactLeft 11) *
      monsterMonomialDiagonalHolomorph
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 11))

/-- Exact finite source-address conditions for both compact monomial boundaries. -/
def generatedRootEightMateTensorAddressCondition (n : Fin 4096) : Prop :=
  let t := golayLabelCoefficients n
  generatedRootEightMateTensorPreLabel n =
      nortonUIntegerLabel ((generatedRootEightCompactRight 11).symm t) ∧
    generatedRootEightMateTensorPreSign n =
      nortonUIntegerSign (monsterMonomialQuadratic
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 11))
          t) ∧
    generatedRootEightMateTensorPostLabel n = nortonUIntegerLabel
      ((generatedRootEightCompactLeft 11).symm
        (t + spinTranslation (generatedRootEightMateTensorPostPauli))) ∧
    generatedRootEightMateTensorPostSign n =
      nortonUIntegerSign (spinPhase (generatedRootEightMateTensorPostPauli) t) *
        nortonUIntegerSign (monsterMonomialQuadratic
          (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 11))
            ((generatedRootEightCompactLeft 11).symm
              (t + spinTranslation (generatedRootEightMateTensorPostPauli))))

/-- Exact address and sign certificates identify the whole genuine pre-boundary operator. -/
theorem generatedRootEight_mate_tensor_pre_embed
    (h : ∀ n, generatedRootEightMateTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightMateTensorPre).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightMateTensorPreInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightMateTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (monsterMonomialQuadratic
    (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 11)) t) *
      (v (nortonUIntegerLabel ((generatedRootEightCompactRight 11).symm t)) : ℝ) =
        (generatedRootEightMateTensorPreSign (nortonUIntegerLabel t) *
          v (generatedRootEightMateTensorPreLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.1, ht.2.1, Int.cast_mul, nortonUIntegerSign_real]

/-- The post-boundary certificate keeps the complete actual Pauli central sign. -/
theorem generatedRootEight_mate_tensor_post_embed
    (h : ∀ n, generatedRootEightMateTensorAddressCondition n)
    (v : NortonUIntegerVector) :
    (generatedRootEightMateTensorPost).val (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedRootEightMateTensorPostInteger v) := by
  ext t
  have ht := h (nortonUIntegerLabel t)
  simp only [generatedRootEightMateTensorAddressCondition,
    nortonUIntegerLabel_inverse] at ht
  change qSign (spinPhase (generatedRootEightMateTensorPostPauli) t) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 11))
        ((generatedRootEightCompactLeft 11).symm
          (t + spinTranslation (generatedRootEightMateTensorPostPauli)))) *
      ((v (nortonUIntegerLabel ((generatedRootEightCompactLeft 11).symm
        (t + spinTranslation (generatedRootEightMateTensorPostPauli))))) : ℝ)) =
      (generatedRootEightMateTensorPostSign (nortonUIntegerLabel t) *
        v (generatedRootEightMateTensorPostLabel (nortonUIntegerLabel t)) : ℤ)
  rw [ht.2.2.1, ht.2.2.2, Int.cast_mul, Int.cast_mul,
    nortonUIntegerSign_real, nortonUIntegerSign_real]
  ring

/-- The original mate contains no Fourier factor. -/
theorem generatedRootEight_mate_tensor_empty_word : generatedRootEightCompactHadamardWord 11 = [] := by
  decide +kernel

/-- Exact rank-zero factorization retains both original phases and the full Pauli correction. -/
theorem generatedRootEight_mate_tensor_compact_factorization :
    generatedRootEightMateCorrectedFiber.val.1 = generatedRootEightMateTensorPost *
      generatedRootEightMateTensorPre := by
  rw [generatedRootEight_mate_corrected_spin, generatedRootEightCompactSpin,
    generatedRootEight_mate_tensor_empty_word]
  simp only [List.map_nil, List.prod_nil, mul_one, generatedRootEightMateTensorPostPauli,
    map_mul, generatedRootEightMateTensorPre, generatedRootEightMateTensorPost, mul_assoc]

/-- The entire actual corrected mate spin acts by its certified original signed addresses. -/
theorem generatedRootEight_mate_tensor_spin_coordinate
    (h : ∀ n, generatedRootEightMateTensorAddressCondition n)
    (f : SpinSpace) (t : SpinIndex) :
    generatedRootEightMateCorrectedFiber.val.1.val f t =
      (generatedRootEightMateTensorPostSign (nortonUIntegerLabel t) : ℝ) *
      (generatedRootEightMateTensorPreSign
        (generatedRootEightMateTensorPostLabel (nortonUIntegerLabel t)) : ℝ) *
      f (golayLabelCoefficients (generatedRootEightMateTensorPreLabel
        (generatedRootEightMateTensorPostLabel (nortonUIntegerLabel t)))) := by
  rw [generatedRootEight_mate_tensor_compact_factorization]
  have hp := h (nortonUIntegerLabel t)
  simp only [generatedRootEightMateTensorAddressCondition, nortonUIntegerLabel_inverse] at hp
  have hq := h (generatedRootEightMateTensorPostLabel (nortonUIntegerLabel t))
  simp only [generatedRootEightMateTensorAddressCondition] at hq
  change qSign (spinPhase generatedRootEightMateTensorPostPauli t) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows 11))
      ((generatedRootEightCompactLeft 11).symm (t + spinTranslation generatedRootEightMateTensorPostPauli))) *
    (qSign (monsterMonomialQuadratic
      (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactSecondPhaseRows 11))
      ((generatedRootEightCompactLeft 11).symm (t + spinTranslation generatedRootEightMateTensorPostPauli))) *
      f ((generatedRootEightCompactRight 11).symm
        ((generatedRootEightCompactLeft 11).symm (t + spinTranslation generatedRootEightMateTensorPostPauli))))) = _
  have he := congrArg golayLabelCoefficients hp.2.2.1
  simp only [nortonUIntegerLabel_inverse] at he
  have hps := congrArg (fun z : ℤ => (z : ℝ)) hp.2.2.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hps
  rw [← he] at hps
  have hqs := congrArg (fun z : ℤ => (z : ℝ)) hq.2.1
  simp only [nortonUIntegerSign_real] at hqs
  have hqa := congrArg golayLabelCoefficients hq.1
  simp only [nortonUIntegerLabel_inverse] at hqa
  rw [← he, ← hqs, ← hqa]
  rw [hps]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
