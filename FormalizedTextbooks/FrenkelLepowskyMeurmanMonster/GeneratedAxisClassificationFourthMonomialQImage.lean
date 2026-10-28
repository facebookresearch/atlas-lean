/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinModelAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators

/-! Exact full-Q images from the verified original signed spin matrix models. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The verified original spin word, expressed as its signed diagonal and label pullback. -/
def generatedFourthMonomialModelSpin (k : Fin 4) : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (generatedFourthMonomialSpinModel k).phase *
    monsterMonomialPermutationHolomorph (generatedFourthMonomialLabelEquiv k).symm

/-- The explicit model is the genuine original spin word, including all central signs. -/
theorem generatedFourth_monomial_model_spin_eq (k : Fin 4) :
    generatedFourthMonomialModelSpin k = (generatedFourthMonomialFiber k).val.1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro f
  ext t
  have h : (generatedFourthMonomialFiber k).val.1.val f t =
      qSign (monsterMonomialQuadratic (generatedFourthMonomialSpinModel k).phase t) *
        f ((generatedFourthMonomialSpinModel k).coordinate *ᵥ t) :=
    generatedFourth_monomial_spin_model_certificate k f t
  exact h.symm

/-- Full original Q image before the actual extraspecial correction. -/
def generatedFourthMonomialModelQImage (k : Fin 4) (q : Q) : Q :=
  monsterMonomialDiagonalImage (generatedFourthMonomialSpinModel k).phase
    (monsterMonomialPermutationImage (generatedFourthMonomialLabelEquiv k).symm q)

/-- The finite expression is the actual conjugation on every original extraspecial element. -/
theorem generatedFourth_monomial_model_q_image (k : Fin 4) (q : Q) :
    spinConjugation (generatedFourthMonomialFiber k).val.1 q =
      generatedFourthMonomialModelQImage k q := by
  rw [← generatedFourth_monomial_model_spin_eq, generatedFourthMonomialModelSpin, map_mul]
  change spinConjugation (monsterMonomialDiagonalHolomorph
    (generatedFourthMonomialSpinModel k).phase)
    (spinConjugation (monsterMonomialPermutationHolomorph
      (generatedFourthMonomialLabelEquiv k).symm) q) = _
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation]
  rfl

/-- The corrected full Q image, with the actual central cocycle retained. -/
def generatedFourthMonomialCorrectedQImage (k : Fin 4) (q : Q) : Q :=
  generatedFourthMonomialCorrection k * generatedFourthMonomialModelQImage k q *
    (generatedFourthMonomialCorrection k)⁻¹

/-- The compact corrected expression equals the genuine local lift's full Q action. -/
theorem generatedFourth_monomial_corrected_q_image (k : Fin 4) (q : Q) :
    spinConjugation (generatedFourthMonomialCorrectedFiber k).val.1 q =
      generatedFourthMonomialCorrectedQImage k q := by
  change spinConjugation (spinHolomorphIncl (generatedFourthMonomialCorrection k) *
    (generatedFourthMonomialFiber k).val.1) q = _
  rw [map_mul]
  change spinConjugation (spinHolomorphIncl (generatedFourthMonomialCorrection k))
    (spinConjugation (generatedFourthMonomialFiber k).val.1 q) = _
  rw [generatedFourth_monomial_model_q_image, spinConjugation_incl]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
