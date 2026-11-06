/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitiveUnitsCertificates

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Both signs of every primitive source letter have all twenty-four actual full Q images. -/
theorem generatedNinth_lower_spin_primitive_units_generator (l : GeneratedNinthLowerSpinLetter)
    (j : Fin 24) :
    spinConjugation (generatedNinthLowerSpinFiberLetter l).val.1 (qCoordinateGenerator j) =
      generatedNinthLowerSpinPrimitiveQGenerator l j := by
  rcases l with ⟨k, b⟩
  cases b
  · change spinConjugation (generatedNinthLowerSpinPositiveFiber k).val.1
      (qCoordinateGenerator j) = _
    rw [generatedNinth_lower_spin_primitive_units_positive_conjugation,
      generatedNinth_lower_spin_primitive_units_positive_certificate]
  · change spinConjugation ((generatedNinthLowerSpinPositiveFiber k).val.1)⁻¹
      (qCoordinateGenerator j) = _
    have h : spinConjugation (generatedNinthLowerSpinPositiveFiber k).val.1
        (generatedNinthLowerSpinPrimitiveQGenerator (k, true) j) = qCoordinateGenerator j := by
      rw [generatedNinth_lower_spin_primitive_units_positive_conjugation,
        generatedNinth_lower_spin_primitive_units_inverse_certificate]
    rw [← h, map_inv]
    exact MulEquiv.symm_apply_apply _ _

/-- The exact ordered primitive evaluator is its entire actual spin conjugation. -/
theorem generatedNinth_lower_spin_primitive_units_evaluation (l : GeneratedNinthLowerSpinLetter)
    (q : Q) :
    spinConjugation (generatedNinthLowerSpinFiberLetter l).val.1 q =
      generatedNinthLowerSpinPrimitiveQEvaluation l q :=
  monsterNortonCoordinateEvaluation_eq _ _
    (generatedNinth_lower_spin_primitive_units_generator l) q


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
