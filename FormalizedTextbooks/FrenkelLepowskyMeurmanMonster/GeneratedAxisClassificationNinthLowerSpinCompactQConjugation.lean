/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQDecidable

/-! Complete conjugation of the genuine compact spin factors, independent
of original word replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact full-Q image of the compact original binary-coordinate Fourier word. -/
def generatedNinthLowerSpinCompactFourierQImage (i : Fin 11) (q : Q) : Q :=
  (generatedNinthLowerSpinCompactHadamardWord i).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The compact model's full original extraspecial image, including its Pauli correction. -/
def generatedNinthLowerSpinCompactQImage (i : Fin 11) (q : Q) : Q :=
  generatedNinthLowerSpinCompactPauli i *
    monsterMonomialPermutationImage (generatedNinthLowerSpinCompactLeft i)
      (monsterMonomialDiagonalImage
        (generatedNinthLowerSpinCompactPhase (generatedNinthLowerSpinCompactFirstPhaseRows i))
        (generatedNinthLowerSpinCompactFourierQImage i
          (monsterMonomialDiagonalImage
            (generatedNinthLowerSpinCompactPhase
              (generatedNinthLowerSpinCompactSecondPhaseRows i))
            (monsterMonomialPermutationImage (generatedNinthLowerSpinCompactRight i) q)))) *
      (generatedNinthLowerSpinCompactPauli i)⁻¹

private theorem fourier_list_conjugation (w : List (Fin 12)) (q : Q) :
    spinConjugation ((w.map generatedNinthLowerSpinHadamard).prod) q =
      w.foldr generatedNinthLowerSpinHadamardQImage q := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil, List.foldr_nil, map_one, MulAut.one_apply]
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, List.foldr_cons, map_mul]
    change spinConjugation (generatedNinthLowerSpinHadamard k)
      (spinConjugation ((w.map generatedNinthLowerSpinHadamard).prod) q) = _
    rw [ih, generatedNinth_lower_spin_hadamard_conjugation]

/-- The compact product's entire full-Q action is its explicit original coordinate formula. -/
theorem generatedNinth_lower_spin_compact_conjugation (i : Fin 11) (q : Q) :
    spinConjugation (generatedNinthLowerSpinCompact i) q =
      generatedNinthLowerSpinCompactQImage i q := by
  rw [generatedNinthLowerSpinCompact]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

set_option maxHeartbeats 16000000 in
-- Compare every compact full generator image with the phase-correct original source cache.
/-- All compact Q generators have the corrected original source image and central coefficient. -/
theorem generatedNinth_lower_spin_compact_generator_certificate :
    ∀ (i : Fin 11) (j : Fin 24),
      generatedNinthLowerSpinCompactQImage i (qCoordinateGenerator j) =
        generatedNinthLowerSpinCorrection i * generatedNinthLowerSpinQImage i j *
          (generatedNinthLowerSpinCorrection i)⁻¹ := by
  decide +kernel

/-- The compact model retains each actual full source Q generator image. -/
theorem generatedNinth_lower_spin_compact_generator (i : Fin 11) (j : Fin 24) :
    spinConjugation (generatedNinthLowerSpinCompact i) (qCoordinateGenerator j) =
      generatedNinthLowerSpinCorrection i * generatedNinthLowerSpinQImage i j *
        (generatedNinthLowerSpinCorrection i)⁻¹ := by
  rw [generatedNinth_lower_spin_compact_conjugation,
    generatedNinth_lower_spin_compact_generator_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
