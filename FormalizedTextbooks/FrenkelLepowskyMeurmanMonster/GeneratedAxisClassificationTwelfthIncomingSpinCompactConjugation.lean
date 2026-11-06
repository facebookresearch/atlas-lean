/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

/-! Genuine compact products have their full original extraspecial conjugation formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact full-Q image of the compact original binary-coordinate Fourier word. -/
def generatedTwelfthIncomingSpinCompactFourierQImage (i : Fin 1) (q : Q) : Q :=
  (generatedTwelfthIncomingSpinCompactHadamardWord i).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The compact model's full original extraspecial image, including its Pauli correction. -/
def generatedTwelfthIncomingSpinCompactQImage (i : Fin 1) (q : Q) : Q :=
  generatedTwelfthIncomingSpinCompactPauli i *
    monsterMonomialPermutationImage (generatedTwelfthIncomingSpinCompactLeft i)
      (monsterMonomialDiagonalImage
        (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactFirstPhaseRows i))
        (generatedTwelfthIncomingSpinCompactFourierQImage i
          (monsterMonomialDiagonalImage
            (generatedTwelfthIncomingSpinCompactPhase
              (generatedTwelfthIncomingSpinCompactSecondPhaseRows i))
            (monsterMonomialPermutationImage (generatedTwelfthIncomingSpinCompactRight i) q)))) *
      (generatedTwelfthIncomingSpinCompactPauli i)⁻¹

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
theorem generatedTwelfth_incoming_spin_compact_conjugation (i : Fin 1) (q : Q) :
    spinConjugation (generatedTwelfthIncomingSpinCompact i) q =
      generatedTwelfthIncomingSpinCompactQImage i q := by
  rw [generatedTwelfthIncomingSpinCompact]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
