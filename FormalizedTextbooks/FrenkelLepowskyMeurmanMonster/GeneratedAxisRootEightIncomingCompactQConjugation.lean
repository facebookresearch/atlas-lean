/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingCompactSpin
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQDecidable
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Complete conjugation of the genuine compact spin factors, independent
of original word replay. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact full-Q image of the compact original binary-coordinate Fourier word. -/
def generatedRootEightIncomingCompactFourierQImage (i : Fin 1) (q : Q) : Q :=
  (generatedRootEightIncomingCompactHadamardWord i).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The compact model's full original extraspecial image, including its Pauli correction. -/
def generatedRootEightIncomingCompactQImage (i : Fin 1) (q : Q) : Q :=
  generatedRootEightIncomingCompactPauli i *
    monsterMonomialPermutationImage (generatedRootEightIncomingCompactLeft i)
      (monsterMonomialDiagonalImage
        (generatedNinthLowerSpinCompactPhase (generatedRootEightIncomingCompactFirstPhaseRows i))
        (generatedRootEightIncomingCompactFourierQImage i
          (monsterMonomialDiagonalImage
            (generatedNinthLowerSpinCompactPhase
              (generatedRootEightIncomingCompactSecondPhaseRows i))
            (monsterMonomialPermutationImage (generatedRootEightIncomingCompactRight i) q)))) *
      (generatedRootEightIncomingCompactPauli i)⁻¹

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
theorem generatedRootEight_incoming_compact_conjugation (i : Fin 1) (q : Q) :
    spinConjugation (generatedRootEightIncomingCompactSpin i) q =
      generatedRootEightIncomingCompactQImage i q := by
  rw [generatedRootEightIncomingCompactSpin]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

/-- The full recorded target at each original positive Q coordinate. -/
def generatedRootEightIncomingCompactBasisImage (i : Fin 1) (j : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedRootEightIncomingCompactBinaryColumns i j)),
    ofAdd ((generatedRootEightIncomingCompactUnitPhases i j : ℕ) : ZMod 2)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
