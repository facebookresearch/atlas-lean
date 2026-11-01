/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactSpin
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
def generatedRootEightCompactFourierQImage (i : Fin 14) (q : Q) : Q :=
  (generatedRootEightCompactHadamardWord i).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The compact model's full original extraspecial image, including its Pauli correction. -/
def generatedRootEightCompactQImage (i : Fin 14) (q : Q) : Q :=
  generatedRootEightCompactPauli i *
    monsterMonomialPermutationImage (generatedRootEightCompactLeft i)
      (monsterMonomialDiagonalImage
        (generatedNinthLowerSpinCompactPhase (generatedRootEightCompactFirstPhaseRows i))
        (generatedRootEightCompactFourierQImage i
          (monsterMonomialDiagonalImage
            (generatedNinthLowerSpinCompactPhase
              (generatedRootEightCompactSecondPhaseRows i))
            (monsterMonomialPermutationImage (generatedRootEightCompactRight i) q)))) *
      (generatedRootEightCompactPauli i)⁻¹

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
theorem generatedRootEight_compact_conjugation (i : Fin 14) (q : Q) :
    spinConjugation (generatedRootEightCompactSpin i) q =
      generatedRootEightCompactQImage i q := by
  rw [generatedRootEightCompactSpin]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

/-- The full recorded target at each original positive Q coordinate. -/
def generatedRootEightCompactBasisImage (i : Fin 14) (j : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedRootEightCompactBinaryColumns i j)),
    ofAdd ((generatedRootEightCompactUnitPhases i j : ℕ) : ZMod 2)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
