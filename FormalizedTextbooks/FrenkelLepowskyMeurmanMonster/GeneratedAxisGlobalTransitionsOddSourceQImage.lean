/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFullImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMonomialQImage

/-! Executable complete extraspecial actions of the signed original odd-family root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem oddSource_hadamard_inv :
    monsterSpinHadamardHolomorph⁻¹ = monsterSpinHadamardHolomorph := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  exact monsterSpinHadamardEquiv_square

private theorem oddSource_diagonal_inv (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalHolomorph M)⁻¹ = monsterMonomialDiagonalHolomorph M := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply LinearEquiv.ext
  exact monsterMonomialDiagonal_involutive M

private theorem oddSource_permutation_inv (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (monsterMonomialPermutationHolomorph P)⁻¹ = monsterMonomialPermutationHolomorph P.symm := by
  apply Subtype.ext
  exact (monsterMonomialPermutation_symm P).symm

private theorem oddSource_inverse_of_cube {A : Type*} [Group A] (a : A) (ha : a ^ 3 = 1) :
    a⁻¹ = a * a := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ha

/-- Reverse all genuine Fourier, shear and quadratic factors of a low source sign. -/
def generatedAxisGlobalOddSourceSignInverseImage (a : Fin 2048) (q : Q) : Q :=
  monsterSpinHadamardImage
    (monsterMonomialPermutationImage (monsterNortonYShear a).symm
      (monsterMonomialDiagonalImage (generatedAxisGlobalSignPhaseMatrix a)
        (monsterSpinHadamardImage q)))

/-- The reversed finite formula is exactly the genuine inverse source-sign Q action. -/
theorem generatedAxisGlobalOddSourceSignInverse_QImage (a : Fin 2048) (q : Q) :
    spinConjugation
      ((generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0).val.1)⁻¹ q =
      generatedAxisGlobalOddSourceSignInverseImage a q := by
  have he : spinConjugation
      (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0).val.1 =
        spinConjugation (generatedAxisGlobalSignSpin a) := by
    ext r
    rw [generatedAxisGlobalSignLow_QImage, generatedAxisGlobalSignSpin_conjugation]
  rw [map_inv, he, ← map_inv]
  rw [generatedAxisGlobalSignSpin, generatedAxisGlobalSignPlusMinus,
    mul_inv_rev, mul_inv_rev, mul_inv_rev, oddSource_hadamard_inv,
    oddSource_diagonal_inv, oddSource_permutation_inv, map_mul, map_mul, map_mul]
  change spinConjugation monsterSpinHadamardHolomorph
    (spinConjugation (monsterMonomialPermutationHolomorph (monsterNortonYShear a).symm)
      (spinConjugation (monsterMonomialDiagonalHolomorph (generatedAxisGlobalSignPhaseMatrix a))
        (spinConjugation monsterSpinHadamardHolomorph q))) = _
  rw [monsterSpinHadamardHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation,
    monsterSpinHadamardHolomorph_conjugation]
  rfl

/-- Complete positive source images with the original central corrections. -/
def generatedAxisGlobalOddSourceBaseQImage (k : Fin 5) (q : Q) : Q :=
  ![xiSpinGImage (xiSpinGammaImage q), generatedAxisGlobalSignFullImage 16 q,
    generatedAxisGlobalSignFullImage 32 q, monsterSourcePermutationImage 0 q,
    monsterSourcePermutationImage 1 q] k

/-- Each positive finite source formula agrees with actual fiber conjugation. -/
theorem generatedAxisGlobalOddSourceBase_QImage (k : Fin 5) (q : Q) :
    spinConjugation (generatedAxisGlobalOddSourceBaseFiber k).val.1 q =
      generatedAxisGlobalOddSourceBaseQImage k q := by
  fin_cases k
  · exact xiSpinHolomorph_conjugation q
  · exact generatedAxisGlobalSignFull_QImage 16 q
  · exact generatedAxisGlobalSignFull_QImage 32 q
  · exact monsterSourcePermutationSpin_conjugation 0 q
  · exact monsterSourcePermutationSpin_conjugation 1 q

/-- Genuine inverse images; Xi uses its proved cube, while permutation phases are reversed. -/
def generatedAxisGlobalOddSourceInverseQImage (k : Fin 5) (q : Q) : Q :=
  ![xiSpinGImage (xiSpinGammaImage (xiSpinGImage (xiSpinGammaImage q))),
    generatedAxisGlobalOddSourceSignInverseImage 16 q,
    generatedAxisGlobalOddSourceSignInverseImage 32 q,
    generatedAxisGlobalMonomialInverseQImage 0 q,
    generatedAxisGlobalMonomialInverseQImage 1 q] k

/-- Every displayed inverse is actual conjugation by the complete inverse source fiber. -/
theorem generatedAxisGlobalOddSourceInverse_QImage (k : Fin 5) (q : Q) :
    spinConjugation ((generatedAxisGlobalOddSourceBaseFiber k).val.1)⁻¹ q =
      generatedAxisGlobalOddSourceInverseQImage k q := by
  fin_cases k
  · have hi : xiSpinHolomorph⁻¹ = xiSpinHolomorph * xiSpinHolomorph :=
      oddSource_inverse_of_cube _ xiSpinHolomorph_cube
    change spinConjugation xiSpinHolomorph⁻¹ q = _
    rw [hi, map_mul]
    change spinConjugation xiSpinHolomorph (spinConjugation xiSpinHolomorph q) = _
    rw [xiSpinHolomorph_conjugation, xiSpinHolomorph_conjugation]
    rfl
  · exact generatedAxisGlobalOddSourceSignInverse_QImage 16 q
  · exact generatedAxisGlobalOddSourceSignInverse_QImage 32 q
  · exact generatedAxisGlobalMonomialInverse_QImage 0 q
  · exact generatedAxisGlobalMonomialInverse_QImage 1 q

/-- The finite action of a signed letter retains its actual inverse central phase. -/
def generatedAxisGlobalOddSourceLetterQImage (l : Fin 10) (q : Q) : Q :=
  let k : Fin 5 := ⟨l.val / 2, by omega⟩
  if l.val % 2 = 1 then generatedAxisGlobalOddSourceInverseQImage k q
  else generatedAxisGlobalOddSourceBaseQImage k q

/-- Complete signed source fibers act by their displayed executable extraspecial formula. -/
theorem generatedAxisGlobalOddSourceLetter_QImage (l : Fin 10) (q : Q) :
    spinConjugation (generatedAxisGlobalOddSourceFiberLetter l).val.1 q =
      generatedAxisGlobalOddSourceLetterQImage l q := by
  by_cases h : l.val % 2 = 1
  · simp only [generatedAxisGlobalOddSourceFiberLetter, generatedAxisGlobalOddSourceLetterQImage,
      h, ↓reduceIte]
    exact generatedAxisGlobalOddSourceInverse_QImage _ q
  · simp only [generatedAxisGlobalOddSourceFiberLetter, generatedAxisGlobalOddSourceLetterQImage,
      h, ↓reduceIte]
    exact generatedAxisGlobalOddSourceBase_QImage _ q

/-- An entire source product applies each letter after its remaining suffix. -/
def generatedAxisGlobalOddSourceWordQImage : List (Fin 10) → Q → Q
  | [], q => q
  | l :: ls, q => generatedAxisGlobalOddSourceLetterQImage l
      (generatedAxisGlobalOddSourceWordQImage ls q)

/-- Every complete original word has precisely this all-Q action, including central phases. -/
theorem generatedAxisGlobalOddSourceWord_QImage (ls : List (Fin 10)) (q : Q) :
    spinConjugation (((ls.map generatedAxisGlobalOddSourceFiberLetter).prod).val.1) q =
      generatedAxisGlobalOddSourceWordQImage ls q := by
  induction ls with
  | nil =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | cons l ls ih =>
    change spinConjugation ((generatedAxisGlobalOddSourceFiberLetter l).val.1 *
      ((ls.map generatedAxisGlobalOddSourceFiberLetter).prod).val.1) q = _
    rw [map_mul]
    change spinConjugation (generatedAxisGlobalOddSourceFiberLetter l).val.1
      (spinConjugation (((ls.map generatedAxisGlobalOddSourceFiberLetter).prod).val.1) q) = _
    rw [ih, generatedAxisGlobalOddSourceLetter_QImage]
    rfl

/-- All nine genuine root words have complete executable extraspecial actions. -/
theorem generatedAxisGlobalOddSourceRoot_QImage (k : Fin 9) (q : Q) :
    spinConjugation (generatedAxisGlobalOddSourceRootFiber k).val.1 q =
      generatedAxisGlobalOddSourceWordQImage (generatedAxisGlobalOddSourceRootWords k) q :=
  generatedAxisGlobalOddSourceWord_QImage _ q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
