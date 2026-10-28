/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords

/-! Full phase-correct extraspecial images of literal signed original permutation words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem diagonal_inv (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalHolomorph M)⁻¹ = monsterMonomialDiagonalHolomorph M := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply LinearEquiv.ext
  exact monsterMonomialDiagonal_involutive M

private theorem permutation_inv (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (monsterMonomialPermutationHolomorph P)⁻¹ = monsterMonomialPermutationHolomorph P.symm := by
  apply Subtype.ext
  exact (monsterMonomialPermutation_symm P).symm

/-- The inverse original lift reverses the real factors and retains the full quadratic phase. -/
def generatedAxisGlobalMonomialInverseQImage (k : Fin 2) (q : Q) : Q :=
  monsterMonomialDiagonalImage (monsterSourcePermutationPhaseData k)
    (monsterMonomialPermutationImage (monsterSourcePermutationCode k).symm q)

/-- The explicit inverse formula is exactly conjugation by the genuine inverse spin lift. -/
theorem generatedAxisGlobalMonomialInverse_QImage (k : Fin 2) (q : Q) :
    spinConjugation (monsterSourcePermutationSpin k)⁻¹ q =
      generatedAxisGlobalMonomialInverseQImage k q := by
  rw [monsterSourcePermutationSpin, mul_inv_rev, diagonal_inv, permutation_inv, map_mul]
  change spinConjugation (monsterMonomialDiagonalHolomorph (monsterSourcePermutationPhaseData k))
    (spinConjugation (monsterMonomialPermutationHolomorph
      (monsterSourcePermutationCode k).symm) q) = _
  rw [monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation]
  rfl

/-- Every literal letter has its original phase-correct forward or inverse Q image. -/
def generatedAxisGlobalMonomialLetterQImage (l : Fin 2 × Bool) (q : Q) : Q :=
  if l.2 then generatedAxisGlobalMonomialInverseQImage l.1 q
  else monsterSourcePermutationImage l.1 q

/-- The literal fiber letter conjugates Q by the displayed executable formula. -/
theorem generatedAxisGlobalMonomialLetter_QImage (l : Fin 2 × Bool) (q : Q) :
    spinConjugation (generatedFourthMonomialFiberLetter l).val.1 q =
      generatedAxisGlobalMonomialLetterQImage l q := by
  rcases l with ⟨k, b⟩
  cases b with
  | false => exact monsterSourcePermutationSpin_conjugation k q
  | true => exact generatedAxisGlobalMonomialInverse_QImage k q

/-- A full literal word applies the first letter after the image of its remaining suffix. -/
def generatedAxisGlobalMonomialWordQImage : List (Fin 2 × Bool) → Q → Q
  | [], q => q
  | l :: w, q => generatedAxisGlobalMonomialLetterQImage l
      (generatedAxisGlobalMonomialWordQImage w q)

/-- Every literal signed source word has its complete actual Q action with all central phases. -/
theorem generatedAxisGlobalMonomialWord_QImage (w : List (Fin 2 × Bool)) (q : Q) :
    spinConjugation (((w.map generatedFourthMonomialFiberLetter).prod).val.1) q =
      generatedAxisGlobalMonomialWordQImage w q := by
  induction w with
  | nil =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | cons l w ih =>
    change spinConjugation
      ((generatedFourthMonomialFiberLetter l).val.1 *
        ((w.map generatedFourthMonomialFiberLetter).prod).val.1) q = _
    rw [map_mul]
    change spinConjugation (generatedFourthMonomialFiberLetter l).val.1
      (spinConjugation (((w.map generatedFourthMonomialFiberLetter).prod).val.1) q) = _
    rw [ih, generatedAxisGlobalMonomialLetter_QImage]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
