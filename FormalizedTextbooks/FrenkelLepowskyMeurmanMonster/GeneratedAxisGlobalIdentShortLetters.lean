/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceQFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignFullImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialWords

/-! # Extraspecial mask data of the identification letters

Valid mask data (`GeneratedAxisGlobalIdentShortMask`) for the letter kinds of the cheap
identification method: the ten odd source letters (Xi, the two source signs and the two monomial
permutations, with inverses), arbitrary source signs `generatedFifthSignFiber a 0` (data checked
against the exact evaluator `generatedAxisGlobalSignFullImage`), and extraspecial letters.  Words
are given with literal data per letter and one boolean check certifies every letter. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Multiplicative

/-! ## The ten odd source letters -/

/-- Correction rows of the binary columns of the ten odd source letters. -/
def sourceLetterRows : Fin 10 → Fin 24 → ℕ :=
  ![![4096, 8192, 16384, 32768, 0, 0, 0, 0, 0, 0, 4194304, 8388608, 57344, 49152, 32768, 0,
      0, 0, 0, 0, 0, 0, 8388608, 0],
    ![4110, 8204, 16392, 32768, 0, 0, 0, 0, 0, 0, 4196352, 8388608, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    ![32, 672, 480, 864, 0, 0, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0,
      0],
    ![32, 672, 480, 864, 0, 0, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0,
      0],
    ![16, 336, 912, 720, 0, 0, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0,
      0],
    ![16, 336, 912, 720, 0, 0, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0,
      0],
    ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0],
    ![1038, 12, 1032, 1024, 864, 896, 896, 768, 1536, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Central coefficients of the ten odd source letters. -/
def sourceLetterCoeff : Fin 10 → ℕ :=
  ![4255744, 2048, 15, 15, 15, 15, 0, 250, 0, 515]

/-- Mask data of an odd source letter, from its checked coordinate image cache. -/
def sourceLetterData (l : Fin 10) : QMaskData :=
  ⟨generatedAxisGlobalOddLetterQCacheBinary l, sourceLetterRows l, sourceLetterCoeff l⟩

set_option maxRecDepth 100000 in
/-- The literal rows are the computed correction rows. -/
theorem sourceLetterRows_eq : ∀ l : Fin 10, ∀ i : Fin 24,
    sourceLetterRows l i = rowsOf (generatedAxisGlobalOddLetterQCacheBinary l) i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The literal coefficients carry the cached central phases. -/
theorem sourceLetterCoeff_bits : ∀ l : Fin 10, ∀ i : Fin 24,
    golayBooleanCast ((sourceLetterCoeff l).testBit i.val) =
      generatedAxisGlobalOddLetterQCachePhase l i := by
  decide +kernel

/-- The odd source letter data are valid. -/
theorem sourceLetterData_valid (l : Fin 10) :
    (sourceLetterData l).Valid
      (spinConjugation (generatedAxisGlobalOddSourceFiberLetter l).val.1) := by
  apply QMaskData.valid_of_generators _ _ _ (sourceLetterRows_eq l)
  intro i
  rw [generatedAxisGlobalOddSourceLetter_QImage, generatedAxisGlobalOddLetterQCache_certificate]
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [qmElt_base]
    rfl
  · apply toAdd.injective
    rw [qmElt_coeff]
    exact (sourceLetterCoeff_bits l i).symm

/-- Xi is odd source letter `0`. -/
theorem sourceLetter_xi : generatedAxisGlobalOddSourceFiberLetter 0 = xiSpinLocalFiber := rfl

/-- The odd source letter of a monomial letter. -/
def monoLetterIndex (l : Fin 2 × Bool) : Fin 10 :=
  ⟨6 + 2 * l.1.val + (if l.2 then 1 else 0), by
    have := l.1.isLt
    split_ifs <;> omega⟩

/-- Monomial letters are odd source letters `6, 7, 8, 9`. -/
theorem sourceLetter_mono (l : Fin 2 × Bool) :
    generatedAxisGlobalOddSourceFiberLetter (monoLetterIndex l) =
      generatedFourthMonomialFiberLetter l := by
  obtain ⟨a, b⟩ := l
  fin_cases a <;> cases b <;> rfl

/-- Xi has the data of odd source letter `0`. -/
theorem xiLetterData_valid :
    (sourceLetterData 0).Valid (spinConjugation xiSpinLocalFiber.val.1) :=
  sourceLetterData_valid 0

/-- Monomial letters have the data of their odd source letters. -/
theorem monoLetterData_valid (l : Fin 2 × Bool) :
    (sourceLetterData (monoLetterIndex l)).Valid
      (spinConjugation (generatedFourthMonomialFiberLetter l).val.1) := by
  rw [← sourceLetter_mono]
  exact sourceLetterData_valid _

/-! ## Source signs -/

/-- Literal data of a source sign agree with its exact evaluator on the generators. -/
def signLetterCheck (a : Fin 4096) (d : QMaskData) : Bool :=
  (List.finRange 24).all (fun i =>
    qmEncode (generatedAxisGlobalSignFullImage a (qCoordinateGenerator i)) ==
      (d.cols i, d.coeff.testBit i.val)) &&
  (List.finRange 24).all (fun i => d.rows i == rowsOf d.cols i)

/-- Checked literal data of a source sign are valid. -/
theorem signLetterCheck_sound (a : Fin 4096) (d : QMaskData) (h : signLetterCheck a d = true) :
    d.Valid (spinConjugation (generatedFifthSignFiber a 0).val.1) := by
  simp only [signLetterCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, beq_iff_eq] at h
  exact QMaskData.valid_of_images _ _ (generatedAxisGlobalSignFull_QImage a) d h.1 h.2

/-! ## Extraspecial letters -/

set_option maxRecDepth 100000 in
/-- The correction rows of the identity columns vanish. -/
theorem rowsOf_units : ∀ i : Fin 24, (0 : ℕ) = rowsOf (fun i => 2 ^ i.val) i := by
  decide +kernel

/-- Mask data of conjugation by an extraspecial element, from its mask (zero rows). -/
def qLetterDataZ (m : ℕ) : QMaskData :=
  ⟨fun i => 2 ^ i.val, fun _ => 0, maskOfBits (qLetterBits m)⟩

/-- Conjugation by any extraspecial element has the data of its mask. -/
theorem qLetterDataZ_valid (q : Q) :
    (qLetterDataZ (qmEncode q).1).Valid (spinConjugation (localFiberIncl q).val.1) := by
  have h := qLetterData_valid (qmEncode q).1 (qmEncode q).2
  rw [qmElt_encode] at h
  intro v
  rw [h v]
  have hr : (qLetterData (qmEncode q).1).rows = (qLetterDataZ (qmEncode q).1).rows := by
    funext i
    exact (rowsOf_units i).symm
  simp only [qLetterData, qLetterDataZ] at hr ⊢
  rw [hr]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
