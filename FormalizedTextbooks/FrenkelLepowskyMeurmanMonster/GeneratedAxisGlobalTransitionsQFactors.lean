/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQImage

/-! Literal individual source factors expose small exact preferred-coordinate checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Individual original phase-preserving local source factors. -/
inductive GeneratedAxisGlobalQFactor where
  | monomial (letter : Fin 2 × Bool)
  | sign (label : Fin 4096)
  | xi

/-- The genuine actual fiber element of each individual source factor. -/
def generatedAxisGlobalQFactorFiber : GeneratedAxisGlobalQFactor → localFiberSubgroup
  | .monomial l => generatedFourthMonomialFiberLetter l
  | .sign a => generatedFifthSignFiber a 0
  | .xi => xiSpinLocalFiber

/-- Its complete explicit extraspecial image retains the original central correction. -/
def generatedAxisGlobalQFactorImage : GeneratedAxisGlobalQFactor → Q → Q
  | .monomial l => generatedAxisGlobalMonomialLetterQImage l
  | .sign a => generatedAxisGlobalSignFullImage a
  | .xi => fun q => xiSpinGImage (xiSpinGammaImage q)

/-- Every individual executable source image equals the genuine actual fiber conjugation. -/
theorem generatedAxisGlobalQFactor_actual (l : GeneratedAxisGlobalQFactor) (q : Q) :
    spinConjugation (generatedAxisGlobalQFactorFiber l).val.1 q =
      generatedAxisGlobalQFactorImage l q := by
  cases l with
  | monomial l => exact generatedAxisGlobalMonomialLetter_QImage l q
  | sign a => exact generatedAxisGlobalSignFull_QImage a q
  | xi => exact xiSpinHolomorph_conjugation q

/-- Chronological source lists multiply each later factor on the left. -/
def generatedAxisGlobalQFactorWord (w : List GeneratedAxisGlobalQFactor) : localFiberSubgroup :=
  (w.map generatedAxisGlobalQFactorFiber).reverse.prod

/-- Chronological preferred-Q transport applies the first factor before its remaining suffix. -/
def generatedAxisGlobalQFactorRun : List GeneratedAxisGlobalQFactor → Q → Q
  | [], q => q
  | l :: w, q => generatedAxisGlobalQFactorRun w (generatedAxisGlobalQFactorImage l q)

/-- Appending a chronological list multiplies its actual word on the left. -/
theorem generatedAxisGlobalQFactorWord_append (w v : List GeneratedAxisGlobalQFactor) :
    generatedAxisGlobalQFactorWord (w ++ v) =
      generatedAxisGlobalQFactorWord v * generatedAxisGlobalQFactorWord w := by
  simp only [generatedAxisGlobalQFactorWord, List.map_append, List.reverse_append,
    List.prod_append]

/-- Every chronological source run is complete genuine extraspecial conjugation. -/
theorem generatedAxisGlobalQFactorRun_actual (w : List GeneratedAxisGlobalQFactor) (q : Q) :
    spinConjugation (generatedAxisGlobalQFactorWord w).val.1 q =
      generatedAxisGlobalQFactorRun w q := by
  induction w generalizing q with
  | nil =>
    change spinConjugation 1 q = q
    rw [map_one]
    rfl
  | cons l w ih =>
    have hw : generatedAxisGlobalQFactorWord (l :: w) =
        generatedAxisGlobalQFactorWord w * generatedAxisGlobalQFactorFiber l := by
      simp only [generatedAxisGlobalQFactorWord, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [hw]
    change spinConjugation
      ((generatedAxisGlobalQFactorWord w).val.1 * (generatedAxisGlobalQFactorFiber l).val.1) q = _
    rw [map_mul]
    change spinConjugation (generatedAxisGlobalQFactorWord w).val.1
      (spinConjugation (generatedAxisGlobalQFactorFiber l).val.1 q) = _
    rw [generatedAxisGlobalQFactor_actual, ih]
    rfl

/-- Small complete factor-state certificates determine the entire chronological Q run. -/
theorem generatedAxisGlobalQFactorRun_states (w : List GeneratedAxisGlobalQFactor)
    (u : ℕ → Q)
    (hs : ∀ j (hj : j < w.length),
      generatedAxisGlobalQFactorImage w[j] (u j) = u (j + 1)) :
    generatedAxisGlobalQFactorRun w (u 0) = u w.length := by
  induction w generalizing u with
  | nil => rfl
  | cons l w ih =>
    change generatedAxisGlobalQFactorRun w
      (generatedAxisGlobalQFactorImage l (u 0)) = u (w.length + 1)
    have h0 := hs 0 (by simp only [List.length_cons]; omega)
    change generatedAxisGlobalQFactorImage l (u 0) = u 1 at h0
    rw [h0]
    apply ih (fun j => u (j + 1))
    intro j hj
    have h := hs (j + 1) (by simp only [List.length_cons]; omega)
    simpa only [List.getElem_cons_succ, Nat.add_assoc] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
