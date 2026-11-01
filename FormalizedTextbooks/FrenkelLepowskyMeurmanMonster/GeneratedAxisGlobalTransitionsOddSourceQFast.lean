/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddLetterQCache09

/-! Compact full-phase evaluation of the ten actual signed source letters and nine root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All original signed letter coordinate images are checked, retaining their actual phases. -/
theorem generatedAxisGlobalOddLetterQCache_certificate (l : Fin 10) (i : Fin 24) :
    generatedAxisGlobalOddSourceLetterQImage l (qCoordinateGenerator i) =
      generatedAxisGlobalOddLetterQCache l i := by
  fin_cases l
  · exact generatedAxisGlobalOddLetterQCache00_certificate i
  · exact generatedAxisGlobalOddLetterQCache01_certificate i
  · exact generatedAxisGlobalOddLetterQCache02_certificate i
  · exact generatedAxisGlobalOddLetterQCache03_certificate i
  · exact generatedAxisGlobalOddLetterQCache04_certificate i
  · exact generatedAxisGlobalOddLetterQCache05_certificate i
  · exact generatedAxisGlobalOddLetterQCache06_certificate i
  · exact generatedAxisGlobalOddLetterQCache07_certificate i
  · exact generatedAxisGlobalOddLetterQCache08_certificate i
  · exact generatedAxisGlobalOddLetterQCache09_certificate i

/-- A compact finite evaluator retains every original source central correction. -/
def generatedAxisGlobalOddSourceFastLetter (l : Fin 10) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedAxisGlobalOddLetterQCache l) q

/-- The compact evaluator is actual complete source conjugation for every extraspecial input. -/
theorem generatedAxisGlobalOddSourceFastLetter_actual (l : Fin 10) (q : Q) :
    spinConjugation (generatedAxisGlobalOddSourceFiberLetter l).val.1 q =
      generatedAxisGlobalOddSourceFastLetter l q := by
  apply monsterNortonCoordinateEvaluation_eq
  intro i
  rw [generatedAxisGlobalOddSourceLetter_QImage]
  exact generatedAxisGlobalOddLetterQCache_certificate l i

/-- Compact suffix-first evaluation of an entire phase-preserving original word. -/
def generatedAxisGlobalOddSourceFastWord : List (Fin 10) → Q → Q
  | [], q => q
  | l :: ls, q => generatedAxisGlobalOddSourceFastLetter l
      (generatedAxisGlobalOddSourceFastWord ls q)

/-- All original complete word actions are compact finite evaluations on the genuine Q model. -/
theorem generatedAxisGlobalOddSourceFastWord_actual (ls : List (Fin 10)) (q : Q) :
    spinConjugation (((ls.map generatedAxisGlobalOddSourceFiberLetter).prod).val.1) q =
      generatedAxisGlobalOddSourceFastWord ls q := by
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
    rw [ih, generatedAxisGlobalOddSourceFastLetter_actual]
    rfl

/-- All nine original source root products have these complete compact actual Q actions. -/
theorem generatedAxisGlobalOddSourceFastRoot_actual (k : Fin 9) (q : Q) :
    spinConjugation (generatedAxisGlobalOddSourceRootFiber k).val.1 q =
      generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k) q :=
  generatedAxisGlobalOddSourceFastWord_actual _ q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
