/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100MathieuGenerators

/-! Two original Mathieu words and finite relations recovering every strong generator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original strong4 * strong8 * strong5 and original strong12, in the original group. -/
def generatedRootEightMathieuReducedGenerator (j : Fin 2) : golayAutomorphismSubgroup :=
  if j = 0 then leechNormSixHS100MathieuOriginalGenerator 0 *
    leechNormSixHS100MathieuOriginalGenerator 4 * leechNormSixHS100MathieuOriginalGenerator 1
  else leechNormSixHS100MathieuOriginalGenerator 8

/-- Literal original physical-permutation words, retaining product order. -/
def generatedRootEightMathieuReducedOriginalWords (j : Fin 2) : List (Fin 4) :=
  if j = 0 then leechNormSixHS100MathieuGeneratorWords 0 ++
    leechNormSixHS100MathieuGeneratorWords 4 ++ leechNormSixHS100MathieuGeneratorWords 1
  else leechNormSixHS100MathieuGeneratorWords 8

/-- Complete literal original physical coordinates of the reduced pair. -/
def generatedRootEightMathieuReducedForward : Fin 2 → Fin 24 → Fin 24 :=
  ![![0, 1, 10, 16, 21, 18, 11, 22, 13, 23, 4, 2, 17, 12, 8, 15, 19, 7, 9, 5, 6, 20, 14, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]]

/-- Complete literal original physical coordinates of the reduced pair. -/
def generatedRootEightMathieuReducedInverse : Fin 2 → Fin 24 → Fin 24 :=
  ![![0, 1, 11, 23, 10, 19, 20, 17, 14, 18, 2, 6, 13, 8, 22, 15, 3, 12, 5, 16, 21, 4, 7, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]]

/-- The two original elements followed by their genuine inverses. -/
def generatedRootEightMathieuReducedLetter (t : Fin 4) : golayAutomorphismSubgroup :=
  if h : t.val < 2 then generatedRootEightMathieuReducedGenerator ⟨t.val, h⟩
  else (generatedRootEightMathieuReducedGenerator ⟨t.val - 2, by omega⟩)⁻¹

/-- The same literal four-letter alphabet acting on every original physical coordinate. -/
def generatedRootEightMathieuReducedLetterArray (t : Fin 4) : Fin 24 → Fin 24 :=
  if h : t.val < 2 then generatedRootEightMathieuReducedForward ⟨t.val, h⟩
  else generatedRootEightMathieuReducedInverse ⟨t.val - 2, by omega⟩

/-- Actual product of the reduced original permutations and their inverses. -/
def generatedRootEightMathieuReducedWord (w : List (Fin 4)) : golayAutomorphismSubgroup :=
  (w.map generatedRootEightMathieuReducedLetter).prod

/-- Full coordinate action of a word in product order. -/
def generatedRootEightMathieuReducedWordArray (w : List (Fin 4)) (i : Fin 24) : Fin 24 :=
  w.foldr (fun t i => generatedRootEightMathieuReducedLetterArray t i) i

/-- Literal words recovering each of the ten original ordered-root strong generators. -/
def generatedRootEightMathieuReducedStrongWords : Fin 10 → List (Fin 4) :=
  ![[1, 2, 1, 2, 1, 0, 0, 0, 1, 0, 1, 2, 1, 2, 2, 2, 1, 0, 1, 0, 1],
    [1, 0, 0, 1, 0, 0, 1, 2, 1, 2, 2, 1, 0, 0, 1, 0, 0, 1],
    [2, 1, 0, 1, 0, 0, 1, 2, 1, 0, 1, 2, 2, 1, 2, 1, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 1, 2, 2],
    [1, 0, 1, 0, 0, 1, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 2, 2],
    [2, 1, 0, 0, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 0, 1, 0, 0],
    [0, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 0, 1, 0, 0],
    [1],
    [2, 2, 2, 1, 2, 2, 2, 1, 0, 0, 1, 2, 2, 1, 2]]

set_option maxHeartbeats 4000000 in
-- Check both complete original coordinate arrays without expanding the source physical words.
/-- The reduced forward arrays are their exact products of original strong arrays. -/
theorem generatedRootEight_mathieu_reduced_forward_certificate : ∀ i : Fin 24,
    leechNormSixHS100MathieuGeneratorForward 0
      (leechNormSixHS100MathieuGeneratorForward 4
        (leechNormSixHS100MathieuGeneratorForward 1 i)) =
        generatedRootEightMathieuReducedForward 0 i ∧
    leechNormSixHS100MathieuGeneratorForward 8 i =
      generatedRootEightMathieuReducedForward 1 i := by
  decide +kernel

/-- Every reduced inverse array is the full original inverse permutation. -/
theorem generatedRootEight_mathieu_reduced_inverse_certificate : ∀ j : Fin 2, ∀ i : Fin 24,
    generatedRootEightMathieuReducedForward j (generatedRootEightMathieuReducedInverse j i) = i := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check all twenty-four actual physical coordinates of all ten strong relations.
/-- The two-source words recover the entire original strong-generator action. -/
theorem generatedRootEight_mathieu_reduced_strong_certificate : ∀ j : Fin 10, ∀ i : Fin 24,
    generatedRootEightMathieuReducedWordArray (generatedRootEightMathieuReducedStrongWords j) i =
      leechNormSixHS100MathieuGeneratorForward j i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
