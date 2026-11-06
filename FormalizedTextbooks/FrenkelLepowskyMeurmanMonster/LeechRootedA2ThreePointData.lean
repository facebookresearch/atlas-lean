/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2ThreePointGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsLeech

/-! Bounded original-code and word certificates for three actual three-point generators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The three already bound complete permutation fibers used as genuine generators. -/
def leechRootedA2ThreePointRepresentative : Fin 3 → Fin 83 := ![0, 1, 3]

/-- The actual left coordinate permutation of each original full fiber. -/
def leechRootedA2ThreePointPermutation (j : Fin 3) : Equiv.Perm (Fin 24) :=
  (representativePermutationPhysicalPermutation (leechRootedA2ThreePointRepresentative j))⁻¹

/-- Actual code labels of the twelve basis images under each genuine permutation. -/
def leechRootedA2ThreePointCodeImages : Fin 3 → Fin 12 → Fin 4096 :=
  ![![1806, 1815, 1835, 1853, 48, 32, 96, 240, 1551, 1295, 1024, 2048],
  ![1806, 1861, 1929, 1987, 192, 129, 218, 60, 1611, 1415, 1217, 2048],
  ![15, 1835, 1806, 1815, 1905, 2008, 26, 19, 1590, 1286, 907, 2048]]

/-- Actual code labels of the twelve basis images under each genuine inverse permutation. -/
def leechRootedA2ThreePointCodeInverse : Fin 3 → Fin 12 → Fin 4096 :=
  ![![1806, 1815, 1835, 1853, 48, 32, 96, 240, 1551, 1295, 1024, 2048],
  ![15, 1806, 1835, 1853, 99, 245, 63, 47, 1562, 1308, 1055, 2048],
  ![1968, 2044, 1853, 1904, 204, 139, 82, 123, 1587, 1396, 1266, 2048]]

/-- Each original physical basis-code image equals the supplied original encoder output. -/
theorem leechRootedA2ThreePoint_code_certificate : ∀ j : Fin 3, ∀ k : Fin 12,
    golayPermute (leechRootedA2ThreePointPermutation j)
      (fun i => (golayGeneratorBit k i : ZMod 2)) =
        golayEncoder (golayLabelCoefficients (leechRootedA2ThreePointCodeImages j k)) ∧
    golayPermute (leechRootedA2ThreePointPermutation j).symm
      (fun i => (golayGeneratorBit k i : ZMod 2)) =
        golayEncoder (golayLabelCoefficients (leechRootedA2ThreePointCodeInverse j k)) := by
  decide +kernel

/-- Six physical letters are the three actual permutations followed by their inverses. -/
def leechRootedA2ThreePointLetterArray (t : Fin 6) : Fin 24 → Fin 24 :=
  if h : t.val < 3 then leechRootedA2ThreePointPermutation ⟨t.val, h⟩
  else (leechRootedA2ThreePointPermutation ⟨t.val - 3, by omega⟩).symm

/-- Actual composition of the three-generator word arrays. -/
def leechRootedA2ThreePointWordArray (w : List (Fin 6)) (i : Fin 24) : Fin 24 :=
  w.foldr (fun t i => leechRootedA2ThreePointLetterArray t i) i

/-- Nine bounded source words expressing the original strong generators. -/
def leechRootedA2ThreePointStrongWords : Fin 9 → List (Fin 6) :=
  ![[5, 4, 0, 1, 2],
  [1, 0, 5, 5, 4, 2, 0, 2],
  [2, 2, 1, 1, 2, 1, 0, 2],
  [0, 4, 5, 0, 1, 2, 4, 0],
  [4, 2, 4, 4, 5, 1, 1],
  [1, 0, 2, 2, 2, 0, 1, 1, 0],
  [0, 5, 5, 0, 5, 4, 4, 0],
  [2, 2, 1, 0, 5, 5, 4, 2],
  [1, 5, 5, 1, 0, 5, 1]]

/-- Every bounded word equals its original physical strong-generator array. -/
theorem leechRootedA2ThreePoint_word_certificate : ∀ j : Fin 9, ∀ i : Fin 24,
    leechRootedA2ThreePointWordArray (leechRootedA2ThreePointStrongWords j) i =
      golayStrongForward (leechRootedA2ThreePointStrongIndex j) i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
