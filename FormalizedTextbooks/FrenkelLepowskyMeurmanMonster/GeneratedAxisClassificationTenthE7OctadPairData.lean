/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OctadPermutationGroup
public import Mathlib.Data.Fintype.Powerset

/-! Genuine original Golay words attaining every unordered pair in the standard octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- The first original coordinate of every complete standard-octad pair address. -/
def generatedTenthE7OctadPairLeft : Fin 28 → Fin 8 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 6]

/-- The second original coordinate of every complete standard-octad pair address. -/
def generatedTenthE7OctadPairRight : Fin 28 → Fin 8 :=
  ![1, 2, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 7, 3, 4, 5, 6, 7, 4, 5, 6, 7, 5, 6, 7, 6, 7, 7]

/-- Every actual unordered pair of coordinates in the entire standard octad. -/
abbrev generatedTenthE7OctadPairs := {s : Finset (Fin 8) // s.card = 2}

/-- Original pair source data, retaining both coordinates at all twenty-eight addresses. -/
def generatedTenthE7OctadPairData (i : Fin 28) : Finset (Fin 8) :=
  {generatedTenthE7OctadPairLeft i, generatedTenthE7OctadPairRight i}

/-- All original pair sources have exactly two distinct actual coordinates. -/
theorem generatedTenth_e7_octad_pair_data_card : ∀ i : Fin 28,
    (generatedTenthE7OctadPairData i).card = 2 := by
  decide +kernel

/-- All original pair sources are distinct. -/
theorem generatedTenth_e7_octad_pair_data_injective :
    Function.Injective generatedTenthE7OctadPairData := by
  decide +kernel

/-- The entire actual pair universe has precisely twenty-eight members. -/
theorem generatedTenth_e7_octad_pairs_card : Nat.card generatedTenthE7OctadPairs = 28 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_finset_len]
  norm_num
  decide +kernel

/-- The genuine original source word at each pair address. -/
def generatedTenthE7OctadPairWords : Fin 28 → Fin 5 → Fin 129 :=
  ![
    ![0, 0, 0, 0, 0],
    ![0, 25, 0, 86, 0],
    ![0, 26, 61, 82, 92],
    ![0, 27, 49, 86, 102],
    ![0, 28, 49, 86, 103],
    ![0, 29, 48, 73, 104],
    ![0, 30, 64, 70, 95],
    ![1, 27, 53, 71, 102],
    ![1, 32, 50, 80, 103],
    ![1, 31, 48, 71, 97],
    ![1, 40, 53, 79, 95],
    ![1, 30, 54, 83, 102],
    ![1, 39, 57, 0, 108],
    ![2, 0, 58, 83, 91],
    ![2, 46, 0, 76, 99],
    ![2, 38, 64, 80, 105],
    ![2, 34, 67, 77, 98],
    ![2, 31, 64, 74, 100],
    ![3, 42, 65, 82, 105],
    ![3, 31, 49, 82, 108],
    ![3, 27, 61, 76, 95],
    ![3, 35, 53, 88, 94],
    ![4, 38, 65, 83, 0],
    ![4, 0, 65, 84, 99],
    ![4, 37, 67, 84, 100],
    ![5, 0, 65, 84, 99],
    ![5, 38, 65, 83, 0],
    ![6, 37, 59, 70, 108]
  ]

/-- Every pair word is a product of genuine original certified Golay automorphisms. -/
def generatedTenthE7OctadPairWord (i : Fin 28) : golayAutomorphismSubgroup :=
  (List.finRange 5).foldl (fun p k => p *
    golayStabilizerAutomorphism (generatedTenthE7OctadPairWords i k)) 1

/-- Each full original word preserves all twenty-four support memberships and attains its pair. -/
theorem generatedTenth_e7_octad_pair_word_actual : ∀ r : Fin 28,
    (∀ i : Fin 24, ((generatedTenthE7OctadPairWord r).val i).val < 8 ↔ i.val < 8) ∧
      ((generatedTenthE7OctadPairWord r).val 0 = Fin.castAdd 16 (generatedTenthE7OctadPairLeft r)) ∧
      ((generatedTenthE7OctadPairWord r).val 1 =
        Fin.castAdd 16 (generatedTenthE7OctadPairRight r)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
