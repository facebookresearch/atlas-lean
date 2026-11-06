/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroProjectionNormalization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOutsidePairOctadOrbitProof
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSelectedOctadCodesData

/-! Original source-section and first-coordinate-fixing support transport certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- These arrays evaluate two genuine original Mathieu words. -/
def generatedFeasibleContainingZeroSupportLetterArray : Fin 2 → Fin 24 → Fin 24 :=
  ![golayStrongWordArray [19, 20, 27, 25, 5, 9, 4], golayStrongLetterArray 11]

/-- All unordered supports external to the actual source octad. -/
def generatedFeasibleContainingZeroPairs : Finset (Fin 24 × Fin 24) :=
  Finset.univ.filter fun p => p.1.val < p.2.val ∧ 8 ≤ p.1.val ∧ 8 ≤ p.2.val

/-- Actual support tree data in earlier-parent order. -/
def generatedFeasibleContainingZeroPairNode : Fin 120 → Fin 24 × Fin 24 :=
  ![(8, 9), (18, 20), (21, 22), (15, 22), (8, 17), (8, 16), (16, 18), (8, 13), (15, 16), (18, 23), (10, 21), (17, 18), (9, 21), (15, 17), (18, 19), (14, 21), (13, 17), (9, 15), (14, 15), (8, 19), (12, 16), (15, 23), (8, 10), (16, 20), (18, 22), (13, 23), (10, 15), (8, 11), (11, 16), (12, 18), (19, 23), (10, 14), (13, 20), (11, 13), (12, 15), (9, 18), (11, 21), (17, 21), (9, 13), (13, 14), (15, 19), (20, 21), (17, 22), (9, 17), (8, 15), (14, 19), (12, 13), (15, 20), (10, 18), (21, 23), (10, 17), (9, 23), (15, 21), (9, 14), (11, 19), (11, 12), (12, 20), (19, 22), (14, 17), (10, 19), (14, 23), (13, 21), (13, 15), (8, 22), (10, 16), (16, 23), (19, 20), (14, 22), (12, 14), (11, 15), (16, 22), (8, 23), (20, 23), (10, 22), (13, 18), (9, 11), (19, 21), (13, 22), (8, 20), (14, 16), (12, 23), (10, 20), (14, 20), (13, 16), (15, 18), (11, 20), (12, 22), (9, 10), (11, 23), (10, 12), (9, 12), (11, 14), (12, 19), (16, 19), (14, 18), (13, 19), (8, 18), (16, 21), (12, 17), (9, 20), (9, 19), (9, 22), (11, 17), (10, 13), (9, 16), (17, 19), (8, 12), (8, 14), (22, 23), (11, 18), (17, 20), (11, 22), (17, 23), (8, 21), (20, 22), (12, 21), (10, 11), (16, 17), (10, 23), (18, 21)]

/-- Actual support tree data in earlier-parent order. -/
def generatedFeasibleContainingZeroPairParent : Fin 120 → Fin 120 :=
  ![0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 8, 9, 9, 10, 11, 11, 12, 12, 13, 13, 14, 15, 15, 16, 16, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 23, 23, 24, 25, 26, 26, 27, 27, 28, 28, 29, 30, 30, 31, 31, 32, 32, 33, 33, 34, 34, 35, 36, 37, 38, 38, 39, 40, 41, 42, 43, 43, 44, 45, 46, 47, 48, 49, 50, 50, 51, 52, 52, 53, 53, 54, 54, 58, 59, 60, 60, 61, 61, 62, 63, 63, 64, 64, 65, 66, 66, 69, 70, 72, 73, 74, 75, 76, 81, 82, 85, 86, 87, 89, 91, 97, 102, 106]

/-- Actual support tree data in earlier-parent order. -/
def generatedFeasibleContainingZeroPairLetter : Fin 120 → Fin 2 :=
  ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]

/-- Actual support tree data in earlier-parent order. -/
def generatedFeasibleContainingZeroOctadNode : Fin 30 → Fin 4096 :=
  ![3, 26, 10, 54, 57, 53, 6, 31, 44, 16, 35, 5, 38, 32, 12, 48, 41, 21, 63, 58, 9, 28, 19, 60, 47, 22, 25, 42, 51, 37]

/-- Actual support tree data in earlier-parent order. -/
def generatedFeasibleContainingZeroOctadParent : Fin 30 → Fin 30 :=
  ![0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8, 8, 9, 11, 11, 12, 12, 13, 15, 21, 22, 23, 24, 28]

/-- Actual support tree data in earlier-parent order. -/
def generatedFeasibleContainingZeroOctadLetter : Fin 30 → Fin 2 :=
  ![0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0]

/-- Every original word fixes both actual first coordinates and the entire source support. -/
theorem generatedFeasibleContainingZeroSupportLetterArray_flags :
    ∀ k : Fin 2,
      generatedFeasibleContainingZeroSupportLetterArray k 0 = 0 ∧
      generatedFeasibleContainingZeroSupportLetterArray k 1 = 1 ∧
      ∀ i : Fin 24,
        (generatedFeasibleContainingZeroSupportLetterArray k i).val < 8 ↔ i.val < 8 := by
  decide +kernel

/-- The actual external pair catalogue has exactly 120 elements. -/
theorem generatedFeasibleContainingZeroPairs_card :
    generatedFeasibleContainingZeroPairs.card = 120 := by decide +kernel

/-- Every pair node lies in the entire actual external catalogue. -/
theorem generatedFeasibleContainingZeroPairNode_mem :
    ∀ n : Fin 120,
      generatedFeasibleContainingZeroPairNode n ∈ generatedFeasibleContainingZeroPairs := by
  decide +kernel

/-- Different node addresses describe different actual pair supports. -/
theorem generatedFeasibleContainingZeroPairNode_injective :
    Function.Injective generatedFeasibleContainingZeroPairNode := by decide +kernel

/-- Each pair node has a strictly earlier parent. -/
theorem generatedFeasibleContainingZeroPairParent_lt :
    ∀ n : Fin 120, n ≠ 0 → (generatedFeasibleContainingZeroPairParent n).val < n.val := by
  decide +kernel

/-- Every pair edge is checked against the actual original word array. -/
theorem generatedFeasibleContainingZeroPair_edge :
    ∀ n : Fin 120, n ≠ 0 →
      let p := generatedFeasibleContainingZeroPairNode (generatedFeasibleContainingZeroPairParent n)
      let q := generatedFeasibleContainingZeroPairNode n
      let a := generatedFeasibleContainingZeroSupportLetterArray (generatedFeasibleContainingZeroPairLetter n)
      (a p.1 = q.1 ∧ a p.2 = q.2) ∨ (a p.1 = q.2 ∧ a p.2 = q.1) := by
  decide +kernel

/-- Every octad node lies in the entire actual disjoint source catalogue. -/
theorem generatedFeasibleContainingZeroOctadNode_mem :
    ∀ n : Fin 30,
      generatedFeasibleContainingZeroOctadNode n ∈ generatedFeasibleContainingSelectedOutsideCodes 0 := by
  decide +kernel

/-- Different addresses describe different actual disjoint octads. -/
theorem generatedFeasibleContainingZeroOctadNode_injective :
    Function.Injective generatedFeasibleContainingZeroOctadNode := by decide +kernel

/-- Each disjoint octad node has a strictly earlier parent. -/
theorem generatedFeasibleContainingZeroOctadParent_lt :
    ∀ n : Fin 30, n ≠ 0 → (generatedFeasibleContainingZeroOctadParent n).val < n.val := by
  decide +kernel

/-- Every disjoint octad edge is checked against the original code encoder and word array. -/
theorem generatedFeasibleContainingZeroOctad_edge :
    ∀ n : Fin 30, n ≠ 0 → ∀ i : Fin 24,
      (golayEncodedMask (generatedFeasibleContainingZeroOctadNode
        (generatedFeasibleContainingZeroOctadParent n)).val).testBit i.val =
      (golayEncodedMask (generatedFeasibleContainingZeroOctadNode n).val).testBit
        (generatedFeasibleContainingZeroSupportLetterArray
          (generatedFeasibleContainingZeroOctadLetter n) i).val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
