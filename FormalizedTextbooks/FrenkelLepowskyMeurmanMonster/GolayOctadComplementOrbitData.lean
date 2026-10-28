/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayOutsidePairOctadOrbitProof

/-! Checked original words and physical support trees in the complement of octad three. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Four short genuine strong-generator words, as physical coordinate arrays. -/
def golayOctadComplementLetterArray : Fin 4 → Fin 24 → Fin 24 :=
  ![golayStrongLetterArray 9,
    fun i => golayStrongLetterArray 15 (golayStrongLetterArray 2
      (golayStrongLetterArray 1 i)),
    fun i => golayStrongLetterArray 15 (golayStrongLetterArray 7
      (golayStrongLetterArray 1 i)),
    fun i => golayStrongLetterArray 0 (golayStrongLetterArray 27
      (golayStrongLetterArray 14 i))]

/-- Actual unordered physical pairs outside coordinates eight through fifteen. -/
def golayOctadComplementPairs : Finset (Fin 24 × Fin 24) :=
  Finset.univ.filter fun p => p.1.val < p.2.val ∧
    ¬ (8 ≤ p.1.val ∧ p.1.val < 16) ∧ ¬ (8 ≤ p.2.val ∧ p.2.val < 16)

/-- Actual original octad labels disjoint from the original octad of label three. -/
def golayOctadComplementOctads : Finset (Fin 4096) :=
  Finset.univ.filter fun d => golayMaskWeight (golayEncodedMask d.val) = 8 ∧
    ∀ j : Fin 8, (golayEncodedMask d.val).testBit (8 + j.val) = false

/-- Physical pair supports in earlier-parent order. -/
def golayOctadComplementPairNode : Fin 120 → Fin 24 × Fin 24 :=
  ![
  (0, 1), (0, 20), (0, 21), (1, 2), (0, 19), (1, 20), (0, 18), (1, 23),
  (16, 20), (18, 21), (0, 2), (0, 5), (0, 6), (0, 23), (1, 18), (1, 19),
  (20, 21), (2, 20), (0, 4), (1, 17), (1, 16), (5, 20), (19, 21), (2, 22),
  (6, 19), (4, 18), (17, 23), (0, 16), (0, 17), (1, 6), (0, 22), (1, 4),
  (1, 22), (18, 20), (2, 21), (2, 17), (1, 5), (6, 20), (21, 23), (2, 18),
  (18, 19), (1, 21), (20, 23), (2, 19), (0, 3), (1, 7), (20, 22), (5, 21),
  (16, 21), (2, 16), (19, 20), (17, 20), (5, 18), (6, 21), (18, 23), (16, 17),
  (6, 18), (5, 23), (22, 23), (4, 21), (3, 18), (2, 4), (5, 17), (7, 16),
  (5, 22), (5, 19), (19, 22), (0, 7), (21, 22), (3, 20), (2, 5), (4, 19),
  (2, 7), (16, 22), (17, 21), (2, 6), (19, 23), (4, 20), (16, 18), (4, 5),
  (2, 23), (17, 18), (16, 19), (6, 16), (1, 3), (7, 20), (3, 21), (17, 19),
  (6, 23), (16, 23), (7, 19), (6, 17), (4, 23), (4, 16), (17, 22), (6, 7),
  (5, 16), (4, 17), (6, 22), (3, 4), (3, 17), (3, 16), (3, 19), (3, 6),
  (7, 18), (18, 22), (5, 6), (4, 6), (3, 23), (4, 7), (7, 21), (2, 3),
  (5, 7), (4, 22), (7, 23), (3, 5), (7, 17), (3, 22), (3, 7), (7, 22)]

/-- The earlier parent for each noninitial pair support. -/
def golayOctadComplementPairParent : Fin 120 → Fin 120 :=
  ![
  0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 3, 4,
  4, 4, 4, 5, 5, 5, 6, 6, 7, 7, 7, 7,
  8, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 14,
  15, 15, 15, 15, 16, 16, 16, 17, 18, 19, 19, 19,
  20, 20, 21, 21, 22, 22, 22, 23, 23, 24, 24, 25,
  25, 25, 25, 26, 26, 26, 26, 28, 29, 31, 31, 33,
  35, 35, 36, 36, 37, 37, 38, 40, 40, 40, 42, 43,
  44, 45, 45, 46, 47, 48, 51, 52, 53, 54, 54, 55,
  55, 56, 57, 60, 60, 61, 69, 71, 74, 75, 76, 78,
  79, 81, 84, 84, 87, 88, 91, 92, 94, 95, 100, 103]

/-- The genuine original word on each pair edge. -/
def golayOctadComplementPairLetter : Fin 120 → Fin 4 :=
  ![
  0, 1, 2, 3, 0, 3, 0, 3, 1, 2, 3, 0,
  1, 2, 3, 0, 2, 3, 0, 3, 0, 1, 2, 3,
  0, 0, 3, 1, 2, 3, 2, 3, 3, 1, 2, 3,
  0, 1, 2, 3, 0, 1, 3, 0, 1, 0, 1, 2,
  2, 3, 0, 2, 0, 1, 3, 1, 2, 0, 2, 0,
  1, 2, 3, 0, 1, 2, 3, 0, 2, 1, 3, 0,
  0, 1, 2, 3, 0, 3, 0, 0, 2, 3, 0, 1,
  3, 1, 2, 0, 3, 3, 0, 3, 3, 0, 3, 0,
  2, 3, 3, 0, 3, 1, 0, 1, 0, 2, 1, 0,
  1, 0, 2, 3, 0, 3, 0, 1, 0, 2, 0, 2]

/-- Actual original encoder labels in earlier-parent order. -/
def golayOctadComplementOctadNode : Fin 30 → Fin 4096 :=
  ![
  2063, 2056, 3011, 3023, 2052, 2371, 2376, 3012, 652, 640, 2691, 2692,
  972, 2383, 967, 3016, 2703, 2372, 651, 647, 332, 7, 320, 12,
  960, 971, 327, 2696, 331, 11]

/-- The earlier parent for each noninitial octad support. -/
def golayOctadComplementOctadParent : Fin 30 → Fin 30 :=
  ![
  0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 4, 4,
  5, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 12,
  13, 14, 14, 14, 18, 22]

/-- The genuine original word on each octad edge. -/
def golayOctadComplementOctadLetter : Fin 30 → Fin 4 :=
  ![
  0, 0, 1, 2, 0, 1, 2, 0, 3, 3, 1, 2,
  3, 0, 3, 0, 1, 2, 3, 0, 2, 1, 3, 2,
  3, 0, 2, 3, 3, 1]

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every actual word preserves precisely the original section coordinates. -/
theorem golayOctadComplement_letter_preserves :
    ∀ k : Fin 4, ∀ i : Fin 24,
      (8 ≤ (golayOctadComplementLetterArray k i).val ∧
        (golayOctadComplementLetterArray k i).val < 16) ↔
      (8 ≤ i.val ∧ i.val < 16) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- There are exactly120 actual unordered pairs outside the section. -/
theorem golayOctadComplement_pairs_card :
    golayOctadComplementPairs.card = 120 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- There are exactly30 original octad supports disjoint from this section. -/
theorem golayOctadComplement_octads_card :
    golayOctadComplementOctads.card = 30 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every displayed node belongs to the actual physical support catalogue. -/
theorem golayOctadComplement_pair_member :
    ∀ n : Fin 120, golayOctadComplementPairNode n ∈ golayOctadComplementPairs := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Different node addresses give distinct actual physical supports. -/
theorem golayOctadComplement_pair_injective :
    Function.Injective golayOctadComplementPairNode := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every noninitial incoming edge has a strictly earlier parent. -/
theorem golayOctadComplement_pair_parent_lt :
    ∀ n : Fin 120, n ≠ 0 → (golayOctadComplementPairParent n).val < n.val := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every parent edge agrees with the stated genuine original physical word. -/
theorem golayOctadComplement_pair_edge :
    ∀ n : Fin 120, n ≠ 0 →
      let p := golayOctadComplementPairNode (golayOctadComplementPairParent n)
      let q := golayOctadComplementPairNode n
      let a := golayOctadComplementLetterArray (golayOctadComplementPairLetter n)
      (a p.1 = q.1 ∧ a p.2 = q.2) ∨ (a p.1 = q.2 ∧ a p.2 = q.1) := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every displayed node belongs to the actual physical support catalogue. -/
theorem golayOctadComplement_octad_member :
    ∀ n : Fin 30, golayOctadComplementOctadNode n ∈ golayOctadComplementOctads := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Different node addresses give distinct actual physical supports. -/
theorem golayOctadComplement_octad_injective :
    Function.Injective golayOctadComplementOctadNode := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every noninitial incoming edge has a strictly earlier parent. -/
theorem golayOctadComplement_octad_parent_lt :
    ∀ n : Fin 30, n ≠ 0 → (golayOctadComplementOctadParent n).val < n.val := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Ordinary-kernel checks use only the displayed finite physical data and original encoder.
/-- Every parent edge agrees with the stated genuine original physical word. -/
theorem golayOctadComplement_octad_edge :
    ∀ n : Fin 30, n ≠ 0 → ∀ i : Fin 24,
      (golayEncodedMask
        (golayOctadComplementOctadNode (golayOctadComplementOctadParent n)).val).testBit i.val =
        (golayEncodedMask (golayOctadComplementOctadNode n).val).testBit
          (golayOctadComplementLetterArray (golayOctadComplementOctadLetter n) i).val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
