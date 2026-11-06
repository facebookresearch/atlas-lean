/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroSparseShortTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates

/-! Actual original physical preferred-root addresses for the bounded zero-class bridge. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option maxRecDepth 100000

/-- The fourteen original Golay encoder labels of all octads occurring in the bridge packets. -/
def generatedFeasibleContainingZeroOutsideAnchorCode : Fin 14 → Fin 4096 := ![6, 10, 12, 768, 774, 778, 780, 2050, 2052, 2056, 2818, 2820, 2824, 2830]

theorem generatedFeasibleContainingZeroOutsideAnchorCode_mem : ∀ j : Fin 14, generatedFeasibleContainingZeroOutsideAnchorCode j ∈ golayOctads := by decide +kernel

/-- The actual octad index of each cached encoder label. -/
def generatedFeasibleContainingZeroOutsideAnchorOctad (j : Fin 14) : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨generatedFeasibleContainingZeroOutsideAnchorCode j, generatedFeasibleContainingZeroOutsideAnchorCode_mem j⟩

theorem generatedFeasibleContainingZeroOutsideAnchorOctad_label (j : Fin 14) :
    golayOctadLabel (generatedFeasibleContainingZeroOutsideAnchorOctad j) = generatedFeasibleContainingZeroOutsideAnchorCode j :=
  congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply _)

/-- Increasing physical coordinates of each cached octad. -/
def generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate : Fin 14 → Fin 8 → Fin 24 :=
  ![![12, 13, 14, 15, 16, 17, 18, 19],
  ![12, 13, 14, 15, 20, 21, 22, 23],
  ![16, 17, 18, 19, 20, 21, 22, 23],
  ![1, 2, 13, 14, 17, 19, 22, 23],
  ![1, 2, 12, 15, 16, 18, 22, 23],
  ![1, 2, 12, 15, 17, 19, 20, 21],
  ![1, 2, 13, 14, 16, 18, 20, 21],
  ![0, 1, 2, 3, 12, 13, 14, 15],
  ![0, 1, 2, 3, 16, 17, 18, 19],
  ![0, 1, 2, 3, 20, 21, 22, 23],
  ![0, 3, 12, 15, 17, 19, 22, 23],
  ![0, 3, 13, 14, 16, 18, 22, 23],
  ![0, 3, 13, 14, 17, 19, 20, 21],
  ![0, 3, 12, 15, 16, 18, 20, 21]]

/-- Bind every cached physical coordinate to the entire actual octad catalogue. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate_actual :
    ∀ j : Fin 14, ∀ k : Fin 8,
      golayOctadCoordinate (generatedFeasibleContainingZeroOutsideAnchorOctad j) k =
        generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j k := by
  intro j k
  let t := golayMaskSupport
    (golayEncodedMask (golayOctadLabel (generatedFeasibleContainingZeroOutsideAnchorOctad j)).val)
  let e := t.orderIsoOfFin (golayOctad_support_card (generatedFeasibleContainingZeroOutsideAnchorOctad j))
  have hm : (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val).testBit
      (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j k).val = true := by
    have hc : ∀ j' : Fin 14, ∀ k' : Fin 8,
        (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j').val).testBit
          (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j' k').val = true := by decide +kernel
    exact hc j k
  let v : t := ⟨generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j k, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedFeasibleContainingZeroOutsideAnchorOctad_label]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel (generatedFeasibleContainingZeroOutsideAnchorOctad j)).val)).sort.idxOf
        (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j k) = k.val
    rw [generatedFeasibleContainingZeroOutsideAnchorOctad_label]
    have hs : (golayMaskSupport (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val)).sort =
        List.ofFn (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j) := by
      have hsorted : ∀ j' : Fin 14,
          List.SortedLT (List.ofFn (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j')) := by
        decide +kernel
      apply ((golayMaskSupport
        (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val)).sortedLT_sort).eq_of_mem_iff
          (hsorted j)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j' : Fin 14, ∀ i' : Fin 24,
          i' ∈ golayMaskSupport (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j').val) ↔
            i' ∈ List.ofFn (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j') := by decide +kernel
      exact hc j i
    rw [hs]
    have hc : ∀ j' : Fin 14, ∀ k' : Fin 8,
        (List.ofFn (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j')).idxOf
          (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j' k') = k'.val := by decide +kernel
    exact hc j k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The original even sign pattern is evaluated in its actual physical coordinates. -/
def generatedFeasibleContainingZeroOutsideAnchorSignMask (j : Fin 14) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate j k).val else 0) ||| m) 0

/-- The cached sign mask is exactly the original preferred octad sign mask. -/
theorem generatedFeasibleContainingZeroOutsideAnchorSignMask_actual (j : Fin 14) (e : Fin 64) :
    generatedFeasibleContainingZeroOutsideAnchorSignMask j e =
      griessOctadSignMask (generatedFeasibleContainingZeroOutsideAnchorOctad j) e := by
  simp only [generatedFeasibleContainingZeroOutsideAnchorSignMask, griessOctadSignMask,
    generatedFeasibleContainingZeroOutsideAnchorOctadCoordinate_actual]

/-- Bridge short labels: signed pairs, or a cached octad with an even sign pattern. -/
abbrev GeneratedFeasibleContainingZeroOutsideAnchorLabel :=
  (Fin 2 × Fin 276) ⊕ (Fin 14 × Fin 64)

/-- The original preferred short index of each bridge label. -/
def generatedFeasibleContainingZeroOutsideAnchorIndex : GeneratedFeasibleContainingZeroOutsideAnchorLabel → GriessShortIndex
  | Sum.inl (s, p) => Sum.inl (s, p)
  | Sum.inr (j, e) => Sum.inr (Sum.inl (generatedFeasibleContainingZeroOutsideAnchorOctad j, e))

/-- The integral Leech coordinates of each bridge label. -/
def generatedFeasibleContainingZeroOutsideAnchorIntegral : GeneratedFeasibleContainingZeroOutsideAnchorLabel → Fin 24 → ℤ
  | Sum.inl (s, p) => fun i =>
    4 * (if i = (generatedAxisGlobalPairCoordinates p).1 then 1 else 0) +
      (if s = 0 then -4 else 4) *
        (if i = (generatedAxisGlobalPairCoordinates p).2 then 1 else 0)
  | Sum.inr (j, e) => fun i =>
    if (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val).testBit i.val then
      if (generatedFeasibleContainingZeroOutsideAnchorSignMask j e).testBit i.val then -2 else 2
    else 0

theorem generatedFeasibleContainingZeroOutsideAnchorIntegral_actual (r : GeneratedFeasibleContainingZeroOutsideAnchorLabel) :
    generatedFeasibleContainingZeroOutsideAnchorIntegral r = griessShortIntegral (generatedFeasibleContainingZeroOutsideAnchorIndex r) := by
  rcases r with ⟨s, p⟩ | ⟨j, e⟩
  · simp only [generatedFeasibleContainingZeroOutsideAnchorIntegral, generatedFeasibleContainingZeroOutsideAnchorIndex,
      griessShortIntegral, generatedAxisGlobalPairCoordinates_actual]
  · simp only [generatedFeasibleContainingZeroOutsideAnchorIntegral, generatedFeasibleContainingZeroOutsideAnchorIndex,
      griessShortIntegral, generatedFeasibleContainingZeroOutsideAnchorOctad_label, generatedFeasibleContainingZeroOutsideAnchorSignMask_actual]

/-- The executable preferred extraspecial element of each bridge label. -/
def generatedFeasibleContainingZeroOutsideAnchorQ (r : GeneratedFeasibleContainingZeroOutsideAnchorLabel) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity
    (monsterNortonLeechCoordinates (generatedFeasibleContainingZeroOutsideAnchorIntegral r))), 1⟩

theorem generatedFeasibleContainingZeroOutsideAnchorQ_actual (r : GeneratedFeasibleContainingZeroOutsideAnchorLabel) :
    generatedFeasibleContainingZeroOutsideAnchorQ r = griessShortQ (generatedFeasibleContainingZeroOutsideAnchorIndex r) := by
  rw [← monsterNortonShortQ_eq]
  simp only [generatedFeasibleContainingZeroOutsideAnchorQ, monsterNortonShortQ, generatedFeasibleContainingZeroOutsideAnchorIntegral_actual]

/-- The 120 short labels supporting each of the four bridge stages. -/
def generatedFeasibleContainingZeroOutsideAnchorRoot : Fin 4 → Fin 120 → GeneratedFeasibleContainingZeroOutsideAnchorLabel :=
  fun k n => ((![#[(Sum.inl (0, 2)), (Sum.inl (1, 2)), (Sum.inl (0, 11)), (Sum.inl (1, 11)), (Sum.inl (0, 14)), (Sum.inl (1, 14)), (Sum.inl (0, 16)), (Sum.inl (1, 16)), (Sum.inl (0, 18)), (Sum.inl (1, 18)), (Sum.inl (0, 21)), (Sum.inl (1, 21)), (Sum.inl (0, 22)), (Sum.inl (1, 22)), (Sum.inl (0, 74)), (Sum.inl (1, 74)), (Sum.inl (0, 77)), (Sum.inl (1, 77)), (Sum.inl (0, 79)), (Sum.inl (1, 79)), (Sum.inl (0, 81)), (Sum.inl (1, 81)), (Sum.inl (0, 84)), (Sum.inl (1, 84)), (Sum.inl (0, 85)), (Sum.inl (1, 85)), (Sum.inl (0, 212)), (Sum.inl (1, 212)), (Sum.inl (0, 214)), (Sum.inl (1, 214)), (Sum.inl (0, 216)), (Sum.inl (1, 216)), (Sum.inl (0, 219)), (Sum.inl (1, 219)), (Sum.inl (0, 220)), (Sum.inl (1, 220)), (Sum.inl (0, 241)), (Sum.inl (1, 241)), (Sum.inl (0, 243)), (Sum.inl (1, 243)), (Sum.inl (0, 246)), (Sum.inl (1, 246)), (Sum.inl (0, 247)), (Sum.inl (1, 247)), (Sum.inl (0, 256)), (Sum.inl (1, 256)), (Sum.inl (0, 259)), (Sum.inl (1, 259)), (Sum.inl (0, 260)), (Sum.inl (1, 260)), (Sum.inl (0, 268)), (Sum.inl (1, 268)), (Sum.inl (0, 269)), (Sum.inl (1, 269)), (Sum.inl (0, 275)), (Sum.inl (1, 275)), (Sum.inr (10, 0)), (Sum.inr (10, 1)), (Sum.inr (10, 2)), (Sum.inr (10, 3)), (Sum.inr (10, 4)), (Sum.inr (10, 5)), (Sum.inr (10, 6)), (Sum.inr (10, 7)), (Sum.inr (10, 8)), (Sum.inr (10, 9)), (Sum.inr (10, 10)), (Sum.inr (10, 11)), (Sum.inr (10, 12)), (Sum.inr (10, 13)), (Sum.inr (10, 14)), (Sum.inr (10, 15)), (Sum.inr (10, 16)), (Sum.inr (10, 17)), (Sum.inr (10, 18)), (Sum.inr (10, 19)), (Sum.inr (10, 20)), (Sum.inr (10, 21)), (Sum.inr (10, 22)), (Sum.inr (10, 23)), (Sum.inr (10, 24)), (Sum.inr (10, 25)), (Sum.inr (10, 26)), (Sum.inr (10, 27)), (Sum.inr (10, 28)), (Sum.inr (10, 29)), (Sum.inr (10, 30)), (Sum.inr (10, 31)), (Sum.inr (10, 32)), (Sum.inr (10, 33)), (Sum.inr (10, 34)), (Sum.inr (10, 35)), (Sum.inr (10, 36)), (Sum.inr (10, 37)), (Sum.inr (10, 38)), (Sum.inr (10, 39)), (Sum.inr (10, 40)), (Sum.inr (10, 41)), (Sum.inr (10, 42)), (Sum.inr (10, 43)), (Sum.inr (10, 44)), (Sum.inr (10, 45)), (Sum.inr (10, 46)), (Sum.inr (10, 47)), (Sum.inr (10, 48)), (Sum.inr (10, 49)), (Sum.inr (10, 50)), (Sum.inr (10, 51)), (Sum.inr (10, 52)), (Sum.inr (10, 53)), (Sum.inr (10, 54)), (Sum.inr (10, 55)), (Sum.inr (10, 56)), (Sum.inr (10, 57)), (Sum.inr (10, 58)), (Sum.inr (10, 59)), (Sum.inr (10, 60)), (Sum.inr (10, 61)), (Sum.inr (10, 62)), (Sum.inr (10, 63))],
  #[(Sum.inl (1, 2)), (Sum.inl (1, 23)), (Sum.inr (7, 15)), (Sum.inr (7, 0)), (Sum.inr (7, 32)), (Sum.inr (7, 47)), (Sum.inr (8, 63)), (Sum.inr (8, 48)), (Sum.inr (8, 32)), (Sum.inr (8, 47)), (Sum.inr (9, 31)), (Sum.inr (9, 16)), (Sum.inr (9, 32)), (Sum.inr (9, 47)), (Sum.inr (7, 6)), (Sum.inr (7, 9)), (Sum.inr (7, 41)), (Sum.inr (7, 38)), (Sum.inr (8, 54)), (Sum.inr (8, 57)), (Sum.inr (8, 41)), (Sum.inr (8, 38)), (Sum.inr (9, 22)), (Sum.inr (9, 25)), (Sum.inr (9, 41)), (Sum.inr (9, 38)), (Sum.inl (1, 212)), (Sum.inl (1, 221)), (Sum.inr (0, 63)), (Sum.inr (0, 48)), (Sum.inr (0, 32)), (Sum.inr (0, 47)), (Sum.inr (1, 31)), (Sum.inr (1, 16)), (Sum.inr (1, 32)), (Sum.inr (1, 47)), (Sum.inr (0, 54)), (Sum.inr (0, 57)), (Sum.inr (0, 41)), (Sum.inr (0, 38)), (Sum.inr (1, 22)), (Sum.inr (1, 25)), (Sum.inr (1, 41)), (Sum.inr (1, 38)), (Sum.inl (0, 256)), (Sum.inl (0, 249)), (Sum.inr (2, 28)), (Sum.inr (2, 19)), (Sum.inr (2, 35)), (Sum.inr (2, 44)), (Sum.inr (2, 22)), (Sum.inr (2, 25)), (Sum.inr (2, 41)), (Sum.inr (2, 38)), (Sum.inl (0, 275)), (Sum.inl (0, 270)), (Sum.inr (6, 16)), (Sum.inr (11, 44)), (Sum.inr (11, 47)), (Sum.inr (6, 19)), (Sum.inr (4, 35)), (Sum.inr (13, 31)), (Sum.inr (13, 28)), (Sum.inr (4, 32)), (Sum.inr (4, 47)), (Sum.inr (13, 19)), (Sum.inr (13, 16)), (Sum.inr (4, 44)), (Sum.inr (6, 28)), (Sum.inr (11, 32)), (Sum.inr (11, 35)), (Sum.inr (6, 31)), (Sum.inr (3, 31)), (Sum.inr (12, 35)), (Sum.inr (12, 32)), (Sum.inr (3, 28)), (Sum.inr (5, 44)), (Sum.inr (10, 16)), (Sum.inr (10, 19)), (Sum.inr (5, 47)), (Sum.inr (5, 32)), (Sum.inr (10, 28)), (Sum.inr (10, 31)), (Sum.inr (5, 35)), (Sum.inr (3, 19)), (Sum.inr (12, 47)), (Sum.inr (12, 44)), (Sum.inr (3, 16)), (Sum.inr (3, 47)), (Sum.inr (12, 19)), (Sum.inr (12, 16)), (Sum.inr (3, 44)), (Sum.inr (5, 28)), (Sum.inr (10, 32)), (Sum.inr (10, 35)), (Sum.inr (5, 31)), (Sum.inr (5, 16)), (Sum.inr (10, 44)), (Sum.inr (10, 47)), (Sum.inr (5, 19)), (Sum.inr (3, 35)), (Sum.inr (12, 31)), (Sum.inr (12, 28)), (Sum.inr (3, 32)), (Sum.inr (6, 32)), (Sum.inr (11, 28)), (Sum.inr (11, 31)), (Sum.inr (6, 35)), (Sum.inr (4, 19)), (Sum.inr (13, 47)), (Sum.inr (13, 44)), (Sum.inr (4, 16)), (Sum.inr (4, 31)), (Sum.inr (13, 35)), (Sum.inr (13, 32)), (Sum.inr (4, 28)), (Sum.inr (6, 44)), (Sum.inr (11, 16)), (Sum.inr (11, 19)), (Sum.inr (6, 47))],
  #[(Sum.inl (1, 2)), (Sum.inl (0, 23)), (Sum.inl (1, 212)), (Sum.inl (0, 221)), (Sum.inl (0, 249)), (Sum.inl (1, 256)), (Sum.inl (0, 270)), (Sum.inl (1, 275)), (Sum.inr (3, 5)), (Sum.inr (3, 6)), (Sum.inr (3, 9)), (Sum.inr (3, 10)), (Sum.inr (3, 53)), (Sum.inr (3, 54)), (Sum.inr (3, 57)), (Sum.inr (3, 58)), (Sum.inr (7, 2)), (Sum.inr (7, 4)), (Sum.inr (7, 11)), (Sum.inr (7, 13)), (Sum.inr (7, 34)), (Sum.inr (7, 36)), (Sum.inr (7, 43)), (Sum.inr (7, 45)), (Sum.inr (10, 0)), (Sum.inr (10, 3)), (Sum.inr (10, 12)), (Sum.inr (10, 15)), (Sum.inr (10, 48)), (Sum.inr (10, 51)), (Sum.inr (10, 60)), (Sum.inr (10, 63)), (Sum.inr (8, 2)), (Sum.inr (8, 4)), (Sum.inr (8, 11)), (Sum.inr (8, 13)), (Sum.inr (8, 18)), (Sum.inr (8, 20)), (Sum.inr (8, 27)), (Sum.inr (8, 29)), (Sum.inr (11, 20)), (Sum.inr (11, 23)), (Sum.inr (11, 24)), (Sum.inr (11, 27)), (Sum.inr (11, 36)), (Sum.inr (11, 39)), (Sum.inr (11, 40)), (Sum.inr (11, 43)), (Sum.inr (0, 2)), (Sum.inr (0, 4)), (Sum.inr (0, 11)), (Sum.inr (0, 13)), (Sum.inr (0, 18)), (Sum.inr (0, 20)), (Sum.inr (0, 27)), (Sum.inr (0, 29)), (Sum.inr (4, 17)), (Sum.inr (4, 18)), (Sum.inr (4, 29)), (Sum.inr (4, 30)), (Sum.inr (4, 33)), (Sum.inr (4, 34)), (Sum.inr (4, 45)), (Sum.inr (4, 46)), (Sum.inr (9, 18)), (Sum.inr (9, 20)), (Sum.inr (9, 27)), (Sum.inr (9, 29)), (Sum.inr (9, 34)), (Sum.inr (9, 36)), (Sum.inr (9, 43)), (Sum.inr (9, 45)), (Sum.inr (12, 4)), (Sum.inr (12, 7)), (Sum.inr (12, 8)), (Sum.inr (12, 11)), (Sum.inr (12, 52)), (Sum.inr (12, 55)), (Sum.inr (12, 56)), (Sum.inr (12, 59)), (Sum.inr (1, 18)), (Sum.inr (1, 20)), (Sum.inr (1, 27)), (Sum.inr (1, 29)), (Sum.inr (1, 34)), (Sum.inr (1, 36)), (Sum.inr (1, 43)), (Sum.inr (1, 45)), (Sum.inr (5, 1)), (Sum.inr (5, 2)), (Sum.inr (5, 13)), (Sum.inr (5, 14)), (Sum.inr (5, 49)), (Sum.inr (5, 50)), (Sum.inr (5, 61)), (Sum.inr (5, 62)), (Sum.inr (2, 17)), (Sum.inr (2, 20)), (Sum.inr (2, 27)), (Sum.inr (2, 30)), (Sum.inr (2, 33)), (Sum.inr (2, 36)), (Sum.inr (2, 43)), (Sum.inr (2, 46)), (Sum.inr (6, 21)), (Sum.inr (6, 22)), (Sum.inr (6, 25)), (Sum.inr (6, 26)), (Sum.inr (6, 37)), (Sum.inr (6, 38)), (Sum.inr (6, 41)), (Sum.inr (6, 42)), (Sum.inr (13, 16)), (Sum.inr (13, 19)), (Sum.inr (13, 28)), (Sum.inr (13, 31)), (Sum.inr (13, 32)), (Sum.inr (13, 35)), (Sum.inr (13, 44)), (Sum.inr (13, 47))],
  #[(Sum.inl (1, 23)), (Sum.inl (0, 23)), (Sum.inl (1, 221)), (Sum.inl (0, 221)), (Sum.inl (1, 249)), (Sum.inl (0, 249)), (Sum.inl (1, 270)), (Sum.inl (0, 270)), (Sum.inr (6, 26)), (Sum.inr (6, 25)), (Sum.inr (6, 22)), (Sum.inr (6, 21)), (Sum.inr (6, 42)), (Sum.inr (6, 41)), (Sum.inr (6, 38)), (Sum.inr (6, 37)), (Sum.inl (1, 35)), (Sum.inl (1, 56)), (Sum.inl (0, 56)), (Sum.inl (0, 35)), (Sum.inl (1, 34)), (Sum.inl (1, 55)), (Sum.inl (0, 55)), (Sum.inl (0, 34)), (Sum.inr (6, 16)), (Sum.inr (6, 19)), (Sum.inr (6, 28)), (Sum.inr (6, 31)), (Sum.inr (6, 32)), (Sum.inr (6, 35)), (Sum.inr (6, 44)), (Sum.inr (6, 47)), (Sum.inl (1, 39)), (Sum.inl (1, 60)), (Sum.inl (0, 60)), (Sum.inl (0, 39)), (Sum.inl (0, 37)), (Sum.inl (0, 58)), (Sum.inl (1, 58)), (Sum.inl (1, 37)), (Sum.inr (6, 56)), (Sum.inr (6, 59)), (Sum.inr (6, 52)), (Sum.inr (6, 55)), (Sum.inr (6, 8)), (Sum.inr (6, 11)), (Sum.inr (6, 4)), (Sum.inr (6, 7)), (Sum.inl (1, 225)), (Sum.inl (1, 234)), (Sum.inl (0, 234)), (Sum.inl (0, 225)), (Sum.inl (0, 223)), (Sum.inl (0, 232)), (Sum.inl (1, 232)), (Sum.inl (1, 223)), (Sum.inr (6, 50)), (Sum.inr (6, 49)), (Sum.inr (6, 62)), (Sum.inr (6, 61)), (Sum.inr (6, 2)), (Sum.inr (6, 1)), (Sum.inr (6, 14)), (Sum.inr (6, 13)), (Sum.inl (0, 41)), (Sum.inl (0, 62)), (Sum.inl (1, 62)), (Sum.inl (1, 41)), (Sum.inl (1, 42)), (Sum.inl (1, 63)), (Sum.inl (0, 63)), (Sum.inl (0, 42)), (Sum.inr (6, 39)), (Sum.inr (6, 36)), (Sum.inr (6, 43)), (Sum.inr (6, 40)), (Sum.inr (6, 23)), (Sum.inr (6, 20)), (Sum.inr (6, 27)), (Sum.inr (6, 24)), (Sum.inl (0, 227)), (Sum.inl (0, 236)), (Sum.inl (1, 236)), (Sum.inl (1, 227)), (Sum.inl (1, 228)), (Sum.inl (1, 237)), (Sum.inl (0, 237)), (Sum.inl (0, 228)), (Sum.inr (6, 45)), (Sum.inr (6, 46)), (Sum.inr (6, 33)), (Sum.inr (6, 34)), (Sum.inr (6, 29)), (Sum.inr (6, 30)), (Sum.inr (6, 17)), (Sum.inr (6, 18)), (Sum.inl (1, 251)), (Sum.inl (0, 262)), (Sum.inl (1, 262)), (Sum.inl (0, 251)), (Sum.inl (0, 252)), (Sum.inl (1, 263)), (Sum.inl (0, 263)), (Sum.inl (1, 252)), (Sum.inr (6, 5)), (Sum.inr (6, 6)), (Sum.inr (6, 9)), (Sum.inr (6, 10)), (Sum.inr (6, 53)), (Sum.inr (6, 54)), (Sum.inr (6, 57)), (Sum.inr (6, 58)), (Sum.inr (6, 15)), (Sum.inr (6, 12)), (Sum.inr (6, 3)), (Sum.inr (6, 0)), (Sum.inr (6, 63)), (Sum.inr (6, 60)), (Sum.inr (6, 51)), (Sum.inr (6, 48))]] : Fin 4 → Array GeneratedFeasibleContainingZeroOutsideAnchorLabel) k).getD n.val (Sum.inl (0, 0))

/-- The unit short coefficients of the four bridge stages, aligned with their labels. -/
def generatedFeasibleContainingZeroOutsideAnchorCoefficient : Fin 4 → Fin 120 → ℤ :=
  fun k n => ((![#[1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, -1, -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, 1, 1],
  #[1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1],
  #[-1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1],
  #[-1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1]] : Fin 4 → Array ℤ) k).getD n.val 0

/-- Different certified original codes retain different actual octad indices. -/
theorem generatedFeasibleContainingZeroOutsideAnchorCode_injective :
    Function.Injective generatedFeasibleContainingZeroOutsideAnchorCode := by decide +kernel

/-- Cached labels faithfully distinguish the entire original preferred short catalogue. -/
theorem generatedFeasibleContainingZeroOutsideAnchorIndex_injective :
    Function.Injective generatedFeasibleContainingZeroOutsideAnchorIndex := by
  intro r s h
  rcases r with ⟨a, p⟩ | ⟨j, e⟩ <;> rcases s with ⟨b, q⟩ | ⟨k, f⟩
  · exact congrArg Sum.inl (Sum.inl_injective h)
  · simp [generatedFeasibleContainingZeroOutsideAnchorIndex] at h
  · simp [generatedFeasibleContainingZeroOutsideAnchorIndex] at h
  · simp only [generatedFeasibleContainingZeroOutsideAnchorIndex, Sum.inr.injEq,
      Sum.inl.injEq, Prod.mk.injEq] at h
    have hc := congrArg golayOctadLabel h.1
    rw [generatedFeasibleContainingZeroOutsideAnchorOctad_label,
      generatedFeasibleContainingZeroOutsideAnchorOctad_label] at hc
    exact congrArg Sum.inr (Prod.ext
      (generatedFeasibleContainingZeroOutsideAnchorCode_injective hc) h.2)

/-- The complete original physical support predicate is computed from certified encoder labels. -/
def generatedFeasibleContainingZeroOutsideAnchorSupport (j : Fin 14) :
    GeneratedFeasibleContainingZeroOutsideAnchorLabel → Prop
  | Sum.inl (_, p) =>
      (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val).testBit
        (generatedAxisGlobalPairCoordinates p).1.val = true ∧
      (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode j).val).testBit
        (generatedAxisGlobalPairCoordinates p).2.val = true
  | Sum.inr (k, _) => k = j

/-- Every computed support predicate is the entire actual octad short support. -/
theorem generatedFeasibleContainingZeroOutsideAnchorSupport_actual
    (j : Fin 14) (r : GeneratedFeasibleContainingZeroOutsideAnchorLabel) :
    generatedFeasibleContainingZeroOutsideAnchorSupport j r ↔
      generatedOctadShortSupport (generatedFeasibleContainingZeroOutsideAnchorOctad j)
        (generatedFeasibleContainingZeroOutsideAnchorIndex r) := by
  rcases r with ⟨s, p⟩ | ⟨k, e⟩
  · simp only [generatedFeasibleContainingZeroOutsideAnchorSupport,
      generatedFeasibleContainingZeroOutsideAnchorIndex, generatedOctadShortSupport,
      generatedOctadPairSupport, generatedFeasibleContainingZeroOutsideAnchorOctad_label,
      generatedAxisGlobalPairCoordinates_actual]
  · change k = j ↔ generatedFeasibleContainingZeroOutsideAnchorOctad k =
      generatedFeasibleContainingZeroOutsideAnchorOctad j
    constructor
    · rintro rfl; rfl
    · intro h
      apply generatedFeasibleContainingZeroOutsideAnchorCode_injective
      simpa only [generatedFeasibleContainingZeroOutsideAnchorOctad_label] using
        congrArg golayOctadLabel h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
