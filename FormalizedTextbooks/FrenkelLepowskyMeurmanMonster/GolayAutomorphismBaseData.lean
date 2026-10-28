/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! A finite, kernel-checked seven-point base of the actual Golay automorphism group.
Eight octad incidence patterns separate all remaining coordinates except 6 and 7.
The minimum-weight argument in GolayAutomorphismBase rules out their transposition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The eight selected bit patterns on the seven fixed points. -/
def golayBaseSelectedPatterns : Fin 8 → ℕ := ![3, 12, 21, 6, 9, 5, 19, 10]

/-- All octad labels with each selected pattern, explicitly enumerated. -/
def golayBasePatternOctads : Fin 8 → Finset (Fin 4096) :=
  ![([2306, 2308, 2312, 2318, 2324, 2328, 2338, 2340,
    2354, 2360, 2372, 2376, 2386] : List (Fin 4096)).toFinset,
  ([256, 262, 266, 268, 272, 284, 288, 294, 304, 314, 320, 332, 336] : List (Fin 4096)).toFinset,
  ([2691, 2703, 2735, 2757, 2767, 2783] : List (Fin 4096)).toFinset,
  ([768, 774, 778, 780, 784, 790, 800, 810, 816, 828, 832, 842, 864] : List (Fin 4096)).toFinset,
  ([
    2818, 2820, 2824, 2830, 2834, 2836, 2850, 2856, 2868, 2872,
    2882, 2888, 2916
  ] : List (Fin 4096)).toFinset,
  ([
    2562, 2564, 2568, 2574, 2578, 2584, 2596, 2600, 2610, 2612,
    2626, 2628, 2680
  ] : List (Fin 4096)).toFinset,
  ([2437, 2447, 2495, 2505, 2511, 2543] : List (Fin 4096)).toFinset,
  ([512, 518, 522, 524, 528, 538, 544, 556, 560, 566, 576, 582, 624] : List (Fin 4096)).toFinset]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Eight filters certify every octad of each selected seven-point pattern.
theorem golayBasePatternOctads_certificate : ∀ k : Fin 8,
    golayOctads.filter (fun d => golayBasePattern d = golayBaseSelectedPatterns k) =
      golayBasePatternOctads k := by
  decide +kernel

/-- Incidence counts, with rows indexed by physical coordinates. -/
def golayBaseIncidenceTable : Fin 24 → Fin 8 → ℕ :=
  ![![13, 0, 6, 0, 13, 13, 6, 0],
  ![13, 0, 0, 13, 0, 0, 6, 13],
  ![0, 13, 6, 13, 0, 13, 0, 0],
  ![0, 13, 0, 0, 13, 0, 0, 13],
  ![0, 0, 6, 0, 0, 0, 6, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![3, 3, 3, 3, 3, 3, 3, 3],
  ![3, 3, 3, 3, 3, 3, 3, 3],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 4, 1, 5, 5, 5, 2, 5],
  ![5, 5, 1, 4, 4, 5, 1, 5],
  ![5, 5, 2, 5, 5, 4, 1, 4],
  ![5, 4, 1, 5, 5, 5, 2, 5],
  ![5, 4, 2, 5, 5, 5, 2, 5],
  ![4, 5, 1, 5, 5, 5, 2, 5],
  ![4, 5, 2, 5, 5, 5, 2, 5],
  ![5, 5, 1, 4, 5, 5, 1, 5],
  ![5, 5, 1, 5, 4, 5, 2, 5],
  ![5, 5, 2, 4, 5, 5, 2, 5],
  ![5, 5, 2, 5, 4, 5, 1, 5],
  ![5, 5, 2, 5, 5, 5, 1, 4],
  ![5, 5, 2, 5, 5, 4, 2, 5],
  ![5, 5, 2, 5, 5, 4, 1, 5],
  ![5, 5, 2, 5, 5, 5, 2, 4]]

set_option maxHeartbeats 12000000 in
-- Count the explicitly enumerated octads at each of the 24 coordinates.
theorem golayBaseIncidenceTable_certificate : ∀ k : Fin 8, ∀ i : Fin 24,
    golayBaseIncidence (golayBaseSelectedPatterns k) i = golayBaseIncidenceTable i k := by
  intro k i
  unfold golayBaseIncidence
  rw [← Finset.filter_filter, golayBasePatternOctads_certificate]
  have h : ∀ k : Fin 8, ∀ i : Fin 24,
      ((golayBasePatternOctads k).filter
        (fun d => golayEncoder (golayLabelCoefficients d) i = 1)).card =
          golayBaseIncidenceTable i k := by decide +kernel
  exact h k i

/-- Every row outside 5, 8, 6, 7 is distinct from all other rows. -/
theorem golayBaseIncidenceTable_separates : ∀ i j : Fin 24,
    i ≠ 5 → i ≠ 8 → i ≠ 6 → i ≠ 7 →
    (∀ k : Fin 8, golayBaseIncidenceTable i k = golayBaseIncidenceTable j k) → i = j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
