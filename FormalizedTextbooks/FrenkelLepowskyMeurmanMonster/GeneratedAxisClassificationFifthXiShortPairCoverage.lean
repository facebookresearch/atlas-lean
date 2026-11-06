/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortNumerator

/-! Exact physical-pair coverage of the genuine fifth short-coordinate support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The136 genuine physical pairs occurring in the fifth-axis short support. -/
def generatedFifthXiShortSupportPair : Fin 136 → Fin 24 × Fin 24 :=
  ![(0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14),
    (0, 15), (0, 20), (0, 21), (0, 22), (0, 23), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9),
    (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 20), (1, 21), (1, 22), (1, 23),
    (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14),
    (2, 15), (2, 20), (2, 21), (2, 22), (2, 23), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9),
    (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 20), (3, 21), (3, 22), (3, 23),
    (4, 6), (4, 16), (4, 17), (4, 18), (4, 19), (5, 7), (5, 16), (5, 17), (5, 18), (5, 19), (6,
    16), (6, 17), (6, 18), (6, 19), (7, 16), (7, 17), (7, 18), (7, 19), (8, 11), (8, 16), (8,
    17), (8, 18), (8, 19), (9, 10), (9, 16), (9, 17), (9, 18), (9, 19), (10, 16), (10, 17), (10,
    18), (10, 19), (11, 16), (11, 17), (11, 18), (11, 19), (12, 13), (12, 16), (12, 17), (12,
    18), (12, 19), (13, 16), (13, 17), (13, 18), (13, 19), (14, 15), (14, 16), (14, 17), (14,
    18), (14, 19), (15, 16), (15, 17), (15, 18), (15, 19), (16, 20), (16, 21), (16, 22), (16,
    23), (17, 20), (17, 21), (17, 22), (17, 23), (18, 20), (18, 21), (18, 22), (18, 23), (19,
    20), (19, 21), (19, 22), (19, 23), (20, 22), (21, 23)]

/-- Every displayed pair is in the preferred increasing physical order. -/
theorem generatedFifthXiShortSupportPair_lt : ∀ r : Fin 136,
    (generatedFifthXiShortSupportPair r).1 < (generatedFifthXiShortSupportPair r).2 := by
  decide +kernel

/-- A finite physical-coordinate lookup for every supported pair. -/
def generatedFifthXiShortSupportPairLookup : Fin 24 → Fin 24 → Fin 136 :=
  ![![0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 0, 0, 0, 12, 13, 14, 15], ![0, 0, 0,
    0, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 0, 0, 0, 28, 29, 30, 31], ![0, 0, 0,
    0, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 0, 0, 0, 0, 44, 45, 46, 47], ![0, 0, 0,
    0, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 0, 0, 0, 0, 60, 61, 62, 63], ![0, 0, 0,
    0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65, 66, 67, 68, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0,
    69, 0, 0, 0, 0, 0, 0, 0, 0, 70, 71, 72, 73, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 74, 75, 76, 77, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 78, 79, 80, 81, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 0, 0, 0, 0, 83, 84,
    85, 86, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87, 0, 0, 0, 0, 0, 88, 89, 90, 91, 0,
    0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92, 93, 94, 95, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 97, 98, 99, 0, 0, 0, 0], ![0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 101, 102, 103, 104, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 106, 107, 108, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 109, 110, 111, 112, 113, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 114, 115, 116, 117, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 118, 119, 120, 121], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 122, 123, 124, 125], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    126, 127, 128, 129], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 130, 131,
    132, 133], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 134, 0], ![0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135], ![0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check all576 physical coordinate pairs against the original middle-projector numerators.
/-- Every genuinely nonzero pair numerator has its exact displayed physical pair. -/
theorem generatedFifthXiShortSupportPair_lookup : ∀ a b : Fin 24,
    a < b → generatedFifthMiddleProjectorNumerator a b ≠ 0 →
      generatedFifthXiShortSupportPair (generatedFifthXiShortSupportPairLookup a b) = (a, b) := by
  decide +kernel

/-- Genuine preferred-short labels of the displayed physical pair rows. -/
def generatedFifthXiShortSupportPairCached (s : Fin 2) (r : Fin 136) :
    generatedFifthXiShortCachedLabel :=
  Sum.inl (s, ⟨generatedFifthXiShortSupportPair r, generatedFifthXiShortSupportPair_lt r⟩)

/-- Any nonzero original pair coefficient is one of these genuinely cached support rows. -/
theorem generatedFifthXiShortSupportPair_actual (s : Fin 2) (p : Fin 276)
    (hp : (griessConwayEncode generatedFifthAxis).2.1 (Sum.inl (s, p)) ≠ 0) :
    ∃ r : Fin 136, generatedFifthXiShortCachedEven
      (generatedFifthXiShortSupportPairCached s r) = Sum.inl (s, p) := by
  have hl := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hl
  have hn : generatedFifthMiddleProjectorNumerator
      (griessCoordinatePair p).1 (griessCoordinatePair p).2 ≠ 0 := by
    intro hz
    apply hp
    rw [generatedFifth_final_pair_numerator]
    simp [generatedFifthFinalPairNumerator, hz]
  let r := generatedFifthXiShortSupportPairLookup
    (griessCoordinatePair p).1 (griessCoordinatePair p).2
  refine ⟨r, ?_⟩
  have hr := generatedFifthXiShortSupportPair_lookup _ _ hl hn
  simp only [generatedFifthXiShortSupportPairCached, generatedFifthXiShortCachedEven]
  apply congrArg (fun q : Fin 276 => (Sum.inl (s, q) : generatedFifthXiEvenShortLabel))
  apply griessCoordinatePairEquiv.injective
  apply Subtype.ext
  change griessCoordinatePair (griessPairIndex _ _ _) = griessCoordinatePair p
  rw [griessPairIndex_coordinates, ite_eq_left (generatedFifthXiShortSupportPair_lt r)]
  exact hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
