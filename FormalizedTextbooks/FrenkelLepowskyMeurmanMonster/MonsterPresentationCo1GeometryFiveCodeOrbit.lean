/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Short genuine M24 transports of two actual sign codes span the whole Golay code. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Each source code orbit word starts at one of the two actual sign generators four and five. -/
def monsterCo1FiveCodeSeed : Fin 12 → Fin 12 :=
  ![4, 5, 4, 5, 5, 4, 4, 5, 5, 4, 4, 4]

/-- Twelve short transport words use the actual two Golay permutation generators. -/
def monsterCo1FiveCodeWords : Fin 12 → List (Fin 2) :=
  ![[], [], [0], [0], [1], [0, 0], [0, 1], [0, 0], [1, 0], [0, 0, 0], [0, 0, 1], [0, 0, 0, 0]]

/-- These codewords are genuine actual permutation transports, not independently named codes. -/
def monsterCo1FiveOrbitCode (j : Fin 12) : golayCode :=
  (monsterCo1FiveCodeWords j).foldl
    (fun c k => golayCodePermutation (omegaOrbitGolayPermutation k) c)
    (monsterCo1GeometrySignCode (monsterCo1FiveCodeSeed j))

/-- A small finite subset of the orbit words expresses each original encoder-basis codeword. -/
def monsterCo1FiveCodeExpansion : Fin 12 → Finset (Fin 12) :=
  ![{0, 1, 6, 7, 8, 10},
    {0, 3, 6, 7, 9, 11},
    {0, 2, 6, 8, 9, 10},
    {0, 3, 4, 6, 7, 10, 11},
    {0},
    {1},
    {4},
    {0, 1, 2, 4, 8},
    {0, 1, 3, 4, 5, 8, 11},
    {2, 3, 4, 5, 8, 11},
    {2, 5, 6, 10},
    {0, 2, 4, 5, 6, 7, 10, 11}]

set_option maxHeartbeats 6000000 in
-- Check twelve sums of short actual permutation-transported encoder words.
/-- The literal orbit codewords span every encoder-basis codeword by exact binary arithmetic. -/
theorem monsterCo1FiveCodeExpansion_certificate : ∀ k : Fin 12,
    (∑ j ∈ monsterCo1FiveCodeExpansion k, monsterCo1FiveOrbitCode j) =
      monsterCo1GeometrySignCode k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
