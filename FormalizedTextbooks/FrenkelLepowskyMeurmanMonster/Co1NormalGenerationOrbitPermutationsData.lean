/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit normal-generation words for two actual Golay permutations.
The words were discovered by Sympy1.14.0; only the finite identities checked
by Lean's kernel are used, without a group-order or completeness assumption. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1NormalGenerationPermutations
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitPermutations

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The two existing actual Golay permutations and their inverses. -/
def co1NormalOrbitOperation (k : Fin 4) : golayAutomorphismSubgroup :=
  if k = 0 then omegaOrbitGolayPermutation 0 else
    if k = 1 then omegaOrbitGolayPermutation 1 else
      if k = 2 then (omegaOrbitGolayPermutation 0)⁻¹ else (omegaOrbitGolayPermutation 1)⁻¹

/-- Ten conjugating words of length at most two. -/
def co1NormalOrbitConjugatingWords : Fin 10 → List (Fin 4) :=
  ![[], [0], [1], [2], [0, 0], [0, 1], [1, 0], [1, 2], [2, 1], [2, 2]]

/-- The actual Golay permutation word conjugating the pair swap in the kth factor. -/
def co1NormalOrbitConjugator (k : Fin 10) : golayAutomorphismSubgroup :=
  ((co1NormalOrbitConjugatingWords k).map co1NormalOrbitOperation).prod

/-- Every factor is an actual conjugate of the certified pair-swap permutation. -/
def co1NormalOrbitFactor (k : Fin 10) : golayAutomorphismSubgroup :=
  co1NormalOrbitConjugator k * co1PairSwapGolay * (co1NormalOrbitConjugator k)⁻¹

/-- Explicit products giving the two source permutation generators. -/
def co1NormalOrbitGeneratorWords : Fin 2 → List (Fin 10) :=
  ![[1, 5, 2, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5,
    3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9,
    2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2,
    2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2,
    3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9,
    2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2,
    2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2,
    9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3,
    2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 9, 2, 9,
    5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2,
    9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3,
    5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2,
    2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2,
    3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2,
    9, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5,
    2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 9, 2, 9, 5, 3, 5, 2,
    3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 2, 3,
    2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2,
    2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2,
    9, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9,
    2, 5, 3, 5, 2, 3, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9,
    5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2,
    3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9,
    2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5,
    2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2],
  [1, 6, 5, 3, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 9, 2, 9,
    5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2,
    9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3,
    5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 9, 2, 9, 5, 3, 5,
    2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 2,
    3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3,
    2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2,
    2, 9, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2,
    9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3,
    2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2,
    9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5,
    3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3,
    5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2,
    2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2,
    3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3,
    2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 9, 2, 5, 3, 5,
    2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 9,
    2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3,
    5, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2,
    5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 9, 2, 9, 5,
    3, 5, 2, 3, 2, 5, 3, 5, 2, 9, 2, 9, 2, 9, 5, 3, 5, 2, 3, 2, 5, 3, 5, 2, 9,
    2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5,
    2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2,
    3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 3,
    2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2,
    2, 3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2,
    3, 2, 2, 9, 2, 5, 3, 5, 2, 3, 2, 5, 3, 5, 9, 2, 9, 2, 9, 2, 5, 3, 5, 2, 3,
    2, 5, 3, 5, 9, 2, 9, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 3, 2,
    2, 9, 2, 5, 3, 5, 2, 3, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2, 2, 9, 2, 2, 3, 2]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Reduce both finite permutation identities; the largest word has724 factors.
theorem co1NormalOrbitGenerator_certificate : ∀ k : Fin 2,
    ((co1NormalOrbitGeneratorWords k).map co1NormalOrbitFactor).prod =
      omegaOrbitGolayPermutation k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
