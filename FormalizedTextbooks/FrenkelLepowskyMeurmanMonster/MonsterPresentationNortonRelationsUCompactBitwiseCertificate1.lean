/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact algebraic binding of one actual Norton compact factor to its bitwise coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseParity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The bitwise label evaluator is exactly actual compact permutation 1. -/
theorem monsterNortonUCompactBitPermutation_actual_1 (n : Fin 4096) :
    nortonUIntegerLabel (monsterNortonUCompactPermutation 1 (golayLabelCoefficients n)) =
      monsterNortonUCompactBitPermutation 1 n := monsterNortonUCompactBitPermutation_actual 1 n

/-- The bitwise sign evaluator is exactly actual compact diagonal 1. -/
theorem monsterNortonUCompactBitDiagonal_actual_1 (n : Fin 4096) :
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 1)
      (golayLabelCoefficients n)) = monsterNortonUCompactBitDiagonal 1 n :=
        monsterNortonUCompactBitDiagonal_actual 1 n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
