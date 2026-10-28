/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual inverse compact numerator evaluated through twelve selected binary columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact inner inverse Gaussian label using the proved column-xor permutations. -/
def monsterNortonUCompactColumnInner (n : Fin 4096) (a : Fin 64) : Fin 4096 :=
  monsterNortonUCompactColumnPermutation 0
    (monsterNortonBitXor (monsterNortonUCompactColumnPermutation 1 n) (monsterNortonBitGrayLabel a))

/-- A sixty-four-term evaluator of the actual inverse numerator using column-xor permutations. -/
def monsterNortonUCompactColumnInverseNumerator (v : NortonUIntegerVector) : NortonUIntegerVector :=
  fun n => monsterNortonUCompactBitDiagonal 1 n * ∑ a : Fin 64,
    xiGraySign (monsterNortonGrayCoefficients a) *
      monsterNortonUCompactBitDiagonal 0 (monsterNortonUCompactColumnInner n a) *
      monsterNortonUCompactBitInversePhase (monsterNortonUCompactColumnInner n a) *
      v (monsterNortonBitXor (monsterNortonUCompactColumnInner n a) 1024)

/-- This column-xor evaluator is the same actual inverse operator on every integer spin vector. -/
theorem monsterNortonUCompactColumnInverseNumerator_actual (v : NortonUIntegerVector) :
    monsterNortonUCompactInverseNumerator v = monsterNortonUCompactColumnInverseNumerator v := by
  rw [monsterNortonUCompactBitInverseNumerator_actual]
  funext n
  simp only [monsterNortonUCompactBitInverseNumerator, monsterNortonUCompactBitInner,
    monsterNortonUCompactRow_eq_column, monsterNortonUCompactColumnInverseNumerator,
    monsterNortonUCompactColumnInner]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
