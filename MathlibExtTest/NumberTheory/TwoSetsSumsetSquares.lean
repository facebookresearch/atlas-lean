/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.TwoSetsSumsetSquares
import Mathlib.Tactic.NormNum

/-! # Tests for integer families with square pairwise sums -/

open MathlibExt.NumberTheory.TwoSetsSumsetSquaresWanted

-- Choudhry's numerical example for (3.3), in the order of the parametrization.
example : PairwiseSumsSquares ![4, 484, 169] ![192, 0, (672 : ℤ)] :=
  pairwiseSumsSquares_triple_family33 5 3 2 1

-- Both negative entries in the second triple cancel an entry of the first.
example : PairwiseSumsSquares ![100, 36, 36] ![-36, 0, (-36 : ℤ)] := by
  have h := pairwiseSumsSquares_triple_family33 1 (-2) 2 1
  norm_num at h
  exact h

-- Four distinct entries in each family, including a negative summand.
example : PairwiseSumsSquares
    ![8850625, 21538881, 10400625, 68807025]
    ![0, 29440719, 50439375, (-7967025 : ℤ)] := by
  have h := pairwiseSumsSquares_quadruple_family51 1 (-2) 2 3
  norm_num at h
  exact h

-- When the two v parameters coincide, three entries in each family vanish.
example : PairwiseSumsSquares ![0, 576, 0, 0] ![0, (1024 : ℤ), 0, 0] :=
  pairwiseSumsSquares_quadruple_family51 1 2 1 1

-- A negative diagonal gives the same squared sum in every row and column.
example : IsSemiMagicRoots (fun i j ↦ if i = j then -2 else 0) := by
  refine ⟨4, ?_⟩
  decide
