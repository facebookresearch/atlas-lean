/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.SophieGermainChainFermatCongruence

open MetaMathlibExt

-- The initial pair can start at the even prime.
example (a : ℤ) (ha : IsCoprime a 10) :
    a ^ 4 ≡ 5 * a ^ 3 - 4 [ZMOD 10] ∧
      5 * a ^ 1 ≡ 2 * a ^ 4 + 2 + 1 [ZMOD 10] := by
  refine sophieGermainChain_fermat_congruence (p := 2) (j := 0) ?_ a ha
  intro i hi
  interval_cases i <;> decide

-- At the next pair, 5 and 11, the base can be negative.
example : (-2 : ℤ) ^ 10 ≡ 11 * (-2) ^ 6 - 10 [ZMOD 55] ∧
    11 * (-2) ^ 4 ≡ 5 * (-2) ^ 10 + 5 + 1 [ZMOD 55] := by
  refine sophieGermainChain_fermat_congruence (p := 2) (j := 1) ?_ (-2) ?_
  · intro i hi
    interval_cases i <;> decide
  · exact ⟨27, 1, by decide⟩
