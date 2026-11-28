/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.InfiniteWord.ThueMorseFactors

open MetaMathlibExt

-- The complement of the initial factor 01 is the factor 10.
example : (fun i : Fin 2 => decide (i.val = 0)) ∈ InfiniteWord.factorSet thueMorse 2 := by
  have h : InfiniteWord.factor thueMorse 2 0 ∈ InfiniteWord.factorSet thueMorse 2 := ⟨0, rfl⟩
  have h' := thueMorse_factor_complement 2 _ h
  have he : (fun i => !(InfiniteWord.factor thueMorse 2 0 i)) =
      (fun i : Fin 2 => decide (i.val = 0)) := by
    funext i
    fin_cases i <;> decide
  exact he ▸ h'

-- The empty factor is also covered.
example : (fun i => !(InfiniteWord.factor thueMorse 0 0 i)) ∈
    InfiniteWord.factorSet thueMorse 0 :=
  thueMorse_factor_complement 0 _ ⟨0, rfl⟩
