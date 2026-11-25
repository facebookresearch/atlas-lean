/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Enumerative.NColorCompositionBinomialSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Tests for the binomial sum for compositions with colors 1 and 2 -/

open MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

example : ccoAllowed 1 1 = 1 := by
  rw [ccoAllowed_one_eq_sum (n := 1) (hn := by decide)]
  decide

example : ccoAllowed 1 2 = 3 := by
  rw [ccoAllowed_one_eq_sum (n := 2) (hn := by decide)]
  decide

example : ccoAllowed 1 3 = 7 := by
  rw [ccoAllowed_one_eq_sum (n := 3) (hn := by decide)]
  decide

example : ccoAllowed 1 4 = 17 := by
  rw [ccoAllowed_one_eq_sum (n := 4) (hn := by decide)]
  decide

-- Color 2 is legal for a part of size 2, but not for a singleton.
example : ∃ p : ColorCompAllowed 1 2, p.val = [(2, 2)] := by
  exact ⟨⟨[(2, 2)], by simp⟩, rfl⟩

example (p : ColorCompAllowed 1 1) : p.val ≠ [(1, 2)] := by
  intro h
  have hp := (p.property.1 (1, 2) (by simp [h])).2.1
  exact (by decide : ¬ 2 ≤ 1) hp
