/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticLinearEquations
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

open MetaMathlibExt Finset

-- Minimum arity and colour count, on a noncyclic group with a negative coefficient.
example : IsUncommonOverFiniteGroup (ZMod 2 × ZMod 2) (![-3, 1, 5] : Fin 3 → ℤ) 3 := by
  apply isUncommonOverFiniteGroup_of_odd _ 1 (by decide) _ _ 3 (by decide)
  simp only [Fintype.card_prod, ZMod.card]
  decide

-- With one variable the sum over colours at each solution is exactly one.
example (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (a : Fin 1 → ℤ) (r : ℕ) :
    ¬ IsUncommonOverFiniteGroup G a r := by
  rintro ⟨w, -, hw, hlt⟩
  simp_rw [Fin.prod_univ_one] at hlt
  rw [sum_comm] at hlt
  simp [hw] at hlt
