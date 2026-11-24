/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree

/-!
# Tests for common divisors of coconut tree leaf labels
-/

open MetaMathlibExt

-- The leaf labels 2, 3, 3 have collective gcd one even though two coincide.
example {g : ℕ} (h₂ : g ∣ 2) (h₃ : g ∣ 3) : g = 1 := by
  let d : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun _ => 2) ![3, 2, 2]
  let r : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim ![2, 4, 6] ![2, 3, 3]
  have h : IsSmoothCoconut 3 3 d r := by
    refine ⟨⟨by decide, by decide, ?_, ?_⟩, by decide, by decide⟩
    · intro v
      classical
      rw [finsum_mem_def, finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
      rcases v with i | i <;> fin_cases i <;>
        simp [Fin.sum_univ_three, Set.indicator_apply, coconutTree, SimpleGraph.fromRel_adj, d, r]
    · intro k hk
      have hd : k ∣ Nat.gcd 2 3 := Nat.dvd_gcd (hk (.inl 0)) (hk (.inr 1))
      exact Nat.dvd_one.mp hd
  apply h.eq_one_of_dvd_leaves
  intro j
  fin_cases j <;> first | exact h₂ | exact h₃

-- With no leaves, a smooth structure would make zero equal to one.
example {p : ℕ} {d r : Fin p ⊕ Fin 0 → ℕ} : ¬ IsSmoothCoconut p 0 d r := by
  intro h
  exact Nat.zero_ne_one (h.eq_one_of_dvd_leaves (g := 0) fun j => Fin.elim0 j)
