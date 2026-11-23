/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
replace the source-specific partition-count alias with canonical cardinalities, narrow imports,
and keep the summation helper private.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

/-!
# A linear lower bound for integer partitions

This file proves an elementary lower bound for the number of integer partitions. The proof is
adapted from `eth/proof/rates/ClauseBound/Part/Bits.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace Nat.Partition

open Finset

private theorem gauss (n : ℕ) : n * (n + 1) ≤ 2 * ∑ v ∈ Icc 1 n, v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    nlinarith

/-- The number of partitions of `n` is at least `(n + 1) / 2`. -/
theorem succ_le_two_mul_card (n : ℕ) :
    n + 1 ≤ 2 * Fintype.card (Partition n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Fintype.card_unique]
  have hsum : ∑ v ∈ Icc 1 n, v ≤ n * Fintype.card (Partition n) := by
    rw [mul_card_eq_sum]
    refine sum_le_sum fun v hv => ?_
    have hv' := mem_Icc.mp hv
    have h1 : 1 ∈ Icc 1 (n / v) :=
      mem_Icc.mpr ⟨le_rfl, (Nat.le_div_iff_mul_le hv'.1).mpr (by omega)⟩
    calc
      v ≤ v * Fintype.card (Partition (n - 1 * v)) :=
        Nat.le_mul_of_pos_right _ Fintype.card_pos
      _ ≤ _ := single_le_sum (f := fun k =>
        v * Fintype.card (Partition (n - k * v))) (fun _ _ => Nat.zero_le _) h1
  have hgauss := gauss n
  have hmul : n * (n + 1) ≤ n * (2 * Fintype.card (Partition n)) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hmul hn

end Nat.Partition
