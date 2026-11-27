/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # The Catalan recurrence from central binomial coefficients -/

namespace MetaMathlibExt

/-- Consecutive Catalan numbers satisfy $(n+2)C_{n+1}=2(2n+1)C_n$. -/
public theorem add_two_mul_catalan_succ (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1), ← succ_mul_catalan_eq_centralBinom n] at h
  apply mul_left_cancel₀ (by omega : n + 1 ≠ 0)
  simpa only [Nat.succ_eq_add_one, mul_assoc, mul_left_comm, mul_comm] using h

/-- The Catalan recurrence in ratio form in a field of characteristic zero. -/
public theorem cast_catalan_succ_eq {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (catalan (n + 1) : K) = (2 * (n : K) + 1) / (n + 2) * 2 * catalan n := by
  have h : ((n : K) + 2) * (catalan (n + 1) : K) = 2 * (2 * (n : K) + 1) * catalan n := by
    exact_mod_cast add_two_mul_catalan_succ n
  have hn : (n : K) + 2 ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  field_simp [hn]
  linear_combination h

end MetaMathlibExt
