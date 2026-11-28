/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenLeonardo
import Mathlib.Tactic.LinearCombination

/-! # Tests for `MathlibExt.NumberTheory.GenLeonardo` -/

namespace MathlibExtTest.GenLeonardo

open MetaMathlibExt

-- Test section: values. For `k = 1` these are the Leonardo numbers.
example : (List.range 8).map (genLeonardo 1) = [1, 1, 3, 5, 9, 15, 25, 41] := by decide

-- For `k = 0` they are the Fibonacci numbers `F_{n+1}`.
example : (List.range 8).map (genLeonardo 0) = [1, 1, 2, 3, 5, 8, 13, 21] := by decide

-- For `k = -1` the sequence is constant, and for `k = -3` it takes negative values.
example : (List.range 8).map (genLeonardo (-1)) = [1, 1, 1, 1, 1, 1, 1, 1] := by decide

example : (List.range 6).map (genLeonardo (-3)) = [1, 1, -1, -3, -7, -13] := by decide

-- A negative parameter gives a zero term followed by a negative term.
example : genLeonardo (-2) 2 = 0 ∧ genLeonardo (-2) 3 = -1 := by decide

example : genLeonardoCompanion (-2) 0 = 3 ∧ genLeonardoCompanion (-2) 2 = 0 := by decide

-- Test section: the shift identity.
/-- The identity of `genLeonardo_shift`, without its hypotheses. -/
private abbrev ShiftIdentity (k : ℤ) (m n t : ℕ) : Prop :=
  genLeonardo k m * genLeonardo k n - genLeonardo k (m + t) * genLeonardo k (n - t)
    = (-1 : ℤ) ^ (n - t + 1) * (genLeonardo k (m + t - n - 1) + k) * (genLeonardo k (t - 1) + k)
      - k * (genLeonardo k m + genLeonardo k n - genLeonardo k (m + t) - genLeonardo k (n - t))

example (k : ℤ) (m n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) (hmt : n + 1 ≤ m + t) :
    ShiftIdentity k m n t :=
  genLeonardo_shift k m n t ht htn hmt

-- A numerical instance, `k = 2`, `m = 5`, `n = 4`, `t = 2`: both sides equal `42`.
example : genLeonardo 2 5 * genLeonardo 2 4 - genLeonardo 2 7 * genLeonardo 2 2 = 42 ∧
    ShiftIdentity 2 5 4 2 :=
  ⟨by decide, genLeonardo_shift 2 5 4 2 (by omega) (by omega) (by omega)⟩

-- In the extreme case `t = n`, `m = 1`, the identity reduces to the recurrence
-- `L_{k,n+1} = L_{k,n} + L_{k,n-1} + k`.
example (k : ℤ) (n : ℕ) (hn : 1 ≤ n) : ShiftIdentity k 1 n n :=
  genLeonardo_shift k 1 n n hn le_rfl (by omega)

-- With `m = n` and `t = 1` the identity is a Cassini-type identity.
example (k : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    genLeonardo k n ^ 2 - genLeonardo k (n + 1) * genLeonardo k (n - 1)
      = (-1) ^ n * (1 + k) ^ 2
        - k * (2 * genLeonardo k n - genLeonardo k (n + 1) - genLeonardo k (n - 1)) := by
  have h := genLeonardo_shift k n n 1 le_rfl hn le_rfl
  rw [Nat.sub_add_cancel hn, show n + 1 - n - 1 = 0 by omega, Nat.sub_self] at h
  have h0 : genLeonardo k 0 = 1 := rfl
  rw [h0] at h
  linear_combination h

-- Test section: no hypothesis can be dropped, because of truncated subtraction in `ℕ`.
-- Without `1 ≤ t`: at `t = 0`, `L_{k,t-1}` reads `L_{k,0}` instead of `L_{k,-1} = -k`.
example : ¬ ShiftIdentity 1 2 1 0 := by decide

-- Without `t ≤ n`.
example : ¬ ShiftIdentity 1 0 0 1 := by decide

-- Without `n + 1 ≤ m + t`.
example : ¬ ShiftIdentity 1 0 1 1 := by decide

-- The first admissible pair gives difference indices one and zero, respectively.
example (k : ℤ) :
    (genLeonardo k 3 ^ 2 - genLeonardo k 1 ^ 2 =
      (genLeonardo k 5 + k) * (genLeonardo k 1 + k) -
        2 * k * (genLeonardo k 3 - genLeonardo k 1)) ∧
    (genLeonardo k 3 ^ 2 + genLeonardo k 0 ^ 2 =
      (genLeonardo k 4 + k) * (genLeonardo k 2 + k) -
        2 * k * (genLeonardo k 3 + genLeonardo k 0) - 2 * k ^ 2) :=
  genLeonardo_sq_sum_diff k 2 1 (by decide) (by decide)

-- At k = 1, m = 3, n = 1, the corrected index gives 82 and the printed index gives 78.
example :
    genLeonardo 1 4 ^ 2 + genLeonardo 1 1 ^ 2 = 82 ∧
    (genLeonardo 1 6 + 1) * (genLeonardo 1 2 + 1) -
      2 * (genLeonardo 1 4 + genLeonardo 1 2) - 2 = 78 := by
  constructor
  · rw [(genLeonardo_sq_sum_diff 1 3 1 (by decide) (by decide)).2]
    decide
  · decide

-- Test section: the square-difference identity.
/-- The identity of `genLeonardo_sq_sub_sq`, without its hypothesis. -/
private abbrev SqSubSqIdentity (k : ℤ) (n : ℕ) : Prop :=
  genLeonardoCompanion k n ^ 2 - genLeonardo k n ^ 2
    = 4 * genLeonardo k (n - 1) * genLeonardo k (n + 1) + 2 * k * genLeonardo k n + k ^ 2

example (k : ℤ) (n : ℕ) (hn : 1 ≤ n) : SqSubSqIdentity k n :=
  genLeonardo_sq_sub_sq k n hn

-- A numerical instance, `k = 1`, `n = 4`: `M_{1,4} = 5 + 15 = 20`, and both sides equal `319`.
example : genLeonardoCompanion 1 4 = 20 ∧
    genLeonardoCompanion 1 4 ^ 2 - genLeonardo 1 4 ^ 2 = 319 ∧ SqSubSqIdentity 1 4 :=
  ⟨by decide, by decide, genLeonardo_sq_sub_sq 1 4 (by omega)⟩

-- A negative parameter, `k = -3`, `n = 3`.
example : SqSubSqIdentity (-3) 3 := genLeonardo_sq_sub_sq (-3) 3 (by omega)

-- The hypothesis `1 ≤ n` cannot be dropped: at `n = 0`, `L_{k,n-1}` reads `L_{k,0}`.
example : ¬ SqSubSqIdentity 1 0 := by decide

end MathlibExtTest.GenLeonardo
