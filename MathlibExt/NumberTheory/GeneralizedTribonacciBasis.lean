/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedTribonacci
import Mathlib.Tactic.Ring

/-!
# Basis sequences for generalized Tribonacci sequences

Every generalized Tribonacci sequence is a linear combination of the three sequences
whose initial values are the coordinate vectors.
-/

public section

namespace MetaMathlibExt

/-- **Basis sequences for generalized Tribonacci sequences.** There are integer sequences
$(u_n)_{n \ge 0}$, $(v_n)_{n \ge 0}$ and $(w_n)_{n \ge 0}$, each satisfying the Tribonacci
recurrence $s_{n+3} = s_{n+2} + s_{n+1} + s_n$ for all $n \ge 0$, with initial values
$(u_0, u_1, u_2) = (1, 0, 0)$, $(v_0, v_1, v_2) = (0, 1, 0)$ and $(w_0, w_1, w_2) = (0, 0, 1)$,
such that for all integers $a, b, c$ and every $n \ge 0$ the $n$-th term of the generalized
Tribonacci sequence with initial values $a, b, c$ equals $u_n a + v_n b + w_n c$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 2
(`integers-2026-A122-prop-2`). -/
theorem exists_generalizedTribonacci_basis :
    ∃ u v w : ℕ → ℤ,
      (∀ n, u (n + 3) = u (n + 2) + u (n + 1) + u n) ∧
      (∀ n, v (n + 3) = v (n + 2) + v (n + 1) + v n) ∧
      (∀ n, w (n + 3) = w (n + 2) + w (n + 1) + w n) ∧
      u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0 ∧
      v 0 = 0 ∧ v 1 = 1 ∧ v 2 = 0 ∧
      w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 1 ∧
      ∀ a b c : ℤ, ∀ n : ℕ,
        generalizedTribonacci a b c n = u n * a + v n * b + w n * c := by
  refine ⟨generalizedTribonacci 1 0 0, generalizedTribonacci 0 1 0,
    generalizedTribonacci 0 0 1, generalizedTribonacci_add_three 1 0 0,
    generalizedTribonacci_add_three 0 1 0, generalizedTribonacci_add_three 0 0 1,
    rfl, rfl, rfl,
    rfl, rfl, rfl,
    rfl, rfl, rfl, ?_⟩
  intro a b c n
  induction n using generalizedTribonacci.induct with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 n ih₂ ih₁ ih₀ =>
    simp only [generalizedTribonacci_add_three, ih₂, ih₁, ih₀]
    ring

end MetaMathlibExt
