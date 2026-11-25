/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Cube solutions of the Nagell–Ljunggren equation modulo nine

For exponents congruent to five modulo six, the equation has no integer solution
with base congruent to two, three, five, or six modulo nine.
-/

namespace MetaMathlibExt

/-- **The Nagell–Ljunggren cube equation for $n \equiv 5 \pmod 6$.** Let $n$ be a natural
number with $n \equiv 5 \pmod 6$. Then there are no integers $x$ and $y$ with
$x \equiv 2, 3, 5$ or $6 \pmod 9$ such that $x^n - 1 = (x - 1) y^3$. Since such an $x$ is not
$1$, this says that $(x^n - 1)/(x - 1) = y^3$ has no such integer solution.

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Theorem 2 (`integers-2026-A104-thm-2`). -/
public theorem nagell_ljunggren_cube_no_solution_of_mod_six_eq_five (n : ℕ)
    (hn : n % 6 = 5) (x y : ℤ) (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6) :
    x ^ n - 1 ≠ (x - 1) * y ^ 3 := by
  have period (a : ZMod 9) (k : ℕ) : a ^ (6 * k + 5) = a ^ 5 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 6 * (k + 1) + 5 = (6 * k + 5) + 6 by omega, pow_add, ih]
      exact (by decide : ∀ r : ZMod 9, r ^ 5 * r ^ 6 = r ^ 5) a
  have obstruction : ∀ a b : ZMod 9, (a = 2 ∨ a = 3 ∨ a = 5 ∨ a = 6) →
      a ^ 5 - 1 ≠ (a - 1) * b ^ 3 := by decide
  have hx' : (x : ZMod 9) = 2 ∨ (x : ZMod 9) = 3 ∨ (x : ZMod 9) = 5 ∨ (x : ZMod 9) = 6 := by
    rw [← ZMod.intCast_mod x 9]
    rcases hx with h | h | h | h <;> simp [h]
  intro heq
  have hmod := congrArg (fun z : ℤ => (z : ZMod 9)) heq
  push_cast at hmod
  rw [show n = 6 * (n / 6) + 5 by omega, period] at hmod
  exact obstruction x y hx' hmod

end MetaMathlibExt
