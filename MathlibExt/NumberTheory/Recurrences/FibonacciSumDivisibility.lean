/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Int.Fib.Lemmas

/-!
# Pisano periods of Fibonacci numbers

For every even index `n > 1`, the Pisano period of `Nat.fib n` divides `2 * n`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

/-- **Pisano period.** For a natural number $n$, the Pisano period $\pi(n)$ is the minimal period
of the pair $(0, 1)$ under the Fibonacci step $(a, b) \mapsto (b, a + b)$ on
$\mathbb{Z}/n\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}$: the least $k \ge 1$ such that $k$
applications of the step map $(0, 1)$ back to $(0, 1)$, or $0$ if there is no such $k$ (as for
$n = 0$, where $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$). -/
noncomputable def pisanoPeriod (n : ℕ) : ℕ :=
  Function.minimalPeriod
    (fun p : ZMod n × ZMod n => (p.2, p.1 + p.2)) (0, 1)

private theorem iterate_fibStep (m k : ℕ) :
    (fun p : ZMod m × ZMod m => (p.2, p.1 + p.2))^[k] (0, 1) =
      ((Nat.fib k : ZMod m), (Nat.fib (k + 1) : ZMod m)) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, Nat.fib_add_two, Nat.cast_add]

/-- **The Pisano period of $F_n$ divides $2n$ for even $n$.** Let $F_n$ denote the $n$-th Fibonacci
number and $\pi(m)$ the Pisano period of $m$. For every even natural number $n > 1$, $\pi(F_n)$
divides $2n$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Proposition 2. -/
theorem pisanoPeriod_fib_dvd_two_mul
    (n : ℕ) (hn : 1 < n) (hn2 : 2 ∣ n) :
    pisanoPeriod (Nat.fib n) ∣ 2 * n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- Modulo F_{k+1}, the two neighbors are equal and Cassini gives their square.
  have cassini := Int.fib_succ_mul_fib_pred_sub_fib_sq ((k + 1 : ℕ) : ℤ)
  rw [Nat.cast_add_one, add_sub_cancel_right] at cassini
  change (Nat.fib (k + 2) : ℤ) * Nat.fib k - (Nat.fib (k + 1) : ℤ) ^ 2 =
    (-1) ^ (k + 1) at cassini
  rw [(even_iff_two_dvd.mpr hn2).neg_one_pow] at cassini
  have hmod := congrArg (Int.cast : ℤ → ZMod (Nat.fib (k + 1))) cassini
  simp [Nat.fib_add_two] at hmod
  apply Function.IsPeriodicPt.minimalPeriod_dvd
  unfold Function.IsPeriodicPt Function.IsFixedPt
  rw [iterate_fibStep, Nat.fib_two_mul, Nat.fib_two_mul_add_one]
  simp [Nat.fib_add_two, pow_two, hmod]

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted
