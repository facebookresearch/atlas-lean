/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the divisibility of sums of Fibonacci numbers

Statements from Oisín Flynn-Connolly, "On the Divisibility
of Sums of Fibonacci Numbers", *INTEGERS* 25 (2025), Article A87
(<https://math.colgate.edu/~integers/z87/z87.pdf>).

The paper's Proposition 1, `S n = F (n + 2) - 1`, is already
Mathlib's `Nat.fib_succ_eq_succ_sum`, so it is not re-requested
here.  The Pisano period is the minimal period of the Fibonacci
pair step on `ZMod n × ZMod n` at `(0, 1)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

/-- The Pisano period of `n`: the minimal period of `(0, 1)` under
the Fibonacci pair step `(a, b) ↦ (b, a + b)` on
`ZMod n × ZMod n`. -/
noncomputable def pisanoPeriod (n : ℕ) : ℕ :=
  Function.minimalPeriod
    (fun p : ZMod n × ZMod n => (p.2, p.1 + p.2)) (0, 1)

/-- The paper's Proposition 2: for even `n > 1`, the Pisano
period of `Nat.fib n` divides `2 * n`.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Proposition 2. -/
theorem_wanted pisanoPeriod_fib_dvd_two_mul
    (n : ℕ) (hn : 1 < n) (hn2 : 2 ∣ n) :
    pisanoPeriod (Nat.fib n) ∣ 2 * n

/-- The paper's Corollary 1: the minimum of `π(n) / n` over
positive `n < N` tends to `0` as `N` tends to infinity. The
finite minimum is written as an infimum indexed by the subtype
of elements of `Finset.Icc 1 (N - 1)`, so out-of-range indices
do not contribute an empty infimum.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Corollary 1. -/
theorem_wanted tendsto_iInf_pisanoPeriod_div_atTop
    :
    Filter.Tendsto
      (fun N : ℕ =>
        ⨅ n : {n : ℕ // n ∈ Finset.Icc 1 (N - 1)},
          (pisanoPeriod n.1 : ℝ) / n.1)
      Filter.atTop (nhds 0)

/-- The paper's Theorem 1: for a prime `p > 5`, the sum of the
first `p` Fibonacci numbers is `1` modulo `p` when
`p % 5 = 1` or `4`, is `p - 2` modulo `p` when `p % 5 = 2` or
`3`, and in particular is not divisible by `p`. These are the
residues forced by the paper's Binet-formula computation.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 1. -/
theorem_wanted sum_fib_mod_prime_eq_and_not_dvd
    (p : ℕ) (hp : p.Prime) (hp5 : 5 < p) :
    ((p % 5 = 1 ∨ p % 5 = 4) →
        (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = 1) ∧
      ((p % 5 = 2 ∨ p % 5 = 3) →
        (∑ i ∈ Finset.Icc 1 p, Nat.fib i) % p = p - 2) ∧
      ¬p ∣ (∑ i ∈ Finset.Icc 1 p, Nat.fib i)

/-- The paper's Theorem 2: if `p` is an odd prime with
`p % 3 = 2` and `p % 5 = 2` or `3`, and `n = 2 * p` or
`n = 4 * p`, then `Nat.fib n` is odd and
`Nat.fib (Nat.fib n + 2) ≡ 1` modulo `Nat.fib n`.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 2. -/
theorem_wanted fib_two_mul_prime_odd_and_fib_fib_add_two_mod
    (p n : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
    (hp3 : p % 3 = 2) (hp5 : p % 5 = 2 ∨ p % 5 = 3)
    (hn : n = 2 * p ∨ n = 4 * p) :
    Nat.fib n % 2 = 1 ∧
      Nat.fib (Nat.fib n + 2) % Nat.fib n = 1

/-- The paper's Corollary 2: there are infinitely many odd
positive integers `k` dividing the sum of the first `k`
Fibonacci numbers.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Corollary 2. -/
theorem_wanted infinite_setOf_odd_dvd_sum_fib
    :
    {k : ℕ | Odd k ∧ k ∣ (∑ i ∈ Finset.Icc 1 k, Nat.fib i)}.Infinite

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted
