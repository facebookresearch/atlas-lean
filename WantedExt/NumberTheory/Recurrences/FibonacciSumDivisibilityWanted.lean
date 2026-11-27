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
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibility
public import MathlibExt.NumberTheory.Recurrences.OddFibonacciSumDivisibility
public import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilitySumFibModPrimeEqAndNotDvd
public import MathlibExt.NumberTheory.Recurrences.PisanoPeriodMinRatio

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

/-- **Odd Fibonacci numbers $F_n$ with $F_{F_n + 2} \equiv 1 \pmod{F_n}$.** Let $F_m$ denote the
$m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. If $p$ is an odd prime with
$p \equiv 2 \pmod 3$ and $p \equiv 2$ or $3 \pmod 5$, and $n = 2p$ or $n = 4p$, then $F_n$ is odd
and $F_{F_n + 2}$ leaves remainder $1$ on division by $F_n$.

Source: Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci
Numbers",
Theorem 2. -/
theorem_wanted fib_two_mul_prime_odd_and_fib_fib_add_two_mod
    (p n : ℕ) (hp : p.Prime) (hpodd : p % 2 = 1)
    (hp3 : p % 3 = 2) (hp5 : p % 5 = 2 ∨ p % 5 = 3)
    (hn : n = 2 * p ∨ n = 4 * p) :
    Nat.fib n % 2 = 1 ∧
      Nat.fib (Nat.fib n + 2) % Nat.fib n = 1

end MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted
