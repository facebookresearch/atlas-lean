/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.Interval
public import MathlibExt.NumberTheory.GeneralizedTribonacci
public import MathlibExt.NumberTheory.GibonacciNumber

/-!
# Divisibility runs between recurrence sequences

The Gibonacci recurrence preserves the gcd of adjacent terms and of terms two apart, and run
backwards it recovers $P_{n-1}$ and $P_{n-3}$ from $P_n$ and $P_{n-2}$.
During a divisibility run, every Gibonacci term in the initial segment is nonzero and divides
the corresponding generalized Tribonacci term.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Gibonacci terms two apart have the gcd of the initial values.** Let $x, y$ be integers and
let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$. For every $n \ge 2$,
the nonnegative greatest common divisor of $P_n$ and $P_{n-2}$ equals that of $x$ and $y$:
$\gcd(P_n, P_{n-2}) = \gcd(x, y)$.

The paper indexes the sequence from $1$ and states this for $n \ge 3$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 2
(`integers-2026-A122-lem-2`). -/
theorem int_gcd_gibonacciNumber_sub_two (x y : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber x y n) (gibonacciNumber x y (n - 2)) = Int.gcd x y := by
  have adjacent (k : ℕ) :
      Int.gcd (gibonacciNumber x y (k + 1)) (gibonacciNumber x y k) = Int.gcd x y := by
    induction k with
    | zero => exact Int.gcd_comm y x
    | succ k ih =>
      rw [gibonacciNumber, Int.gcd_self_add_left, Int.gcd_comm]
      exact ih
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel, gibonacciNumber, Int.gcd_add_self_left]
  exact adjacent k

/-- **Backward recurrence for Gibonacci numbers.** Let $x, y$ be integers and let
$(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$. For every $n \ge 3$,
$P_{n-1} = P_n - P_{n-2}$ and $P_{n-3} = P_n - 2 P_{n-2}$.

The paper indexes the sequence from $1$ and states these identities for $n \ge 4$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 3
(`integers-2026-A122-lem-3`). -/
theorem gibonacciNumber_backward (x y : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    gibonacciNumber x y (n - 1) = gibonacciNumber x y n - gibonacciNumber x y (n - 2) ∧
    gibonacciNumber x y (n - 3) = gibonacciNumber x y n - 2 * gibonacciNumber x y (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, Nat.add_sub_cancel]
  -- Two steps of the forward recurrence give `P (k + 3) = 2 P (k + 1) + P k`.
  have h₃ : gibonacciNumber x y (k + 3) =
      gibonacciNumber x y (k + 2) + gibonacciNumber x y (k + 1) := rfl
  have h₂ : gibonacciNumber x y (k + 2) =
      gibonacciNumber x y (k + 1) + gibonacciNumber x y k := rfl
  omega

/-- **Divisibility runs.** For integers $x, y, a, b, c$ and a natural number $L$, let
$(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$, and let $(Q_n)_{n \ge 0}$
be the generalized Tribonacci sequence with $Q_0 = a$, $Q_1 = b$ and $Q_2 = c$. The configuration
$(x, y; a, b, c)$ has a divisibility run of length at least $L$ when $P_i \ne 0$ and
$P_i \mid Q_i$ for every $i < L$.

This is the statement that the run length $L(x, y; a, b, c)$ of the paper's Equation (1) is at
least $L$; the paper indexes the sequences from $1$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1) and
Proposition 3. -/
def IsDivRunUpTo (x y a b c : ℤ) (L : ℕ) : Prop :=
  ∀ i : ℕ, i < L → gibonacciNumber x y i ≠ 0 ∧ gibonacciNumber x y i ∣ generalizedTribonacci a b c i

/-- **Divisibility runs of length zero.** For integers $x, y, a, b, c$, let $(P_n)_{n \ge 0}$ be
the Gibonacci sequence with $P_0 = x$ and $P_1 = y$, let $(Q_n)_{n \ge 0}$ be the generalized
Tribonacci sequence with $Q_0 = a$, $Q_1 = b$ and $Q_2 = c$, and say $(x, y; a, b, c)$ has a
divisibility run of length at least $L$ when $P_i \ne 0$ and $P_i \mid Q_i$ for every natural
number $i < L$. Then $(x, y; a, b, c)$ always has a divisibility run of length at least $0$, since
no natural number $i$ satisfies $i < 0$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1). -/
theorem isDivRunUpTo_zero (x y a b c : ℤ) : IsDivRunUpTo x y a b c 0 :=
  fun i hi => (Nat.not_lt_zero i hi).elim

/-- **Divisibility runs of length one, two and three.** For integers $x, y, a, b, c$, let $(P_n)$
be the Gibonacci sequence with $P_0 = x$, $P_1 = y$ and $(Q_n)$ the generalized Tribonacci sequence
with $Q_0 = a$, $Q_1 = b$, $Q_2 = c$, and say $(x, y; a, b, c)$ has a divisibility run of length at
least $L$ when $P_i \ne 0$ and $P_i \mid Q_i$ for every $i < L$. Then there is a run of length at
least $1$ if and only if $x \ne 0$ and $x \mid a$; a run of length at least $2$ if and only if
$x \ne 0$, $x \mid a$, $y \ne 0$ and $y \mid b$; and a run of length at least $3$ if and only if
$x \ne 0$, $x \mid a$, $y \ne 0$, $y \mid b$, $x + y \ne 0$ and $x + y \mid c$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 3
(`integers-2026-A122-prop-3`). -/
theorem isDivRunUpTo_small (x y a b c : ℤ) :
    (IsDivRunUpTo x y a b c 1 ↔ x ≠ 0 ∧ x ∣ a) ∧
    (IsDivRunUpTo x y a b c 2 ↔ (x ≠ 0 ∧ x ∣ a) ∧ y ≠ 0 ∧ y ∣ b) ∧
    (IsDivRunUpTo x y a b c 3 ↔
      (x ≠ 0 ∧ x ∣ a) ∧ (y ≠ 0 ∧ y ∣ b) ∧ x + y ≠ 0 ∧ x + y ∣ c) := by
  simp [IsDivRunUpTo, Nat.forall_lt_succ_right, gibonacciNumber, add_comm y x, and_assoc]

/-- Run-length conditions are decidable (finitely many indices, integer divisibility).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1). -/
instance instDecidableIsDivRunUpTo (x y a b c : ℤ) (L : ℕ) :
    Decidable (IsDivRunUpTo x y a b c L) := by
  unfold IsDivRunUpTo
  infer_instance

/-- **Counting configurations with long divisibility runs.** For natural numbers $B$ and $r$,
$A_B(r)$ is the number of integer tuples $(x, y, a, b, c)$ with all five entries in $[-B, B]$,
$(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at
least $r$: for every $i < r$, the Gibonacci number $P_i$ with initial values $P_0 = x$, $P_1 = y$
is nonzero and divides the generalized Tribonacci number $Q_i$ with initial values $Q_0 = a$,
$Q_1 = b$, $Q_2 = c$ (indices start at $0$).

The tuples satisfying the size and nonvanishing conditions form the paper's set
$\mathcal{C}_B$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (2). -/
def divRunCount (B r : ℕ) : ℕ :=
  ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
      Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter fun t =>
    (t.1, t.2.1) ≠ (0, 0) ∧ (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ≠ (0, 0, 0) ∧
      IsDivRunUpTo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 r).card

/-- **Run count at bound 1 and length 1.** Exactly $156$ integer tuples $(x, y, a, b, c)$ with
all entries in $\{-1, 0, 1\}$, $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ have a
divisibility run of length at least $1$; that is, $A_1(1) = 156$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
theorem divRunCount_one_one : divRunCount 1 1 = 156 := by
  decide +kernel

end MetaMathlibExt
