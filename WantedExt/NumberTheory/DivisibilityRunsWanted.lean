/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.GeneralizedTribonacci
public import MathlibExt.NumberTheory.GibonacciNumber

namespace MetaMathlibExt

@[expose] public section

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
public def IsDivRunUpTo (x y a b c : ℤ) (L : ℕ) : Prop :=
  ∀ i : ℕ, i < L → gibonacciNumber x y i ≠ 0 ∧ gibonacciNumber x y i ∣ generalizedTribonacci a b c i

/-- **Divisibility runs of length zero.** For integers $x, y, a, b, c$, let $(P_n)_{n \ge 0}$ be
the Gibonacci sequence with $P_0 = x$ and $P_1 = y$, let $(Q_n)_{n \ge 0}$ be the generalized
Tribonacci sequence with $Q_0 = a$, $Q_1 = b$ and $Q_2 = c$, and say $(x, y; a, b, c)$ has a
divisibility run of length at least $L$ when $P_i \ne 0$ and $P_i \mid Q_i$ for every natural
number $i < L$. Then $(x, y; a, b, c)$ always has a divisibility run of length at least $0$, since
no natural number $i$ satisfies $i < 0$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1). -/
public theorem isDivRunUpTo_zero (x y a b c : ℤ) : IsDivRunUpTo x y a b c 0 :=
  fun i hi => (Nat.not_lt_zero i hi).elim

/-- **Gibonacci terms two apart have the gcd of the initial values.** Let $x, y$ be integers and
let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$. For every $n \ge 2$,
the nonnegative greatest common divisor of $P_n$ and $P_{n-2}$ equals that of $x$ and $y$:
$\gcd(P_n, P_{n-2}) = \gcd(x, y)$.

The paper indexes the sequence from $1$ and states this for $n \ge 3$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 2
(`integers-2026-A122-lem-2`). -/
public theorem_wanted int_gcd_gibonacciNumber_sub_two (x y : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    Int.gcd (gibonacciNumber x y n) (gibonacciNumber x y (n - 2)) = Int.gcd x y

/-- **Backward recurrence for Gibonacci numbers.** Let $x, y$ be integers and let
$(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$. For every $n \ge 3$,
$P_{n-1} = P_n - P_{n-2}$ and $P_{n-3} = P_n - 2 P_{n-2}$.

The paper indexes the sequence from $1$ and states these identities for $n \ge 4$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 3
(`integers-2026-A122-lem-3`). -/
public theorem_wanted gibonacciNumber_backward (x y : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    gibonacciNumber x y (n - 1) = gibonacciNumber x y n - gibonacciNumber x y (n - 2) ∧
    gibonacciNumber x y (n - 3) = gibonacciNumber x y n - 2 * gibonacciNumber x y (n - 2)

/-- **Gibonacci numbers in terms of Fibonacci numbers.** Let $x, y$ be integers, let
$(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and $P_1 = y$, and let $(F_n)_{n \ge 0}$
be the Fibonacci sequence with $F_0 = 0$ and $F_1 = 1$. For every $n \ge 1$,
$P_n = F_{n-1}\,x + F_n\,y$.

The paper indexes $P$ from $1$ and states this as $P_n = F_{n-2}\,x + F_{n-1}\,y$ for $n \ge 2$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 1
(`integers-2026-A122-prop-1`). -/
public theorem_wanted gibonacciNumber_eq_fib (x y : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    gibonacciNumber x y n = (Nat.fib (n - 1) : ℤ) * x + (Nat.fib n : ℤ) * y

/-- **Basis sequences for generalized Tribonacci sequences.** There are integer sequences
$(u_n)_{n \ge 0}$, $(v_n)_{n \ge 0}$ and $(w_n)_{n \ge 0}$, each satisfying the Tribonacci
recurrence $s_{n+3} = s_{n+2} + s_{n+1} + s_n$ for all $n \ge 0$, with initial values
$(u_0, u_1, u_2) = (1, 0, 0)$, $(v_0, v_1, v_2) = (0, 1, 0)$ and $(w_0, w_1, w_2) = (0, 0, 1)$,
such that for all integers $a, b, c$ and every $n \ge 0$ the $n$-th term of the generalized
Tribonacci sequence with initial values $a, b, c$ equals $u_n a + v_n b + w_n c$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 2
(`integers-2026-A122-prop-2`). -/
public theorem_wanted exists_generalizedTribonacci_basis :
    ∃ u v w : ℕ → ℤ,
      (∀ n, u (n + 3) = u (n + 2) + u (n + 1) + u n) ∧
      (∀ n, v (n + 3) = v (n + 2) + v (n + 1) + v n) ∧
      (∀ n, w (n + 3) = w (n + 2) + w (n + 1) + w n) ∧
      u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 0 ∧
      v 0 = 0 ∧ v 1 = 1 ∧ v 2 = 0 ∧
      w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 1 ∧
      ∀ a b c : ℤ, ∀ n : ℕ,
        generalizedTribonacci a b c n = u n * a + v n * b + w n * c

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
public theorem_wanted isDivRunUpTo_small (x y a b c : ℤ) :
    (IsDivRunUpTo x y a b c 1 ↔ x ≠ 0 ∧ x ∣ a) ∧
    (IsDivRunUpTo x y a b c 2 ↔ (x ≠ 0 ∧ x ∣ a) ∧ y ≠ 0 ∧ y ∣ b) ∧
    (IsDivRunUpTo x y a b c 3 ↔
      (x ≠ 0 ∧ x ∣ a) ∧ (y ≠ 0 ∧ y ∣ b) ∧ x + y ≠ 0 ∧ x + y ∣ c)

/-- **Divisibility by a Gibonacci sequence forces a Tribonacci sequence to vanish.** Let
$x, y, a, b, c$ be integers, let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$ and
$P_1 = y$, and let $(Q_n)_{n \ge 0}$ be the generalized Tribonacci sequence with $Q_0 = a$,
$Q_1 = b$ and $Q_2 = c$. If $P_n \ne 0$ and $P_n \mid Q_n$ for every $n \ge 0$, then $Q_n = 0$
for every $n \ge 0$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 1
(`integers-2026-A122-thm-1`). -/
public theorem_wanted generalizedTribonacci_eq_zero_of_dvd (x y a b c : ℤ)
    (hP : ∀ n : ℕ, gibonacciNumber x y n ≠ 0)
    (hdiv : ∀ n : ℕ, gibonacciNumber x y n ∣ generalizedTribonacci a b c n) :
    ∀ n : ℕ, generalizedTribonacci a b c n = 0


/-- **Growth bounds for Gibonacci and generalized Tribonacci sequences.** Let $\varphi$ be the
golden ratio. For integers $x, y$ let $(P_n)_{n \ge 0}$ be the Gibonacci sequence with $P_0 = x$
and $P_1 = y$, and for integers $a, b, c$ let $(Q_n)_{n \ge 0}$ be the generalized Tribonacci
sequence with $Q_0 = a$, $Q_1 = b$ and $Q_2 = c$. Then (i) for all integers $x, y$ and every
$n \ge 0$, $|P_n| \le (|x| + |y|)\,\varphi^n$; (ii) there are real constants $c_0 > 0$ and
$c_1 > 0$ such that for all integers $x, y$ with $(x, y) \ne (0, 0)$ and every $n \ge 0$ with
$c_1 (\log(|x| + |y|) + 1) \le n$, one has $c_0\,\varphi^{n+1} / (|x| + |y|) \le |P_n|$; and
(iii) for every real $\tau$ with $\tau^3 = \tau^2 + \tau + 1$, all integers $a, b, c$ and every
$n \ge 0$, $|Q_n| \le (|a| + |b| + |c|)\,\tau^n$.

The paper indexes both sequences from $1$, so its $n$-th terms are $P_{n-1}$ and $Q_{n-1}$ here.
It prints (ii) with the threshold "n large enough depending on $|x| + |y|$"; the logarithmic
threshold is the one the paper uses in its proof of Theorem 2.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Lemma 1
(`integers-2026-A122-lem-1`), with the threshold as used in the proof of Theorem 2. -/
public theorem_wanted gibonacci_generalizedTribonacci_growth_bounds :
    (∀ (x y : ℤ) (n : ℕ),
      |(gibonacciNumber x y n : ℝ)| ≤ (|(x : ℝ)| + |(y : ℝ)|) * Real.goldenRatio ^ n) ∧
    (∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ x y : ℤ, (x, y) ≠ (0, 0) →
      ∀ n : ℕ, c₁ * (Real.log (|(x : ℝ)| + |(y : ℝ)|) + 1) ≤ (n : ℝ) →
        c₀ * Real.goldenRatio ^ (n + 1) / (|(x : ℝ)| + |(y : ℝ)|)
          ≤ |(gibonacciNumber x y n : ℝ)|) ∧
    (∀ τ : ℝ, τ ^ 3 = τ ^ 2 + τ + 1 → ∀ (a b c : ℤ) (n : ℕ),
      |(generalizedTribonacci a b c n : ℝ)| ≤ (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) * τ ^ n)

/-- Run-length conditions are decidable (finitely many indices, integer divisibility).

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Equation (1). -/
public instance (x y a b c : ℤ) (L : ℕ) : Decidable (IsDivRunUpTo x y a b c L) := by
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
public def divRunCount (B r : ℕ) : ℕ :=
  ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
      Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter fun t =>
    (t.1, t.2.1) ≠ (0, 0) ∧ (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ≠ (0, 0, 0) ∧
      IsDivRunUpTo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 r).card

/-- **Run count at bound 1 and length 1.** Exactly $156$ integer tuples $(x, y, a, b, c)$ with
all entries in $\{-1, 0, 1\}$, $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ have a
divisibility run of length at least $1$; that is, $A_1(1) = 156$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4 (`integers-2026-A122-prop-4`). -/
public theorem divRunCount_one_one : divRunCount 1 1 = 156 := by
  decide +kernel

/-- **Divisibility runs have logarithmic length.** There is a real constant $C > 0$ such that for
every natural number $B \ge 2$, all integers $x, y, a, b, c \in [-B, B]$ with $(x, y) \ne (0, 0)$
and $(a, b, c) \ne (0, 0, 0)$, and every natural number $L$ such that $(x, y, a, b, c)$ has a
divisibility run of length at least $L$, we have $L \le C \log B$. Here a divisibility run of
length at least $L$ means that for every $i < L$ the Gibonacci number $P_i$ with $P_0 = x$,
$P_1 = y$ is nonzero and divides the generalized Tribonacci number $Q_i$ with $Q_0 = a$,
$Q_1 = b$, $Q_2 = c$.

In the paper's notation this is $E(B) \le C \log B$, where $E(B)$ is the maximal run length
over these configurations.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Theorem 2
(`integers-2026-A122-thm-2`). -/
public theorem_wanted divRun_length_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B → ∀ x y a b c : ℤ,
      x ∈ Set.Icc (-(B : ℤ)) B → y ∈ Set.Icc (-(B : ℤ)) B → a ∈ Set.Icc (-(B : ℤ)) B →
      b ∈ Set.Icc (-(B : ℤ)) B → c ∈ Set.Icc (-(B : ℤ)) B →
      (x, y) ≠ (0, 0) → (a, b, c) ≠ (0, 0, 0) →
      ∀ L : ℕ, IsDivRunUpTo x y a b c L → (L : ℝ) ≤ C * Real.log B

/-- **Exact formula for the length-one run count.** For every natural number $B$, let
$D(B) = \sum_{m=1}^{B} \lfloor B/m \rfloor$ and let $A_B(1)$ be the number of integer tuples
$(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have
a divisibility run of length at least $1$. Then
$$A_B(1) = 4(2B+1)^3 D(B) + 2B(2B+1)\left((2B+1)^2 - 1\right).$$

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem_wanted divRunCount_one (B : ℕ) :
    divRunCount B 1 = 4 * (2 * B + 1) ^ 3 * ∑ m ∈ Finset.Icc 1 B, B / m
      + 2 * B * (2 * B + 1) * ((2 * B + 1) ^ 2 - 1)

/-- **Asymptotics of the length-one run count.** There is a real constant $K$ such that for every
natural number $B \ge 2$ the number $A_B(1)$ of integer tuples $(x, y, a, b, c) \in [-B, B]^5$
with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at
least $1$ satisfies $|A_B(1) - 32 B^4 \log B| \le K B^4$; that is,
$A_B(1) = 32 B^4 \log B + O(B^4)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem_wanted divRunCount_one_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 1 : ℝ) - 32 * (B : ℝ) ^ 4 * Real.log B| ≤ K * (B : ℝ) ^ 4

/-- **Exact formula for the length-two run count.** For every natural number $B$, let
$S(B) = \sum_{m=1}^{B} \left(2\lfloor B/m \rfloor + 1\right)$ and let $A_B(2)$ be the number of
integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $2$. Then
$S(B) = 2 \sum_{m=1}^{B} \lfloor B/m \rfloor + B$ and $A_B(2) = 4(2B+1) S(B)^2 - 4B^2$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`). -/
public theorem_wanted divRunCount_two (B : ℕ) :
    ∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) = 2 * ∑ m ∈ Finset.Icc 1 B, B / m + B ∧
      (divRunCount B 2 : ℤ)
        = 4 * (2 * B + 1) * (∑ m ∈ Finset.Icc 1 B, (2 * (B / m) + 1) : ℕ) ^ 2 - 4 * B ^ 2

/-- **Asymptotics of the length-two run count.** There is a real constant $K$ such that for every
natural number $B \ge 2$ the number $A_B(2)$ of integer tuples $(x, y, a, b, c) \in [-B, B]^5$
with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at
least $2$ satisfies $|A_B(2) - 32 B^3 (\log B)^2| \le K B^3 \log B$; that is,
$A_B(2) = 32 B^3 (\log B)^2 + O(B^3 \log B)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 5
(`integers-2026-A122-prop-5`). -/
public theorem_wanted divRunCount_two_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 2 : ℝ) - 32 * (B : ℝ) ^ 3 * Real.log B ^ 2|
        ≤ K * (B : ℝ) ^ 3 * Real.log B

/-- **Exact formula for the length-three run count.** For a natural number $B$, let $A_B(3)$ be
the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $3$, and for integers
$m \ge 1$ let $d_B(m) = 2\lfloor B/m \rfloor + 1$. Then
$$A_B(3) = \sum_{x, y} \left(d_B(|x|)\, d_B(|y|)\, d_B(|x+y|) - 1\right),$$
where the sum runs over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$ and
$x + y \ne 0$, and also
$$
A_B(3) = 2 \sum_{m=1}^{B} \sum_{n=1}^{B} d_B(m)\, d_B(n)\, d_B(m+n) +
4 \sum_{1 \le n < m \le B} d_B(m)\, d_B(n)\, d_B(m-n) - (4B^2 - 2B).
$$

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 6
(`integers-2026-A122-prop-6`). -/
public theorem_wanted divRunCount_three (B : ℕ) :
    ((divRunCount B 3 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 then
              ((2 * (B / x.natAbs) + 1) * (2 * (B / y.natAbs) + 1)
                * (2 * (B / (x + y).natAbs) + 1) - 1 : ℕ)
            else 0) ∧
    (divRunCount B 3 : ℤ)
        = 2 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m + n)) + 1) : ℕ)
          + 4 * ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Ico 1 m,
            ((2 * (B / m) + 1) * (2 * (B / n) + 1) * (2 * (B / (m - n)) + 1) : ℕ)
          - (4 * B ^ 2 - 2 * B)

/-- **Divisor-sum formula for the length-four run count.** For a natural number $B$, let $A_B(4)$
be the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $4$. For integers $x, y$
let $T_B(x, y)$ be the number of integer triples $(a, b, c) \in [-B, B]^3$ with $x \mid a$,
$y \mid b$, $x + y \mid c$ and $x + 2y \mid a + b + c$, and let $T'_B(x, y)$ be the number of
integer triples $(\alpha, \beta, \gamma)$ with $|\alpha| \le \lfloor B/|x| \rfloor$,
$|\beta| \le \lfloor B/|y| \rfloor$, $|\gamma| \le \lfloor B/|x+y| \rfloor$ and
$x + 2y \mid x\alpha + y\beta + (x+y)\gamma$. Then
$$A_B(4) = \sum_{x, y} \left(T_B(x, y) - 1\right) = \sum_{x, y} \left(T'_B(x, y) - 1\right),$$
where both sums run over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$, $x + y \ne 0$
and $x + 2y \ne 0$.

The second form comes from writing $a = x\alpha$, $b = y\beta$, $c = (x+y)\gamma$; it is the
paper's $\sum \chi_{x,y}(\alpha, \beta, \gamma)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 7
(`integers-2026-A122-prop-7`). -/
public theorem_wanted divRunCount_four (B : ℕ) :
    ((divRunCount B 4 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
              (((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ
                  Finset.Icc (-(B : ℤ)) B).filter fun t =>
                    x ∣ t.1 ∧ y ∣ t.2.1 ∧ x + y ∣ t.2.2 ∧
                      x + 2 * y ∣ t.1 + t.2.1 + t.2.2).card : ℤ) - 1
            else 0) ∧
    (divRunCount B 4 : ℤ)
        = ∑ x ∈ Finset.Icc (-(B : ℤ)) B, ∑ y ∈ Finset.Icc (-(B : ℤ)) B,
            if x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 ∧ x + 2 * y ≠ 0 then
              (((Finset.Icc (-((B / x.natAbs : ℕ) : ℤ)) (B / x.natAbs : ℕ) ×ˢ
                  Finset.Icc (-((B / y.natAbs : ℕ) : ℤ)) (B / y.natAbs : ℕ) ×ˢ
                  Finset.Icc (-((B / (x + y).natAbs : ℕ) : ℤ)) (B / (x + y).natAbs : ℕ)).filter
                    fun t => x + 2 * y ∣ x * t.1 + y * t.2.1 + (x + y) * t.2.2).card : ℤ) - 1
            else 0

end

end MetaMathlibExt
