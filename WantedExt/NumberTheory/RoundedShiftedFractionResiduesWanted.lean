/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- **Floor sequence parity count.** For a natural number $n$, the floor sequence parity count
$\mathcal{F}_n$ is the number of integers $k$ with $1 \le k \le n$ for which
$\lfloor n/k \rfloor$ is odd (OEIS A059851).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓕_n`). -/
public def floorQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Odd (n / k))).card

/-- **The floor sequence parity count at $10$.** The number $\mathcal{F}_{10}$ of integers $k$
with $1 \le k \le 10$ for which $\lfloor 10/k \rfloor$ is odd equals $7$: the quotients
$\lfloor 10/k \rfloor$ for $k = 1, \dots, 10$ are $10, 5, 3, 2, 2, 1, 1, 1, 1, 1$, and seven of
them are odd.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 and Figure 1. -/
public theorem floorQuotientOddCount_ten : floorQuotientOddCount 10 = 7 := by
  decide

/-- **Ceiling parity count.** For a natural number $n$, the ceiling parity count $\mathcal{C}_n$
is the number of integers $k$ with $1 \le k \le n$ for which $\lceil n/k \rceil$ is odd
(OEIS A330926).

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓒_n`). -/
public def ceilQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => Odd ⌈(n : ℚ) / (k : ℚ)⌉)).card

/-- **The ceiling parity count at $9$.** The ceiling parity count $\mathcal{C}_9$, the number of
integers $k$ with $1 \le k \le 9$ for which $\lceil 9/k \rceil$ is odd, equals $5$.

The ceilings $\lceil 9/k \rceil$ for $k = 1, \dots, 9$ are $9, 5, 3, 3, 2, 2, 2, 2, 1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Figure 1. -/
public theorem ceilQuotientOddCount_nine : ceilQuotientOddCount 9 = 5 := by
  decide +kernel

/-- **Rounding sequence parity count.** For a natural number $n$, the rounding sequence parity
count $\mathcal R_n$ is the number of integers $k$ with $1 \le k \le n$ for which the nearest
integer to $n/k$ is odd, where half-integers are rounded up: the nearest integer to a rational
number $x$ is taken to be $\lfloor x + 1/2 \rfloor$.

Rounding half-integers up is the paper's convention for $\mathrm{nint}$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 1 (definition of `𝓡_n` and the footnote on `nint`). -/
public def roundQuotientOddCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k : ℕ => Odd (round ((n : ℚ) / (k : ℚ))))).card

/-- **The rounding sequence parity count at $10$.** The number $\mathcal{R}_{10}$ of integers $k$
with $1 \le k \le 10$ for which the nearest integer to $10/k$ (half-integers rounded up) is odd
equals $7$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Figure 1. -/
public theorem roundQuotientOddCount_ten : roundQuotientOddCount 10 = 7 := by
  decide +kernel

/-- **Residue counts of the shifted floor sequence.** For a natural number $n$, real numbers
$\alpha$ and $\nu$, an integer $r$ and a natural number $m$, the count
$\mathcal N_{n,\alpha,\nu,r,m}$ is the number of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$. In other words, it counts the terms of
the $\alpha$-shifted, $\nu$-offset floor sequence
$\lfloor (n - \nu)/1 + \alpha \rfloor, \dots, \lfloor (n - \nu)/n + \alpha \rfloor$ that are
congruent to $r$ modulo $m$, where congruence modulo $0$ means equality.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 4 (definition of `𝓝_{n,α,ν,r,m}`). -/
public noncomputable def shiftedFloorResidueCount (n : ℕ) (α ν : ℝ) (r : ℤ)
    (m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter
    (fun k : ℕ => ⌊((n : ℝ) - ν) / (k : ℝ) + α⌋ ≡ r [ZMOD m])).card

/-- **Every term is counted modulo one.** For a natural number $n$, real numbers $\alpha$ and
$\nu$, an integer $r$ and a natural number $m$, let $\mathcal N_{n,\alpha,\nu,r,m}$ be the number
of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$. Then $\mathcal N_{n,\alpha,\nu,r,1} = n$
for every natural number $n$, all real numbers $\alpha$ and $\nu$ and every integer $r$.

This is the remark after equation (4.2) of the paper.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Section 4. -/
public theorem shiftedFloorResidueCount_modulus_one (n : ℕ) (α ν : ℝ)
    (r : ℤ) : shiftedFloorResidueCount n α ν r 1 = n := by
  unfold shiftedFloorResidueCount
  rw [Finset.filter_true_of_mem (fun k _ => by simp [Int.ModEq])]
  simp

/-- **Counting large terms of the floor sequence.** For every natural number $n$ and every
integer $k \ge 1$, exactly $\lfloor n/k \rfloor$ of the integers $d$ with $1 \le d \le n$
satisfy $\lfloor n/d \rfloor \ge k$; that is, exactly $\lfloor n/k \rfloor$ terms of the floor
sequence $\lfloor n/1 \rfloor, \dots, \lfloor n/n \rfloor$ are at least $k$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 1 (`jis-2024-24.2.5-lem-1`). -/
public theorem_wanted floor_div_sequence_card_ge (n k : ℕ) (hk : 1 ≤ k) :
    ((Finset.Icc 1 n).filter (fun d : ℕ => k ≤ n / d)).card = n / k

/-- **The floor parity count as an alternating sum.** Let $\mathcal{F}_n$ be the number of
integers $k$ with $1 \le k \le n$ for which $\lfloor n/k \rfloor$ is odd. For every natural
number $n$, $\mathcal{F}_n = \sum_{d=1}^{n} \lfloor n/d \rfloor (-1)^{d+1}$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 2 (`jis-2024-24.2.5-prop-2`). -/
public theorem_wanted floorQuotientOddCount_eq_alternating_sum (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      ∑ d ∈ Finset.Icc 1 n, ((n / d : ℕ) : ℤ) * (-1) ^ (d + 1)

/-- **The floor parity count through the divisor summatory function.** Let $\tau(m)$ be the
number of positive divisors of $m$, let $D(x) = \sum_{1 \le m \le x} \tau(m)$, and let
$\mathcal{F}_n$ be the number of integers $k$ with $1 \le k \le n$ for which
$\lfloor n/k \rfloor$ is odd. For every natural number $n$, $\mathcal{F}_n = D(n) - 2D(n/2)$,
where $D(n/2) = D(\lfloor n/2 \rfloor)$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 3 (`jis-2024-24.2.5-cor-3`). -/
public theorem_wanted floorQuotientOddCount_eq_divisor_summatory_sub (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      ∑ m ∈ Finset.Icc 1 n, (m.divisors.card : ℤ) -
        2 * ∑ m ∈ Finset.Icc 1 (n / 2), (m.divisors.card : ℤ)

/-- **Odd floor quotients as a hyperbolic lattice-point difference.** For every natural number
$n$, the floor sequence parity count $\mathcal{F}_n$ equals the number of integer pairs $(x, y)$
with $x, y \ge 1$ and $n/2 < xy \le n$ minus the number of integer pairs $(x, y)$ with
$x, y \ge 1$ and $xy \le n/2$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 4 (`jis-2024-24.2.5-prop-4`). -/
public theorem_wanted floorQuotientOddCount_eq_hyperbolic_lattice_difference
    (n : ℕ) :
    (floorQuotientOddCount n : ℤ) =
      (Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧
          (n : ℤ) < 2 * (p.1 * p.2) ∧ p.1 * p.2 ≤ n} : ℤ) -
        Nat.card {p : ℤ × ℤ // 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * (p.1 * p.2) ≤ n}

/-- **Dirichlet's asymptotic for the divisor summatory function.** Let $\tau(m)$ be the number of
positive divisors of $m$, let $D(x) = \sum_{1 \le m \le x} \tau(m)$ for real $x$, and let
$\gamma$ be the Euler–Mascheroni constant. There is a real constant $C$ such that
$|D(x) - (x \log x + (2\gamma - 1)\, x)| \le C \sqrt{x}$ for every real $x \ge 1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 6 (`jis-2024-24.2.5-thm-6`). -/
public theorem_wanted divisor_summatory_asymptotic :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (m.divisors.card : ℝ)) -
          (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
        C * Real.sqrt x

/-- **Asymptotics of the floor parity count.** Let $\mathcal{F}_n$ be the number of integers $k$
with $1 \le k \le n$ for which $\lfloor n/k \rfloor$ is odd. There is a real constant $C$ such
that $|\mathcal{F}_n - n \log 2| \le C \sqrt{n}$ for every integer $n \ge 1$, and
$\mathcal{F}_n / n \to \log 2$ as $n \to \infty$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 7 (`jis-2024-24.2.5-prop-7`). -/
public theorem_wanted floorQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(floorQuotientOddCount n : ℝ) - n * Real.log 2| ≤ C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (floorQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (Real.log 2))

/-- **Ceiling parity count from the floor parity count.** For a natural number $m$, let
$\mathcal{C}_m$ and $\mathcal{F}_m$ be the numbers of integers $k$ with $1 \le k \le m$ for which
$\lceil m/k \rceil$, respectively $\lfloor m/k \rfloor$, is odd. Then for every natural number
$n$, $\mathcal{C}_{n+1} = (n + 1) - \mathcal{F}_n$.

The source prints a second equality $\mathcal{C}_n = \sum_{d=2}^{n} \lfloor n/d \rfloor (-1)^d$,
which is not part of this statement: it fails at $n = 3$, where $\mathcal{C}_3 = 2$ but the sum
is $1 - 1 = 0$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 9 (`jis-2024-24.2.5-prop-9`). -/
public theorem_wanted ceilQuotientOddCount_succ_eq (n : ℕ) :
    (ceilQuotientOddCount (n + 1) : ℤ) = (n + 1 : ℤ) - floorQuotientOddCount n

/-- **Asymptotics of the ceiling parity count.** Let $\mathcal{C}_n$ be the number of integers
$k$ with $1 \le k \le n$ for which $\lceil n/k \rceil$ is odd. There is a real constant $C$ such
that $|\mathcal{C}_n - (1 - \log 2)\, n| \le C \sqrt{n}$ for every integer $n \ge 1$, and
$\mathcal{C}_n / n \to 1 - \log 2$ as $n \to \infty$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 10 (`jis-2024-24.2.5-cor-10`). -/
public theorem_wanted ceilQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(ceilQuotientOddCount n : ℝ) - (1 - Real.log 2) * n| ≤
        C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (ceilQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (1 - Real.log 2))

/-- **Square-root bound for the number of divisors.** For every natural number $n$, the number
of positive divisors of $n$ is at most $2\sqrt{n}$. For $n = 0$ the set of divisors is taken to
be empty, so the bound holds trivially.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 12 (`jis-2024-24.2.5-lem-12`). -/
public theorem_wanted card_divisors_le_two_mul_sqrt (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n

/-- **Counting large terms of the rounded quotient sequence.** Let $n$ be a natural number.
Every $d$ with $1 \le d \le n$ satisfies $\lfloor n/d + 1/2 \rfloor \ge 1$, and for every
integer $k \ge 2$ the number of $d$ with $1 \le d \le n$ and $\lfloor n/d + 1/2 \rfloor \ge k$
is $\lfloor 2n/(2k-1) \rfloor$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 13 (`jis-2024-24.2.5-lem-13`). -/
public theorem_wanted round_div_sequence_card_ge (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun d : ℕ => (1 : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋)).card
        = n ∧
      ∀ k : ℕ, 2 ≤ k →
        ((Finset.Icc 1 n).filter
            (fun d : ℕ => (k : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋)).card =
          2 * n / (2 * k - 1)

/-- **Alternating-sum formula for the rounding sequence parity count.** For every natural
number $n$, the rounding sequence parity count $\mathcal{R}_n$ satisfies
$\mathcal{R}_n = -n + \sum_{d=1}^{n} (-1)^{d+1} \lfloor 2n/(2d-1) \rfloor$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 14 (`jis-2024-24.2.5-prop-14`). -/
public theorem_wanted roundQuotientOddCount_eq_alternating_sum (n : ℕ) :
    (roundQuotientOddCount n : ℤ) =
      -n + ∑ d ∈ Finset.Icc 1 n, ((2 * n / (2 * d - 1) : ℕ) : ℤ) * (-1) ^ (d + 1)

/-- **Divisor-sum formula for the rounding sequence parity count.** For a positive integer $k$
and $r \in \{1, 3\}$, let $d_{r,4}(k)$ be the number of positive divisors of $k$ congruent to
$r$ modulo $4$. Then for every natural number $n$, the rounding sequence parity count
$\mathcal{R}_n$ satisfies $\mathcal{R}_n = -n + \sum_{k=1}^{2n} (d_{1,4}(k) - d_{3,4}(k))$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 15 (`jis-2024-24.2.5-lem-15`). -/
public theorem_wanted roundQuotientOddCount_eq_sum_divisor_difference (n : ℕ) :
    (roundQuotientOddCount n : ℤ) =
      -n + ∑ k ∈ Finset.Icc 1 (2 * n),
        (((k.divisors.filter (fun d : ℕ => d % 4 = 1)).card : ℤ) -
          (k.divisors.filter (fun d : ℕ => d % 4 = 3)).card)

/-- **Jacobi's formula for the number of representations as a sum of two squares.** For every
integer $n \ge 1$, the number $r_2(n)$ of pairs $(a, b) \in \mathbb{Z}^2$ with $a^2 + b^2 = n$
equals $4\,(d_{1,4}(n) - d_{3,4}(n))$, where $d_{r,4}(n)$ is the number of positive divisors of
$n$ congruent to $r$ modulo $4$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 16 (`jis-2024-24.2.5-thm-16`). -/
public theorem_wanted card_sq_add_sq_eq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} : ℤ) =
      4 * (((n.divisors.filter (fun d : ℕ => d % 4 = 1)).card : ℤ) -
        (n.divisors.filter (fun d : ℕ => d % 4 = 3)).card)

/-- **Lattice points in the disc of radius $\sqrt{2n}$.** For every natural number $n$, the
number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + y^2 \le 2n$ equals
$4\,\mathcal{R}_n + 4n + 1$, where $\mathcal{R}_n$ is the number of $k \in \{1, \dots, n\}$ for
which the nearest integer to $n/k$, with half-integers rounded up, is odd. At $n = 0$ both sides
are $1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 17 (`jis-2024-24.2.5-prop-17`). -/
public theorem_wanted card_lattice_disc_two_mul (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ 2 * n} =
      4 * roundQuotientOddCount n + 4 * n + 1

/-- **The rounding sequence parity count drops by at most one.** For every natural number $n$,
the rounding sequence parity count $\mathcal{R}$ satisfies
$\mathcal{R}_{n+1} \ge \mathcal{R}_n - 1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 19 (`jis-2024-24.2.5-cor-19`). -/
public theorem_wanted roundQuotientOddCount_sub_one_le_succ (n : ℕ) :
    (roundQuotientOddCount n : ℤ) - 1 ≤ roundQuotientOddCount (n + 1)

/-- **Gauss's bound for lattice points in a disc.** There is a constant $C$ such that for every
real $x \ge 1$, the number $N(x)$ of integer pairs $(a, b)$ with $a^2 + b^2 \le x$ satisfies
$|N(x) - \pi x| \le C \sqrt{x}$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 20 (`jis-2024-24.2.5-thm-20`). -/
public theorem_wanted gauss_circle_asymptotic :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(Nat.card {p : ℤ × ℤ // ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ x} : ℝ) -
          Real.pi * x| ≤ C * Real.sqrt x

/-- **Asymptotic density of odd rounded quotients.** There is a constant $C$ such that the
rounding sequence parity count $\mathcal{R}_n$ satisfies $|\mathcal{R}_n - (\pi/2 - 1)n| \le
C\sqrt{n}$ for every natural number $n \ge 1$; moreover $\mathcal{R}_n / n \to \pi/2 - 1$ as
$n \to \infty$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 21 (`jis-2024-24.2.5-prop-21`). -/
public theorem_wanted roundQuotientOddCount_asymptotic :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(roundQuotientOddCount n : ℝ) - (Real.pi / 2 - 1) * n| ≤
        C * Real.sqrt n) ∧
    Tendsto (fun n : ℕ => (roundQuotientOddCount n : ℝ) / n) atTop
      (𝓝 (Real.pi / 2 - 1))

/-- **Tail counts of the shifted floor sequence.** Let $n$ be a natural number and let $\alpha$
and $\nu$ be real numbers with $0 \le \alpha < 1$, $0 \le \nu < 1$ and $\nu \le n\alpha$. Then
$\lfloor (n - \nu)/d + \alpha \rfloor \ge 1$ for all $n$ integers $d$ with $1 \le d \le n$, and
for every natural number $k \ge 2$ the number of integers $d$ with $1 \le d \le n$ and
$\lfloor (n - \nu)/d + \alpha \rfloor \ge k$ is $\lfloor (n - \nu)/(k - \alpha) \rfloor$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 24 (`jis-2024-24.2.5-lem-24`). -/
public theorem_wanted shifted_floor_sequence_card_ge (n : ℕ) (α ν : ℝ)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν) (hν₁ : ν < 1)
    (hnαν : ν ≤ n * α) :
    ((Finset.Icc 1 n).filter
        (fun d : ℕ => (1 : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋)).card = n ∧
      ∀ k : ℕ, 2 ≤ k →
        (((Finset.Icc 1 n).filter
            (fun d : ℕ => (k : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋)).card : ℤ) =
          ⌊((n : ℝ) - ν) / (k - α)⌋

/-- **Floor-sum formulas for the shifted floor residue counts.** Let $n$ and $m$ be natural
numbers with $m \ge 2$, and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$,
$0 \le \nu < 1$ and $\nu \le n\alpha$. For an integer $r$ let $\mathcal N_{n,\alpha,\nu,r,m}$ be
the number of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$. Then

$$\mathcal N_{n,\alpha,\nu,1,m} = n - \Bigl\lfloor \frac{n - \nu}{1 - \alpha} \Bigr\rfloor +
\sum_{i=0}^{n} \Bigl( \Bigl\lfloor \frac{n - \nu}{1 + im - \alpha} \Bigr\rfloor -
\Bigl\lfloor \frac{n - \nu}{2 + im - \alpha} \Bigr\rfloor \Bigr),$$

and for every natural number $r$ with $2 \le r \le m$,

$$\mathcal N_{n,\alpha,\nu,r,m} = \sum_{i=0}^{n} \Bigl( \Bigl\lfloor \frac{n - \nu}{r + im - \alpha}
\Bigr\rfloor - \Bigl\lfloor \frac{n - \nu}{r + 1 + im - \alpha} \Bigr\rfloor \Bigr).$$

The paper sums over all $i \ge 0$; the terms with $i > n$ vanish, because for them every
denominator exceeds $n - \nu \ge 0$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 25 (`jis-2024-24.2.5-prop-25`). -/
public theorem_wanted shiftedFloorResidueCount_eq_sum_floor_sub (n m : ℕ)
    (hm : 2 ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν)
    (hν₁ : ν < 1) (hnαν : ν ≤ n * α) :
    ((shiftedFloorResidueCount n α ν 1 m : ℤ) =
      n - ⌊((n : ℝ) - ν) / (1 - α)⌋ +
        ∑ i ∈ Finset.range (n + 1),
          (⌊((n : ℝ) - ν) / (1 + i * m - α)⌋ -
            ⌊((n : ℝ) - ν) / (2 + i * m - α)⌋)) ∧
    ∀ r : ℕ, 2 ≤ r → r ≤ m →
      (shiftedFloorResidueCount n α ν r m : ℤ) =
        ∑ i ∈ Finset.range (n + 1),
          (⌊((n : ℝ) - ν) / (r + i * m - α)⌋ -
            ⌊((n : ℝ) - ν) / (r + 1 + i * m - α)⌋)

/-- **Alternating sums of floor quotients along an increasing sequence.** Let $0 \le \nu < 1$
and let $b_0, b_1, b_2, \dots$ be a strictly increasing sequence of real numbers with $b_k \ge 1$
and $b_k \ge k$ for every $k \ge 0$. Then there is a real constant $C$ such that for every integer
$n \ge 1$, with both sums taken over the integers $k$ satisfying $0 \le k \le n - \nu$,

$$\Bigl| \sum_k (-1)^k \lfloor (n - \nu)/b_k \rfloor - n \sum_k (-1)^k/b_k \Bigr| \le C\sqrt{n}.$$

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 32 (`jis-2024-24.2.5-prop-32`). -/
public theorem_wanted alternating_sum_floor_div_eq_add_bigO (ν : ℝ)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) (b : ℕ → ℝ) (hb : StrictMono b)
    (hb₁ : ∀ k, 1 ≤ b k) (hbk : ∀ k : ℕ, (k : ℝ) ≤ b k) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
            (⌊((n : ℝ) - ν) / b k⌋ : ℝ) * (-1) ^ k) -
          n * ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ n - ν),
            (-1) ^ k / b k| ≤ C * Real.sqrt n

/-- **Series asymptotics for the shifted floor residue counts with $2 \le r \le m$.** Let $r$ and
$m$ be natural numbers with $2 \le r \le m$, and let $\alpha$ and $\nu$ be real numbers with
$0 \le \alpha < 1$ and $0 \le \nu < 1$. For a natural number $n$ let
$\mathcal N_{n,\alpha,\nu,r,m}$ be the number of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$, and put

$$S = \sum_{i \ge 0} \Bigl( \frac{1}{r + im - \alpha} - \frac{1}{r + 1 + im - \alpha} \Bigr).$$

Then there is a constant $C$ such that
$\bigl| \mathcal N_{n,\alpha,\nu,r,m} - nS \bigr| \le C \sqrt n$ for every natural number
$n \ge 1$ with $\nu \le n\alpha$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 34 (`jis-2024-24.2.5-cor-34`). -/
public theorem_wanted shiftedFloorResidueCount_asymptotic_series (r m : ℕ)
    (hr : 2 ≤ r) (hrm : r ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
      |(shiftedFloorResidueCount n α ν r m : ℝ) -
          n * ∑' i : ℕ, (1 / ((r : ℝ) + i * m - α) - 1 / ((r : ℝ) + 1 + i * m - α))|
        ≤ C * Real.sqrt n

/-- **Series asymptotics for the shifted floor residue count with $r = 1$.** Let $m \ge 2$ be a
natural number and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$ and
$0 \le \nu < 1$. For a natural number $n$ let $\mathcal N_{n,\alpha,\nu,1,m}$ be the number of
integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv 1 \pmod m$, and put

$$S = \sum_{i \ge 0} \Bigl( \frac{1}{1 + im - \alpha} - \frac{1}{2 + im - \alpha} \Bigr).$$

Then there is a constant $C$ such that

$$\Bigl| \mathcal N_{n,\alpha,\nu,1,m} - \Bigl( -\frac{\alpha n}{1 - \alpha} + nS \Bigr) \Bigr| \le
C \sqrt n$$

for every natural number $n \ge 1$ with $\nu \le n\alpha$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 35 (`jis-2024-24.2.5-cor-35`). -/
public theorem_wanted shiftedFloorResidueCount_one_asymptotic_series (m : ℕ)
    (hm : 2 ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν)
    (hν₁ : ν < 1) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
      |(shiftedFloorResidueCount n α ν 1 m : ℝ) -
          (-α * n / (1 - α) +
            n * ∑' i : ℕ, (1 / (1 + (i : ℝ) * m - α) - 1 / (2 + (i : ℝ) * m - α)))|
        ≤ C * Real.sqrt n

/-- **Integral formula for an alternating series of reciprocals.** Let $r$ and $m$ be natural
numbers with $2 \le r \le m$ and let $\alpha$ be a real number with $0 \le \alpha < 1$. Then

$$\sum_{i \ge 0} \Bigl( \frac{1}{r + im - \alpha} - \frac{1}{r + 1 + im - \alpha} \Bigr) =
\int_0^1 \frac{(1 - x)\, x^{r - 1 - \alpha}}{1 - x^m} \, dx.$$

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 36 (`jis-2024-24.2.5-prop-36`). -/
public theorem_wanted tsum_alternating_inv_eq_integral (r m : ℕ) (hr : 2 ≤ r)
    (hrm : r ≤ m) (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    ∑' i : ℕ, (1 / ((r : ℝ) + i * m - α) - 1 / ((r : ℝ) + 1 + i * m - α)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m)

/-- **Integral asymptotics for the shifted floor residue counts.** Let $m \ge 1$ be a natural
number and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$ and $0 \le \nu < 1$.
For natural numbers $n$ and $r$ let $\mathcal N_{n,\alpha,\nu,r,m}$ be the number of integers $k$
with $1 \le k \le n$ such that $\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$, and put

$$I_r = \int_0^1 \frac{(1 - x)\, x^{r - 1 - \alpha}}{1 - x^m} \, dx.$$

Then there is a constant $C$ such that

$$\Bigl| \mathcal N_{n,\alpha,\nu,1,m} - \Bigl( -\frac{\alpha n}{1 - \alpha} + n I_1 \Bigr) \Bigr|
\le C \sqrt n$$

for every natural number $n \ge 1$ with $\nu \le n\alpha$, and for every natural number $r$ with
$2 \le r \le m$ there is a constant $C_r$ such that
$\bigl| \mathcal N_{n,\alpha,\nu,r,m} - n I_r \bigr| \le C_r \sqrt n$ for every natural number
$n \ge 1$ with $\nu \le n\alpha$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Theorem 37 (`jis-2024-24.2.5-thm-37`). -/
public theorem_wanted shiftedFloorResidueCount_asymptotic_integral (m : ℕ)
    (hm : 1 ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν)
    (hν₁ : ν < 1) :
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
      |(shiftedFloorResidueCount n α ν 1 m : ℝ) -
          (-α * n / (1 - α) +
            n * ∫ x in (0 : ℝ)..1, (1 - x) * x ^ (-α) / (1 - x ^ m))|
        ≤ C * Real.sqrt n) ∧
    ∀ r : ℕ, 2 ≤ r → r ≤ m →
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ν ≤ n * α →
        |(shiftedFloorResidueCount n α ν r m : ℝ) -
            n * ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m)|
          ≤ C * Real.sqrt n

/-- **Limiting densities of the shifted floor residue counts.** Let $r$ and $m$ be natural
numbers with $1 \le r \le m$, and let $\alpha$ and $\nu$ be real numbers with $0 \le \alpha < 1$
and $0 \le \nu < 1$. For a natural number $n$ let $\mathcal N_{n,\alpha,\nu,r,m}$ be the number
of integers $k$ with $1 \le k \le n$ such that
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$, and for a natural number $s$ put

$$I_s = \int_0^1 \frac{(1 - x)\, x^{s - 1 - \alpha}}{1 - x^m} \, dx.$$

Then, as $n \to \infty$, $\mathcal N_{n,\alpha,\nu,r,m}/n$ tends to $-\alpha/(1 - \alpha) + I_1$
if $r = 1$ and to $I_r$ if $r \ge 2$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 38 (`jis-2024-24.2.5-cor-38`). -/
public theorem_wanted shiftedFloorResidueCount_div_tendsto (r m : ℕ)
    (hr : 1 ≤ r) (hrm : r ≤ m) (α ν : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hν₀ : 0 ≤ ν) (hν₁ : ν < 1) :
    Tendsto (fun n : ℕ => (shiftedFloorResidueCount n α ν r m : ℝ) / n) atTop
      (𝓝 (if r = 1 then
          -α / (1 - α) + ∫ x in (0 : ℝ)..1, (1 - x) * x ^ (-α) / (1 - x ^ m)
        else ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m)))

/-- **Lattice points in the disc of radius $\sqrt{n}$ via shifted floor sequences.** For every
natural number $n$, the number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + y^2 \le n$ equals
$4\,\mathcal{N}_{\lceil n/2 \rceil, 1/2, \{n/2\}, 1, 2} + 4\lfloor n/2 \rfloor + 1$, where
$\{n/2\}$ is the fractional part of $n/2$ and $\mathcal{N}_{N,\alpha,\nu,r,m}$ is the number of
$k \in \{1, \dots, N\}$ with $\lfloor (N - \nu)/k + \alpha \rfloor \equiv r \pmod m$. At $n = 0$
both sides are $1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 39 (`jis-2024-24.2.5-prop-39`). -/
public theorem_wanted card_lattice_disc_eq_shiftedFloorResidueCount (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 ≤ n} =
      4 * shiftedFloorResidueCount ⌈(n : ℝ) / 2⌉₊ (1 / 2)
          (Int.fract ((n : ℝ) / 2)) 1 2 + 4 * (n / 2) + 1

/-- **Number of representations by $x^2 + xy + y^2$.** For every integer $n \ge 1$, the number
of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + xy + y^2 = n$ equals
$6\,(d_{1,3}(n) - d_{2,3}(n))$, where $d_{r,3}(n)$ is the number of positive divisors of $n$
congruent to $r$ modulo $3$.

The paper cites this as Dickson, Exercise XXII.2.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 42 (`jis-2024-24.2.5-prop-42`). -/
public theorem_wanted card_eisenstein_form_eq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 = n} : ℤ) =
      6 * (((n.divisors.filter (fun d : ℕ => d % 3 = 1)).card : ℤ) -
        (n.divisors.filter (fun d : ℕ => d % 3 = 2)).card)

/-- **Lattice points in the ellipse $x^2 + xy + y^2 \le n$.** For every natural number $n$, the
number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + xy + y^2 \le n$ equals
$6\,\mathcal{N}_{n,0,0,1,3} + 1$, where $\mathcal{N}_{n,0,0,1,3}$ is the number of
$k \in \{1, \dots, n\}$ with $\lfloor n/k \rfloor \equiv 1 \pmod 3$. At $n = 0$ both sides
are $1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 43 (`jis-2024-24.2.5-cor-43`). -/
public theorem_wanted card_eisenstein_ellipse_eq (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ n} =
      6 * shiftedFloorResidueCount n 0 0 1 3 + 1

/-- **Lattice points in the ellipse $x^2 + xy + y^2 \le n$, asymptotically.** There is a real
constant $C$ such that for every integer $n \ge 1$, the number $E(n)$ of pairs
$(x, y) \in \mathbb{Z}^2$ with $x^2 + xy + y^2 \le n$ satisfies
$\bigl| E(n) - \tfrac{2}{3}\sqrt{3}\,\pi n \bigr| \le C\sqrt{n}$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 45 (`jis-2024-24.2.5-cor-45`). -/
public theorem_wanted card_eisenstein_ellipse_asymptotic :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ n} : ℝ) -
          2 / 3 * Real.sqrt 3 * Real.pi * n| ≤ C * Real.sqrt n

/-- **Lattice points in a disc of the hexagonal lattice.** Let $\omega = e^{2\pi i/3}$, so that
$\mathbb{Z} + \mathbb{Z}\omega$ is the hexagonal (triangular) lattice whose neighboring points are
one unit apart. For every natural number $n$, the number of pairs $(x, y) \in \mathbb{Z}^2$ with
$|x + y\omega| \le \sqrt{n}$ equals $1 + 6\,\mathcal{N}_{n,0,0,1,3}$, where
$\mathcal{N}_{n,\alpha,\nu,r,m}$ is the number of $k \in \{1, \dots, n\}$ with
$\lfloor (n - \nu)/k + \alpha \rfloor \equiv r \pmod m$. Moreover, $\mathcal{N}_{n,0,0,1,3}$ is
the number of terms of $\lfloor n/1 \rfloor, \dots, \lfloor n/n \rfloor$ that are congruent to
$1$ modulo $3$.

Every hexagonal lattice with unit spacing is congruent to this one, so this counts the lattice
points in any closed disc of radius $\sqrt{n}$ centered at a lattice point.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 47 (`jis-2024-24.2.5-cor-47`). -/
public theorem_wanted card_hexagonal_lattice_disc_eq (n : ℕ) :
    Nat.card {p : ℤ × ℤ //
        ‖(p.1 : ℂ) + p.2 * Complex.exp (2 * Real.pi / 3 * Complex.I)‖ ≤
          Real.sqrt n} =
      1 + 6 * shiftedFloorResidueCount n 0 0 1 3 ∧
    shiftedFloorResidueCount n 0 0 1 3 =
      ((Finset.Icc 1 n).filter (fun k => n / k % 3 = 1)).card

/-- **Dickson's divisor formula for $x^2 + 2y^2$.** For every integer $n \ge 1$, the number of
pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + 2y^2 = n$ equals
$2\,(d_1(n) + d_3(n) - d_5(n) - d_7(n))$, where $d_r(n)$ denotes the number of positive divisors
$d$ of $n$ with $d \equiv r \pmod 8$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 48 (`jis-2024-24.2.5-prop-48`). -/
public theorem_wanted card_sq_add_two_mul_sq_eq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 = n} : ℤ) =
      2 * (((n.divisors.filter (fun d : ℕ => d % 8 = 1)).card : ℤ) +
        (n.divisors.filter (fun d : ℕ => d % 8 = 3)).card -
        (n.divisors.filter (fun d : ℕ => d % 8 = 5)).card -
        (n.divisors.filter (fun d : ℕ => d % 8 = 7)).card)

/-- **Lattice points in the ellipse $x^2 + 2y^2 \le n$.** For a natural number $n$, let $F(n)$ be
the number of pairs $(x, y) \in \mathbb{Z}^2$ with $x^2 + 2y^2 \le n$, and let
$\mathcal{N}_{N,\alpha,\nu,r,m}$ be the number of $k \in \{1, \dots, N\}$ with
$\lfloor (N - \nu)/k + \alpha \rfloor \equiv r \pmod m$. Then $F(0) = 1$, $F(1) = 3$,
$F(2) = 5$ and $F(5) = 11$. For every natural number $n \notin \{1, 2, 5\}$, writing
$N = \lceil n/4 \rceil$ and $\theta = \{-n/4\}$ for the fractional part of $-n/4$,
$F(n) = 1 + 2\,\mathcal{N}_{N,3/4,\theta,1,2} + 2\,\mathcal{N}_{N,1/4,\theta,1,2} +
2n + 2\lfloor n/3 \rfloor - 4N$. This formula includes $n = 0$, where both sides are $1$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Corollary 49 (`jis-2024-24.2.5-cor-49`). -/
public theorem_wanted card_sq_add_two_mul_sq_ellipse_eq :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 0} = 1 ∧
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 1} = 3 ∧
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 2} = 5 ∧
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 5} = 11 ∧
    ∀ n : ℕ, n ≠ 1 → n ≠ 2 → n ≠ 5 →
      (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + 2 * p.2 ^ 2 ≤ n} : ℤ) =
        1 + 2 * shiftedFloorResidueCount ⌈(n : ℝ) / 4⌉₊ (3 / 4)
            (Int.fract (-(n : ℝ) / 4)) 1 2 +
          2 * shiftedFloorResidueCount ⌈(n : ℝ) / 4⌉₊ (1 / 4)
            (Int.fract (-(n : ℝ) / 4)) 1 2 +
          2 * n + 2 * (n / 3 : ℕ) - 4 * ⌈(n : ℝ) / 4⌉₊

end

end MetaMathlibExt
