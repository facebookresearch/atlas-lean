/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Congruences for representations as sums of squares and triangular numbers

Statements from Alegri and Christopher, *On Formulas, Recurrences, and
Congruences for Representations of Integers as Sums of Squares and Triangular
Numbers*, INTEGERS 26 (2026), Article A93. With `θ(q) = ∑_{m ∈ ℤ} q^{m²}` and
`ψ(q) = ∑_{m ≥ 0} q^{m(m+1)/2}`, `r_k(n)` and `t_k(n)` are the coefficients of
`q^n` in `θ(q)^k` and `ψ(q)^k`: for `k ≥ 1` the numbers of representations of `n`
as an ordered sum of `k` squares of integers and of `k` triangular numbers. The
source treats them as polynomials in `k` (`n! r_k(n), n! t_k(n) ∈ ℤ[k]`) and
evaluates at arbitrary integers `k` (e.g. `k + r p` with `r ∈ ℤ`); here `k ∈ ℤ`
through the integer powers of the units `θ` and `ψ` of `ℤ⟦q⟧`, which agree with
those polynomial values.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The square theta series.** The square theta series is the formal power series
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$ in $\mathbb{Z}[[q]]$: for each $n \ge 0$, its
coefficient of $q^n$ is the number of integers $m$ with $m^2 = n$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def squareThetaSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((Finset.Icc (-(n : ℤ)) n).filter fun m : ℤ => m ^ 2 = (n : ℤ)).card : ℤ)

/-- **Triangular theta series.** The triangular theta series is the formal power series
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$ with integer coefficients: for each natural number $n$,
its coefficient of $q^n$ is the number of natural numbers $m$ with $m(m+1)/2 = n$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def triangularThetaSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((Finset.range (n + 1)).filter fun m => m * (m + 1) / 2 = n).card : ℤ)

/-- **First coefficients of the square theta series.** In the square theta series
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$, the coefficients of $q^0$, $q^1$, $q^2$ and $q^4$ are
$1$, $2$, $0$ and $2$ respectively.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem coeff_squareThetaSeries_small :
    PowerSeries.coeff 0 squareThetaSeries = 1 ∧ PowerSeries.coeff 1 squareThetaSeries = 2 ∧
      PowerSeries.coeff 2 squareThetaSeries = 0 ∧ PowerSeries.coeff 4 squareThetaSeries = 2 := by
  simp only [squareThetaSeries, PowerSeries.coeff_mk]
  decide

/-- **First coefficients of the triangular theta series.** In the triangular theta series
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$, the coefficients of $q^0$, $q^1$, $q^2$ and $q^3$ are $1$,
$1$, $0$ and $1$ respectively.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem coeff_triangularThetaSeries_small :
    PowerSeries.coeff 0 triangularThetaSeries = 1 ∧ PowerSeries.coeff 1 triangularThetaSeries = 1 ∧
      PowerSeries.coeff 2 triangularThetaSeries = 0 ∧
        PowerSeries.coeff 3 triangularThetaSeries = 1 := by
  simp only [triangularThetaSeries, PowerSeries.coeff_mk]
  decide

/-- **The square theta series is a unit.** The square theta series
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$ is a unit of the ring $\mathbb{Z}[[q]]$ of formal
power series with integer coefficients, since its constant coefficient is $1$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem isUnit_squareThetaSeries : IsUnit squareThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_squareThetaSeries_small.1]
  exact isUnit_one

/-- **The triangular theta series is a unit.** The triangular theta series
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$ is a unit of the ring $\mathbb{Z}[[q]]$ of formal power
series with integer coefficients, since its constant coefficient is $1$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem isUnit_triangularThetaSeries : IsUnit triangularThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_triangularThetaSeries_small.1]
  exact isUnit_one

/-- **Representation numbers for sums of squares.** For an integer $k$ and a natural number $n$,
$r_k(n)$ is the coefficient of $q^n$ in $\theta(q)^k$, where
$\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$. Since $\theta$ has constant coefficient $1$, it is a
unit of $\mathbb{Z}[[q]]$, so $\theta^k$ is a power series for negative $k$ as well.

For $k \ge 1$, $r_k(n)$ is the number of ways to write $n$ as an ordered sum of $k$ squares of
integers.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def sumOfSquaresRepCount (k : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((isUnit_squareThetaSeries.unit ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

/-- **Representation numbers for sums of triangular numbers.** For an integer $k$ and a natural
number $n$, $t_k(n)$ is the coefficient of $q^n$ in $\psi(q)^k$, where
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Since $\psi$ has constant coefficient $1$, it is a unit of
$\mathbb{Z}[[q]]$, so $\psi^k$ is a power series for negative $k$ as well.

For $k \ge 1$, $t_k(n)$ is the number of ways to write $n$ as an ordered sum of $k$ triangular
numbers $m(m+1)/2$ with $m \ge 0$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def sumOfTriangularRepCount (k : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((isUnit_triangularThetaSeries.unit ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

/-- **The one-square counts are the coefficients of the square theta series.** For an integer $k$
and $n \ge 0$, let $r_k(n)$ be the coefficient of $q^n$ in $\theta(q)^k$, where $\theta$ is the
square theta series. Then for every $n \ge 0$, $r_1(n)$ equals the coefficient of $q^n$ in
$\theta(q)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem sumOfSquaresRepCount_one (n : ℕ) :
    sumOfSquaresRepCount 1 n = PowerSeries.coeff n squareThetaSeries := by
  simp [sumOfSquaresRepCount]

/-- **Triangular representation numbers with one summand.** For an integer $k$, let $t_k(n)$ be the
coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Then for every
natural number $n$, $t_1(n)$ equals the coefficient of $q^n$ in $\psi(q)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem sumOfTriangularRepCount_one (n : ℕ) :
    sumOfTriangularRepCount 1 n = PowerSeries.coeff n triangularThetaSeries := by
  simp [sumOfTriangularRepCount]

/-- **Divisibility of square representation counts by a large prime is periodic.** For an integer
$k$ and $n \ge 0$, let $r_k(n)$ be the coefficient of $q^n$ in $\theta(q)^k$, where $\theta$ is the
square theta series; for $k \ge 1$ it is the number of representations of $n$ as an ordered sum of
$k$ squares of integers. Let $n \ge 1$ and $k \ge 1$ be integers and let $p$ be a prime with
$p \ge n + 1$. If $p$ divides $r_k(n)$, then $p$ divides $r_{k+jp}(n)$ for every integer $j$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 3 (`integers-2026-A93-thm-3`). -/
public theorem_wanted sumOfSquaresRepCount_add_mul_prime {n k p : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hp : p.Prime) (hpn : n + 1 ≤ p) (h : (p : ℤ) ∣ sumOfSquaresRepCount k n) (r : ℤ) :
    (p : ℤ) ∣ sumOfSquaresRepCount (k + r * p) n

/-- **Prime divisibility of triangular representation numbers persists under prime shifts.** For an
integer $k$, let $t_k(n)$ be the coefficient of $q^n$ in $\psi(q)^k$, where
$\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Let $n \ge 1$ and $k \ge 1$ be natural numbers and let $p$
be a prime with $p \ge n + 1$. If $p$ divides $t_k(n)$, then $p$ divides $t_{k+rp}(n)$ for every
integer $r$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 4 (`integers-2026-A93-thm-4`). -/
public theorem_wanted sumOfTriangularRepCount_add_mul_prime {n k p : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hp : p.Prime) (hpn : n + 1 ≤ p)
    (h : (p : ℤ) ∣ sumOfTriangularRepCount k n) (r : ℤ) :
    (p : ℤ) ∣ sumOfTriangularRepCount (k + r * p) n

/-- **Window congruence for sums of squares.** For an integer $k$, let $r_k(n)$ be the coefficient
of $q^n$ in $\theta(q)^k$, where $\theta(q) = \sum_{m \in \mathbb{Z}} q^{m^2}$. Let $n \ge 1$, let
$p$ be an odd prime with $p - 1 \ge n + 1$, and let $s \ge p$ be an integer. Then $p$ divides
$\sum_{i=0}^{p-1} r_{s-i}(n)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 5 (`integers-2026-A93-thm-5`). -/
public theorem_wanted sum_sumOfSquaresRepCount_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) {s : ℤ} (hs : (p : ℤ) ≤ s) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfSquaresRepCount (s - i) n

/-- **Window congruence for sums of triangular numbers.** For an integer $k$, let $t_k(n)$ be the
coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. Let $n \ge 1$,
let $p$ be an odd prime with $p - 1 \ge n + 1$, and let $s \ge p$ be an integer. Then $p$ divides
$\sum_{i=0}^{p-1} t_{s-i}(n)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 6 (`integers-2026-A93-thm-6`). -/
public theorem_wanted sum_sumOfTriangularRepCount_window {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) {s : ℤ} (hs : (p : ℤ) ≤ s) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfTriangularRepCount (s - i) n

/-- **Representability criterion from a window of counts.** For an integer $k$ and $n \ge 0$, let
$r_k(n)$ and $t_k(n)$ be the coefficients of $q^n$ in $\theta(q)^k$ and $\psi(q)^k$, where $\theta$
and $\psi$ are the square and triangular theta series (units of $\mathbb{Z}[[q]]$). Let $n \ge 1$,
let $p$ be an odd prime with $p - 1 \ge n + 1$, and let $s$ be an integer. If $p$ does not divide
$r_{s-1}(n) + r_{s-2}(n) + \cdots + r_{s-(p-1)}(n)$, then $r_s(n) \ne 0$. Likewise, if $p$ does not
divide $t_{s-1}(n) + t_{s-2}(n) + \cdots + t_{s-(p-1)}(n)$, then $t_s(n) \ne 0$.

The source places no condition on $s$, so the statement is made for every integer $s$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 7 (`integers-2026-A93-thm-7`). -/
public theorem_wanted repCount_ne_zero_of_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ) :
    (¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfSquaresRepCount (s - i) n →
      sumOfSquaresRepCount s n ≠ 0) ∧
    (¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfTriangularRepCount (s - i) n →
      sumOfTriangularRepCount s n ≠ 0)

/-- **Window criterion for representability by triangular numbers.** For an integer $k$, let
$t_k(n)$ be the coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$.
Let $n \ge 1$ and let $p$ be an odd prime with $p - 1 \ge n + 1$. For every integer $s$, if $p$ does
not divide $\sum_{i=1}^{p-1} t_{s-i}(n)$, then $t_s(n) \ne 0$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 8 (`integers-2026-A93-thm-8`). -/
public theorem_wanted sumOfTriangularRepCount_ne_zero_of_window {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ)
    (h : ¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfTriangularRepCount (s - i) n) :
    sumOfTriangularRepCount s n ≠ 0

/-- **A prime between $p/2$ and $p$ divides the representation counts of $p$.** For integers
$k, n \ge 1$, let $r_k(n)$ be the number of representations of $n$ as an ordered sum of $k$ squares
of integers and $t_k(n)$ the number of representations of $n$ as an ordered sum of $k$ triangular
numbers $m(m+1)/2$ with $m \ge 0$. Let $p$ be an odd prime and $\ell$ a prime with
$p/2 < \ell < p$. Then $\ell$ divides both $r_\ell(p)$ and $t_\ell(p)$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 11 (`integers-2026-A93-thm-11`). -/
public theorem_wanted prime_dvd_repCount_of_half_lt {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hpq : p < 2 * q) (hqp : q < p) :
    (q : ℤ) ∣ sumOfSquaresRepCount q p ∧ (q : ℤ) ∣ sumOfTriangularRepCount q p

/-- **Logarithmic coefficients of the triangular theta series.** For a natural number $n$, let
$b_n$ be the rational number
$b_n = \sum_{d \mid n,\ n/d \text{ odd}} 1/d - \sum_{d \mid n,\ n/d \text{ even}} 1/d$, where $d$
runs over the positive divisors of $n$; for $n = 0$ the sums are taken to be empty, so $b_0 = 0$.

With $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$, the expansion
$\log \psi(q) = \sum_{m \ge 1} \log(1 - q^{2m}) - \sum_{m \ge 1} \log(1 - q^{2m-1})$ in the proof
of Theorem 2 shows that $b_n$ is the coefficient of $q^n$ in $\log \psi(q)$. The printed formula
of Theorem 2 has the parity condition on $d$ instead of $n/d$, which gives $b_2 = 1/2$ instead
of $-1/2$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 2 and its proof. -/
public def triangularLogCoeff (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, if Odd (n / d) then (1 : ℚ) / d else -((1 : ℚ) / d)

/-- **First logarithmic coefficients of the triangular theta series.** The logarithmic
coefficients $b_n$ of the triangular theta series satisfy $b_1 = 1$, $b_2 = -1/2$ and
$b_3 = 4/3$; this matches the expansion
$\log(1 + q + q^3 + \cdots) = q - q^2/2 + 4q^3/3 + \cdots$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 2 and its proof. -/
public theorem triangularLogCoeff_small :
    triangularLogCoeff 1 = 1 ∧ triangularLogCoeff 2 = -1 / 2 ∧ triangularLogCoeff 3 = 4 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [triangularLogCoeff]
    decide +kernel

/-- **Composition formula for triangular representation numbers.** For an integer $k$, let $t_k(n)$
be the coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. For
$m \ge 1$ let
$b_m = \sum_{d \mid m,\ m/d \text{ odd}} 1/d - \sum_{d \mid m,\ m/d \text{ even}} 1/d$, the
coefficient of $q^m$ in $\log \psi(q)$. Then for every integer $k$ and natural number $n$,

$$t_k(n) = \sum_{(w_1, \dots, w_l)} \frac{k^l}{l!}\, b_{w_1} \cdots b_{w_l},$$

where the sum runs over all compositions $(w_1, \dots, w_l)$ of $n$, that is, all tuples of positive
integers with sum $n$, of every length $l$ (for $n = 0$, only the empty composition).

The source prints $b_m$ with the parity condition on $d$ instead of $m/d$; with that coefficient the
formula fails, giving $t_1(2) = 1$ although $t_1(2) = 0$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 2 (`integers-2026-A93-thm-2`). -/
public theorem_wanted sumOfTriangularRepCount_eq_sum_compositions (k : ℤ) (n : ℕ) :
    (sumOfTriangularRepCount k n : ℚ) =
      ∑ c : Composition n, (k : ℚ) ^ c.length / (c.length.factorial : ℚ) *
        (c.blocks.map triangularLogCoeff).prod

/-- **Recurrence for triangular representation numbers.** For an integer $k$, let $t_k(n)$ be the
coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. For $m \ge 1$
let $b_m = \sum_{d \mid m,\ m/d \text{ odd}} 1/d - \sum_{d \mid m,\ m/d \text{ even}} 1/d$, the
coefficient of $q^m$ in $\log \psi(q)$. Then for every integer $k$ and natural number $n$,

$$t_k(n + 1) = \sum_{j=0}^{n} \frac{k (j + 1)\, b_{j+1}}{n + 1}\, t_k(n - j).$$

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Corollary 1, second recurrence (`integers-2026-A93-cor-1`). -/
public theorem_wanted sumOfTriangularRepCount_succ (k : ℤ) (n : ℕ) :
    (sumOfTriangularRepCount k (n + 1) : ℚ) =
      ∑ j ∈ Finset.range (n + 1),
        (k : ℚ) * (j + 1) * triangularLogCoeff (j + 1) / (n + 1) * sumOfTriangularRepCount k (n - j)

/-- **Integer zeros of the sums-of-squares counting polynomial.** For an integer $k$ and $n \ge 0$,
let $r_k(n)$ be the coefficient of $q^n$ in $\theta(q)^k$, where $\theta$ is the square theta
series. For every $n \ge 0$ there is a polynomial $P(z) = \sum_i c_i z^i$ with integer
coefficients such that $P(z) = n! \, r_z(n)$ for every integer $z$, and every nonzero integer $k$
with $r_k(n) = 0$ divides $c_1$ and satisfies $|k| < 2 |c_i|^{1/(n-i)}$ for some $i$ with
$0 \le i < n$.

Equivalently, $|k| < 2 R_n$ with $R_n = \max_{0 \le i \le n-1} |c_i|^{1/(n-i)}$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 9 (`integers-2026-A93-thm-9`). -/
public theorem_wanted sumOfSquaresRepCount_integer_root (n : ℕ) :
    ∃ P : Polynomial ℤ, (∀ z : ℤ, P.eval z = n.factorial * sumOfSquaresRepCount z n) ∧
      ∀ k : ℤ, k ≠ 0 → sumOfSquaresRepCount k n = 0 →
        k ∣ P.coeff 1 ∧
          ∃ i < n, (|k| : ℝ) < 2 * (|P.coeff i| : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - i))

/-- **Integer roots of triangular representation numbers.** For an integer $k$, let $t_k(n)$ be the
coefficient of $q^n$ in $\psi(q)^k$, where $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$. For every
natural number $n$ there is a polynomial $P(z) = \sum_i a_i z^i$ with integer coefficients such that
$P(z) = n!\, t_z(n)$ for every integer $z$, and every nonzero integer $k$ with $t_k(n) = 0$ divides
$a_1$ and satisfies $|k| < 2 |a_i|^{1/(n-i)}$ for some $i < n$.

For $n \ge 1$ the bound says $|k| < 2 \max_{0 \le i \le n-1} |a_i|^{1/(n-i)}$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 10 (`integers-2026-A93-thm-10`). -/
public theorem_wanted sumOfTriangularRepCount_integer_root (n : ℕ) :
    ∃ P : Polynomial ℤ, (∀ z : ℤ, P.eval z = n.factorial * sumOfTriangularRepCount z n) ∧
      ∀ k : ℤ, k ≠ 0 → sumOfTriangularRepCount k n = 0 →
        k ∣ P.coeff 1 ∧
          ∃ i < n, (|k| : ℝ) < 2 * (|P.coeff i| : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - i))

end

end MetaMathlibExt
