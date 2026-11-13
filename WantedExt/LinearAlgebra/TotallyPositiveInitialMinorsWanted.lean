/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.PositiveMinors
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Totally positive matrices and initial minors

Statement-only targets from Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui,
*Total Positivity of Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal
of Integer Sequences 29 (2026), Article 26.2.5: the Gasca–Peña criterion it quotes, and its
results on Toeplitz matrices of generalized hyper-Fibonacci numbers.

A real `n × n` matrix is totally positive (`Matrix.HasPositiveMinors`) when every minor (rows
`r 0 < ⋯ < r (k-1)`, columns `c 0 < ⋯ < c (k-1)`) is positive. An initial minor uses
consecutive rows and consecutive columns, at least one of the two blocks starting at the first
index.

`W_{p,n}` is `generalizedPFibonacci p a b n` and `W_{p,n}^{(r)}` is
`generalizedHyperFibonacci p a b r n`; the hyper `p`-Fibonacci and hyper `p`-Lucas numbers are
the cases `(a, b) = (0, 1)` and `(2, p)` (bridges to `lucasU` and `lucasV`). The `m × m` Toeplitz
matrix `T_{m,n}^{(r)}` has entry `W_{p,n+i-j}^{(r)}` in row `i`, column `j` (`0 ≤ i, j < m`); all
statements about it are for large `n`, where every index is nonnegative, so natural subtraction
is harmless. `TP_k` (every minor of order at most `k` positive) is written out with the same
strictly increasing row and column maps as `Matrix.HasPositiveMinors`. The paper's standing
hypotheses are `p ≥ 1`, `a ≥ 0`, `b > 0`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Gasca–Peña criterion for total positivity.** Let $A$ be a real $n \times n$ matrix whose
rows and columns are indexed by $0, \dots, n - 1$. Then $A$ is totally positive (has positive
minors) if and only if all its initial minors are positive: for all natural numbers $k$, $i_0$
and $j_0$ with $i_0 + k \le n$, $j_0 + k \le n$ and $i_0 = 0$ or $j_0 = 0$, the $k \times k$
submatrix of $A$ with rows $i_0, \dots, i_0 + k - 1$ and columns $j_0, \dots, j_0 + k - 1$ has
positive determinant.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz
Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29 (2026),
Article 26.2.5, Theorem 3, quoting Gasca and Peña (`jis-2026-26.2.5-thm-3`). -/
public theorem_wanted hasPositiveMinors_iff_initial_minors_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.HasPositiveMinors A ↔
      ∀ (k i₀ j₀ : ℕ) (hi : i₀ + k ≤ n) (hj : j₀ + k ≤ n), (i₀ = 0 ∨ j₀ = 0) →
        0 < (A.submatrix (fun r : Fin k => (⟨i₀ + r, by omega⟩ : Fin n))
          (fun c : Fin k => (⟨j₀ + c, by omega⟩ : Fin n))).det

/-- **Generalized $p$-Fibonacci sequence.** For integers $p$, $a$ and $b$, the generalized
Fibonacci sequence $(W_{p,n})_{n \ge 0}$ of integers is defined by $W_{p,0} = a$, $W_{p,1} = b$
and $W_{p,n} = p W_{p,n-1} + W_{p,n-2}$ for $n \ge 2$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, recurrence (1). -/
public def generalizedPFibonacci (p a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => p * generalizedPFibonacci p a b (n + 1) + generalizedPFibonacci p a b n

/-- **$p$-Fibonacci numbers as a Lucas sequence.** For every integer $p$, the generalized
Fibonacci sequence $W_{p,n}$ with initial values $a = 0$ and $b = 1$ (the $p$-Fibonacci numbers
$F_{p,n}$) is the Lucas sequence $U(p, -1)$: $W_{p,n} = U_n(p, -1)$ for every natural number $n$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, remark after recurrence (1) (`p`-Fibonacci
numbers `F_{p,n}`). -/
public theorem generalizedPFibonacci_zero_one (p : ℤ) (n : ℕ) :
    generalizedPFibonacci p 0 1 n = lucasU ⟨p, -1, by decide⟩ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    simp only [generalizedPFibonacci, lucasU, ih1, ih2]
    ring

/-- **$p$-Lucas numbers as a companion Lucas sequence.** For every integer $p$, the generalized
Fibonacci sequence $W_{p,n}$ with initial values $a = 2$ and $b = p$ (the $p$-Lucas numbers
$L_{p,n}$) is the companion Lucas sequence $V(p, -1)$: $W_{p,n} = V_n(p, -1)$ for every natural
number $n$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, remark after recurrence (1) (`p`-Lucas numbers
`L_{p,n}`). -/
public theorem generalizedPFibonacci_two_p (p : ℤ) (n : ℕ) :
    generalizedPFibonacci p 2 p n = lucasV ⟨p, -1, by decide⟩ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    simp only [generalizedPFibonacci, lucasV, ih1, ih2]
    ring

/-- **Generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers and let $W_{p,n}$ denote the
generalized Fibonacci sequence, with $W_{p,0} = a$, $W_{p,1} = b$ and
$W_{p,n+2} = p W_{p,n+1} + W_{p,n}$. The generalized hyper-Fibonacci numbers $W^{(r)}_{p,n}$, for
natural numbers $r$ and $n$, are the integers defined by $W^{(0)}_{p,n} = W_{p,n}$ and, for
$r \ge 1$, by $W^{(r)}_{p,n} = \sum_{k=0}^{n} p^{n-k} W^{(r-1)}_{p,k}$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, definition (2). -/
public def generalizedHyperFibonacci (p a b : ℤ) : ℕ → ℕ → ℤ
  | 0 => generalizedPFibonacci p a b
  | r + 1 => fun n =>
      ∑ k ∈ Finset.range (n + 1), p ^ (n - k) * generalizedHyperFibonacci p a b r k

/-- **Initial values of generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers and let
$W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci numbers. For every natural number $r$,
$W^{(r)}_{p,0} = a$ and $W^{(r)}_{p,1} = p \cdot a \cdot r + b$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, definition (2) (initial values). -/
public theorem generalizedHyperFibonacci_zero_one (p a b : ℤ) (r : ℕ) :
    generalizedHyperFibonacci p a b r 0 = a ∧
      generalizedHyperFibonacci p a b r 1 = p * a * r + b := by
  induction r with
  | zero => exact ⟨rfl, by simp [generalizedHyperFibonacci, generalizedPFibonacci]⟩
  | succ r ih =>
    refine ⟨?_, ?_⟩
    · simp [generalizedHyperFibonacci, ih.1]
    · simp only [generalizedHyperFibonacci, Finset.sum_range_succ, Finset.sum_range_zero,
        ih.1, ih.2]
      push_cast
      ring

/-- **Recurrence for generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers and let
$W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci numbers. For all natural numbers $r \ge 1$
and $n \ge 1$, $W^{(r)}_{p,n} = p W^{(r)}_{p,n-1} + W^{(r-1)}_{p,n}$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Lemma 5, identity (3), quoting Ait-Amrane et al.
(`jis-2026-26.2.5-lem-5`). -/
public theorem_wanted generalizedHyperFibonacci_succ_succ (p a b : ℤ) (r n : ℕ) :
    generalizedHyperFibonacci p a b (r + 1) (n + 1) =
      p * generalizedHyperFibonacci p a b (r + 1) n + generalizedHyperFibonacci p a b r (n + 1)

/-- **A binomial-sum formula for generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers
with $p \ne 0$, let $W_{p,n}$ denote the generalized Fibonacci sequence and $W^{(r)}_{p,n}$ the
generalized hyper-Fibonacci numbers. For all natural numbers $r$ and $n$ with $1 \le r \le n$, the
following identity of rational numbers holds:
$$
W^{(r)}_{p,n-r} = W_{p,n+r} - \frac{p^n}{p^{r-1}} \sum_{k=0}^{r-1} \binom{n-k-1}{r-k-1} W_{p,2k+1}.
$$

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Lemma 5, identity (4), quoting Ait-Amrane et al.
(`jis-2026-26.2.5-lem-5`). -/
public theorem_wanted generalizedHyperFibonacci_sub_eq_sub (p a b : ℤ) (hp : p ≠ 0) (r n : ℕ)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (generalizedHyperFibonacci p a b r (n - r) : ℚ) =
      generalizedPFibonacci p a b (n + r) -
        (p : ℚ) ^ n * (∑ k ∈ Finset.range r,
          ((n - k - 1).choose (r - k - 1) : ℚ) * generalizedPFibonacci p a b (2 * k + 1)) /
          (p : ℚ) ^ (r - 1)

/-- **Hankel determinants of generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers, let
$W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci numbers and put $\Delta = a^2 + pab - b^2$.
For all natural numbers $r$ and $n$, the $(r+2) \times (r+2)$ Hankel matrix
$H_{r,n} = (W^{(r)}_{p,n+i+j})_{0 \le i, j \le r+1}$ has determinant
$\det H_{r,n} = (-1)^{n+1+\lfloor (r+3)/2 \rfloor} p^{nr+r^2} b^r \Delta$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Proposition 7, quoting Ait-Amrane et al.
(`jis-2026-26.2.5-prop-7`). -/
public theorem_wanted generalizedHyperFibonacci_hankel_det (p a b : ℤ) (r n : ℕ) :
    (Matrix.of fun i j : Fin (r + 2) =>
        generalizedHyperFibonacci p a b r (n + i + j)).det =
      (-1) ^ (n + 1 + (r + 3) / 2) * p ^ (n * r + r ^ 2) * b ^ r * (a ^ 2 + p * a * b - b ^ 2)

/-- **Eventual positivity of hyper-Fibonacci Toeplitz determinants.** Let $p, a, b$ be integers
with $p \ge 1$, $a \ge 0$ and $b > 0$, and let $W^{(r)}_{p,n}$ denote the generalized
hyper-Fibonacci numbers. For every natural number $m \ge 1$ there is a natural number $N$ such
that for every $n \ge N$ the $m \times m$ Toeplitz matrix with entry $W^{(m-1)}_{p,n+i-j}$ in row
$i$ and column $j$ ($0 \le i, j < m$) has positive determinant.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Theorem 8 (`jis-2026-26.2.5-thm-8`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_det_eventually_pos (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < (Matrix.of fun i j : Fin m =>
      generalizedHyperFibonacci p a b (m - 1) (n + i - j)).det

/-- **Eventual positivity of lower-order hyper-Fibonacci Toeplitz determinants.** Let $p, a, b$ be
integers with $p \ge 1$, $a \ge 0$ and $b > 0$, and let $W^{(r)}_{p,n}$ denote the generalized
hyper-Fibonacci numbers. For natural numbers $r$, $m$ and $n$ write $T^{(r)}_{m,n}$ for the
$m \times m$ Toeplitz matrix with entry $W^{(r)}_{p,n+i-j}$ in row $i$ and column $j$
($0 \le i, j < m$). If $r \ge 1$ and $1 \le m \le r + 1$, then there is a natural number $N$ such
that $\det T^{(r)}_{m,n} > 0$ for every $n \ge N$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 9 (`jis-2026-26.2.5-cor-9`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_det_eventually_pos_of_le (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ r + 1) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < (Matrix.of fun i j : Fin m =>
      generalizedHyperFibonacci p a b r (n + i - j)).det

/-- **Eventual log-concavity of generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers
with $p \ge 1$, $a \ge 0$ and $b > 0$, let $W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci
numbers, and let $r \ge 1$ be a natural number. Then there is a natural number $N$ such that for
every $n \ge N$ we have $W^{(r)}_{p,n} > 0$ and
$W^{(r)}_{p,n} W^{(r)}_{p,n+2} \le (W^{(r)}_{p,n+1})^2$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 10 (`jis-2026-26.2.5-cor-10`). -/
public theorem_wanted generalizedHyperFibonacci_eventually_logConcave (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p a b r n ∧
      generalizedHyperFibonacci p a b r n * generalizedHyperFibonacci p a b r (n + 2) ≤
        generalizedHyperFibonacci p a b r (n + 1) ^ 2

/-- **Eventual log-concavity of hyper $p$-Fibonacci and hyper $p$-Lucas numbers.** Let
$p \ge 1$ be an integer and $r \ge 1$ a natural number, and let $F_{p,n}^{(r)}$ and
$L_{p,n}^{(r)}$ be the generalized hyper-Fibonacci numbers $W_{p,n}^{(r)}$ with initial values
$(a, b) = (0, 1)$ and $(a, b) = (2, p)$ respectively (the hyper $p$-Fibonacci and hyper
$p$-Lucas numbers). Both sequences are eventually log-concave: there is $N$ such that for all
$n \ge N$, $F_{p,n}^{(r)} > 0$ and $F_{p,n}^{(r)} F_{p,n+2}^{(r)} \le (F_{p,n+1}^{(r)})^2$, and
there is $N'$ such that for all $n \ge N'$, $L_{p,n}^{(r)} > 0$ and
$L_{p,n}^{(r)} L_{p,n+2}^{(r)} \le (L_{p,n+1}^{(r)})^2$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 11 (`jis-2026-26.2.5-cor-11`). -/
public theorem_wanted hyperPFibonacci_hyperPLucas_eventually_logConcave (p : ℤ) (hp : 1 ≤ p)
    (r : ℕ) (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p 0 1 r n ∧
      generalizedHyperFibonacci p 0 1 r n * generalizedHyperFibonacci p 0 1 r (n + 2) ≤
        generalizedHyperFibonacci p 0 1 r (n + 1) ^ 2) ∧
    (∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p 2 p r n ∧
      generalizedHyperFibonacci p 2 p r n * generalizedHyperFibonacci p 2 p r (n + 2) ≤
        generalizedHyperFibonacci p 2 p r (n + 1) ^ 2)

/-- **Eventual total positivity of hyper-Fibonacci Toeplitz matrices.** Let $p, a, b$ be integers
with $p \ge 1$, $a \ge 0$ and $b > 0$, put $\Delta = a^2 + pab - b^2$, let $W^{(r)}_{p,n}$
denote the generalized hyper-Fibonacci numbers, and let $r \ge 1$ be a natural number. For a
natural number $s$ write $T_s$ for the real $(r+2) \times (r+2)$ Toeplitz matrix with entry
$W^{(r)}_{p,s+i-j}$ in row $i$ and column $j$ ($0 \le i, j \le r+1$). If $\Delta > 0$, there is a
natural number $N$ such that $T_{2n}$ has positive minors (is totally positive) for every
$n \ge N$; if $\Delta < 0$, there is a natural number $N$ such that $T_{2n+1}$ has positive
minors for every $n \ge N$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Theorem 12 (`jis-2026-26.2.5-thm-12`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_hasPositiveMinors (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    (0 < a ^ 2 + p * a * b - b ^ 2 → ∃ N : ℕ, ∀ n ≥ N,
      Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
        (generalizedHyperFibonacci p a b r (2 * n + i - j) : ℝ))) ∧
    (a ^ 2 + p * a * b - b ^ 2 < 0 → ∃ N : ℕ, ∀ n ≥ N,
      Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
        (generalizedHyperFibonacci p a b r (2 * n + 1 + i - j) : ℝ)))

/-- **Eventually positive bounded-order minors of hyper-Fibonacci Toeplitz matrices.** Let
$p, a, b$ be integers with $p \ge 1$, $a \ge 0$ and $b > 0$, let $W^{(r)}_{p,n}$ denote the
generalized hyper-Fibonacci numbers, and let $r \ge 1$ be a natural number. For a natural number
$n$ let $T_n$ be the real $(r+2) \times (r+2)$ Toeplitz matrix with entry $W^{(r)}_{p,n+i-j}$ in
row $i$ and column $j$ ($0 \le i, j \le r+1$). Then there is a natural number $N$ such that for
every $n \ge N$, every natural number $k \le r + 1$ and all strictly increasing maps
$\rho, \gamma : \{0, \dots, k-1\} \to \{0, \dots, r+1\}$, the $k \times k$ submatrix
$((T_n)_{\rho(u), \gamma(v)})_{0 \le u, v < k}$ has positive determinant; that is, every minor
of $T_n$ of order at most $r + 1$ is positive.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 13 (`jis-2026-26.2.5-cor-13`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_positiveMinors_le (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ r + 1, ∀ (rows cols : Fin k → Fin (r + 2)),
      StrictMono rows → StrictMono cols →
        0 < ((Matrix.of fun i j : Fin (r + 2) =>
          (generalizedHyperFibonacci p a b r (n + i - j) : ℝ)).submatrix rows cols).det

/-- **Total positivity of hyper $p$-Fibonacci Toeplitz matrices.** Let $p \ge 1$ be an integer
and $r \ge 1$ a natural number, and let $F_{p,n}^{(r)}$ be the hyper $p$-Fibonacci numbers, the
generalized hyper-Fibonacci numbers $W_{p,n}^{(r)}$ with initial values $a = 0$ and $b = 1$.
Consider real $(r + 2) \times (r + 2)$ matrices with rows and columns indexed by
$0, \dots, r + 1$. For all sufficiently large $n$, the Toeplitz matrix with entry
$F_{p,2n+1+i-j}^{(r)}$ in row $i$ and column $j$ is totally positive. Moreover, for all
sufficiently large $n$, the Toeplitz matrix with entry $F_{p,n+i-j}^{(r)}$ in row $i$ and
column $j$ is $\mathrm{TP}_{r+1}$: each of its minors of order at most $r + 1$ is positive.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 14 (`jis-2026-26.2.5-cor-14`). -/
public theorem_wanted hyperPFibonacci_toeplitz_hasPositiveMinors (p : ℤ) (hp : 1 ≤ p) (r : ℕ)
    (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
      (generalizedHyperFibonacci p 0 1 r (2 * n + 1 + i - j) : ℝ))) ∧
    (∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ r + 1, ∀ (rows cols : Fin k → Fin (r + 2)),
      StrictMono rows → StrictMono cols →
        0 < ((Matrix.of fun i j : Fin (r + 2) =>
          (generalizedHyperFibonacci p 0 1 r (n + i - j) : ℝ)).submatrix rows cols).det)

/-- **Total positivity of hyper $p$-Lucas Toeplitz matrices.** Let $p \ge 1$ be an integer and
$r \ge 1$ a natural number, and let $L_{p,n}^{(r)}$ be the hyper $p$-Lucas numbers, the
generalized hyper-Fibonacci numbers $W_{p,n}^{(r)}$ with initial values $a = 2$ and $b = p$.
Consider real $(r + 2) \times (r + 2)$ matrices with rows and columns indexed by
$0, \dots, r + 1$. For all sufficiently large $n$, the Toeplitz matrix with entry
$L_{p,2n+i-j}^{(r)}$ in row $i$ and column $j$ is totally positive. Moreover, for all
sufficiently large $n$, the Toeplitz matrix with entry $L_{p,n+i-j}^{(r)}$ in row $i$ and
column $j$ is $\mathrm{TP}_{r+1}$: each of its minors of order at most $r + 1$ is positive.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 15 (`jis-2026-26.2.5-cor-15`). -/
public theorem_wanted hyperPLucas_toeplitz_hasPositiveMinors (p : ℤ) (hp : 1 ≤ p) (r : ℕ)
    (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
      (generalizedHyperFibonacci p 2 p r (2 * n + i - j) : ℝ))) ∧
    (∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ r + 1, ∀ (rows cols : Fin k → Fin (r + 2)),
      StrictMono rows → StrictMono cols →
        0 < ((Matrix.of fun i j : Fin (r + 2) =>
          (generalizedHyperFibonacci p 2 p r (n + i - j) : ℝ)).submatrix rows cols).det)

end

end MetaMathlibExt
