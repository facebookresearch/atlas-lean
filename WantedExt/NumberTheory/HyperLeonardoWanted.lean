/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import WantedExt.NumberTheory.GenLeonardoWanted

/-!
# Hyper-Leonardo numbers

Statements from Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
*A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48.

The Leonardo numbers are `genLeonardo 1` (`Le₀ = Le₁ = 1`, `Le_{n+2} = Le_{n+1} + Le_n + 1`).
The hyper-Leonardo numbers are their iterated partial sums,
`Le^{(0)}_n = Le_n` and `Le^{(r)}_n = ∑_{k=0}^{n} Le^{(r-1)}_k`; the hyper-Fibonacci numbers
`F^{(r)}_n` are the iterated partial sums of `Nat.fib`.
-/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- **Hyper-Leonardo numbers.** Let $Le_n$ be the Leonardo numbers, defined by
$Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$. The hyper-Leonardo numbers are the
integers $Le^{(r)}_n$, for $r, n \ge 0$, defined by $Le^{(0)}_n = Le_n$ and
$Le^{(r+1)}_n = \sum_{k=0}^{n} Le^{(r)}_k$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Definition 1, as displayed in
the derivation `Le^{(1)}_n = ∑_{k=0}^{n} Le^{(0)}_k` after Proposition 5
(`integers-2026-A48-prop-5`). -/
def hyperLeonardo : ℕ → ℕ → ℤ
  | 0, n => genLeonardo 1 n
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hyperLeonardo r k

/-- **Hyper-Leonardo numbers of order zero.** For every natural number $n$, the hyper-Leonardo
number $Le^{(0)}_n$ equals the Leonardo number $L_{1,n}$, the generalized Leonardo number with
$k = 1$, given by $L_{1,0} = L_{1,1} = 1$ and $L_{1,n+2} = L_{1,n+1} + L_{1,n} + 1$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Definition 1. -/
theorem hyperLeonardo_zero (n : ℕ) : hyperLeonardo 0 n = genLeonardo 1 n := rfl

/-- **Hyper-Leonardo numbers as partial sums.** For all natural numbers $r$ and $n$, the
hyper-Leonardo numbers $Le^{(r)}_n$ satisfy $Le^{(r+1)}_n = \sum_{k=0}^{n} Le^{(r)}_k$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Definition 1. -/
theorem hyperLeonardo_succ (r n : ℕ) :
    hyperLeonardo (r + 1) n = ∑ k ∈ Finset.range (n + 1), hyperLeonardo r k := rfl

/-- **First hyper-Leonardo numbers of order one.** The hyper-Leonardo numbers $Le^{(1)}_n$ of
order $1$ satisfy $Le^{(1)}_0 = 1$, $Le^{(1)}_1 = 2$, $Le^{(1)}_2 = 5$ and $Le^{(1)}_3 = 10$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, Proposition 1
(`Le^{(1)}_0 = 1`, `Le^{(1)}_1 = 2`). -/
theorem hyperLeonardo_one_small :
    hyperLeonardo 1 0 = 1 ∧ hyperLeonardo 1 1 = 2 ∧ hyperLeonardo 1 2 = 5 ∧
      hyperLeonardo 1 3 = 10 := by
  simp [hyperLeonardo, Finset.sum_range_succ, genLeonardo]

/-- **Hyper-Fibonacci numbers.** The hyper-Fibonacci numbers $F^{(r)}_n$, for natural numbers $r$
and $n$, are the natural numbers defined by $F^{(0)}_n = F_n$, the $n$-th Fibonacci number
(with $F_0 = 0$ and $F_1 = 1$), and $F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, the hyper-Fibonacci
numbers `F^{(r)}_{n+1} = ∑_{k=0}^{n+1} F^{(r-1)}_k` displayed after Proposition 5
(`integers-2026-A48-prop-5`). -/
def hyperFibonacci : ℕ → ℕ → ℕ
  | 0, n => Nat.fib n
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hyperFibonacci r k

/-- **Hyper-Fibonacci numbers of order zero.** For every natural number $n$, the hyper-Fibonacci
number $F^{(0)}_n$ equals the $n$-th Fibonacci number $F_n$ (with $F_0 = 0$ and $F_1 = 1$).

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5. -/
theorem hyperFibonacci_zero (n : ℕ) : hyperFibonacci 0 n = Nat.fib n := rfl

/-- **Hyper-Fibonacci numbers as partial sums.** For all natural numbers $r$ and $n$, the
hyper-Fibonacci numbers $F^{(r)}_n$ satisfy $F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5. -/
theorem hyperFibonacci_succ (r n : ℕ) :
    hyperFibonacci (r + 1) n = ∑ k ∈ Finset.range (n + 1), hyperFibonacci r k := rfl

/-- **Small values of the hyper-Fibonacci numbers of order one.** The hyper-Fibonacci numbers
$F^{(1)}_n$ of order $1$ satisfy $F^{(1)}_0 = 0$, $F^{(1)}_1 = 1$, $F^{(1)}_2 = 2$ and
$F^{(1)}_3 = 4$.

Source: Spreafico and Catarino, INTEGERS 26 (2026), Article A48, after Proposition 5
(`F^{(r)}_0 = 0`). -/
theorem hyperFibonacci_one_small :
    hyperFibonacci 1 0 = 0 ∧ hyperFibonacci 1 1 = 1 ∧ hyperFibonacci 1 2 = 2 ∧
      hyperFibonacci 1 3 = 4 := by
  simp [hyperFibonacci, Finset.sum_range_succ, Nat.fib_add_two]

/-- **Recurrences for the hyper-Leonardo numbers of orders zero, one and two.** The
hyper-Leonardo numbers $Le^{(r)}_n$ satisfy $Le^{(0)}_0 = Le^{(0)}_1 = 1$, $Le^{(1)}_0 = 1$,
$Le^{(1)}_1 = 2$, $Le^{(2)}_0 = 1$ and $Le^{(2)}_1 = 3$, and for every natural number $n \ge 2$,
$$Le^{(0)}_n = Le^{(0)}_{n-1} + Le^{(0)}_{n-2} + 1,$$
$$Le^{(1)}_n = Le^{(1)}_{n-1} + Le^{(1)}_{n-2} + \binom{n-1}{1} + 1,$$
$$Le^{(2)}_n = Le^{(2)}_{n-1} + Le^{(2)}_{n-2} + \binom{n}{2} + \binom{n-1}{1} + 2.$$

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 1
(`integers-2026-A48-prop-1`). -/
public theorem_wanted hyperLeonardo_recurrence_small_order :
    (∀ n, hyperLeonardo 0 (n + 2) = hyperLeonardo 0 (n + 1) + hyperLeonardo 0 n + 1) ∧
    hyperLeonardo 0 0 = 1 ∧ hyperLeonardo 0 1 = 1 ∧
    (∀ n, hyperLeonardo 1 (n + 2) =
      hyperLeonardo 1 (n + 1) + hyperLeonardo 1 n + ((n + 1).choose 1 : ℕ) + 1) ∧
    hyperLeonardo 1 0 = 1 ∧ hyperLeonardo 1 1 = 2 ∧
    (∀ n, hyperLeonardo 2 (n + 2) = hyperLeonardo 2 (n + 1) + hyperLeonardo 2 n +
      ((n + 2).choose 2 : ℕ) + ((n + 1).choose 1 : ℕ) + 2) ∧
    hyperLeonardo 2 0 = 1 ∧ hyperLeonardo 2 1 = 3

/-- **Recurrence for the hyper-Leonardo numbers.** For every natural number $r$, the
hyper-Leonardo numbers $Le^{(r)}_n$ of order $r$ satisfy $Le^{(r)}_0 = 1$, $Le^{(r)}_1 = r + 1$
and, for every natural number $n \ge 2$,
$Le^{(r)}_n = r + Le^{(r)}_{n-1} + Le^{(r)}_{n-2} + \binom{n+r-2}{r} +
\sum_{j=1}^{r-1} j \binom{n+r-2-j}{r-j}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 2
(`integers-2026-A48-prop-2`). -/
public theorem_wanted hyperLeonardo_recurrence (r : ℕ) :
    (∀ n, hyperLeonardo r (n + 2) = r + hyperLeonardo r (n + 1) + hyperLeonardo r n +
      ((n + r).choose r : ℕ) +
        ∑ j ∈ Finset.Ico 1 r, (j * (n + r - j).choose (r - j) : ℕ)) ∧
    hyperLeonardo r 0 = 1 ∧ hyperLeonardo r 1 = r + 1

/-- **Recurrence across consecutive orders of hyper-Leonardo numbers.** For all natural numbers
$r \ge 1$ and $n \ge 1$, the hyper-Leonardo numbers $Le^{(r)}_n$ satisfy
$Le^{(r)}_n = Le^{(r)}_{n-1} + Le^{(r-1)}_n$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 3, Equation (4)
(`integers-2026-A48-prop-3`). -/
public theorem_wanted hyperLeonardo_succ_succ (r n : ℕ) :
    hyperLeonardo (r + 1) (n + 1) = hyperLeonardo (r + 1) n + hyperLeonardo r (n + 1)

/-- **Consecutive hyper-Leonardo numbers of order one.** For every natural number $n$, the
hyper-Leonardo numbers $Le^{(1)}_n$ of order $1$ satisfy
$Le^{(1)}_{n+1} = Le^{(1)}_n + L_{1,n+1}$, where $L_{1,n}$ is the generalized Leonardo number
with $k = 1$, that is, the Leonardo number $Le_n$.

This is the case $r = 1$ of the recurrence $Le^{(r)}_n = Le^{(r)}_{n-1} + Le^{(r-1)}_n$. The
extracted text of the source reads $Le^{(1)}_n = Le_{n-1} + Le_n$, which fails at $n = 2$, where
$Le^{(1)}_2 = 5$ but $Le_1 + Le_2 = 4$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 1, Equation (5)
(`integers-2026-A48-cor-1`). -/
public theorem_wanted hyperLeonardo_one_succ (n : ℕ) :
    hyperLeonardo 1 (n + 1) = hyperLeonardo 1 n + genLeonardo 1 (n + 1)

/-- **Generating function of shifted binomial coefficients.** For every natural number $r$, the
formal power series $\sum_{n \ge 0} \binom{n+r}{r} t^n$ with integer coefficients satisfies
$\left(\sum_{n \ge 0} \binom{n+r}{r} t^n\right)(1-t)^{r+1} = 1$ in $\mathbb{Z}[[t]]$, that is,
$\sum_{n \ge 0} \binom{n+r}{r} t^n = 1/(1-t)^{r+1}$.

The paper states this for positive $r$; it holds for every $r \ge 0$ and is stated so.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Lemma 2
(`integers-2026-A48-lem-2`). -/
public theorem choose_add_powerSeries_mul_one_sub_pow (r : ℕ) :
    PowerSeries.mk (fun n => (((n + r).choose r : ℕ) : ℤ)) * (1 - X) ^ (r + 1) = 1 := by
  have h : PowerSeries.mk (fun n => (((n + r).choose r : ℕ) : ℤ)) =
      (PowerSeries.mk 1 : ℤ⟦X⟧) ^ (r + 1) := by
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    congr 1
    funext n
    rw [add_comm]
  rw [h, ← mul_pow, PowerSeries.mk_one_mul_one_sub_eq_one, one_pow]

/-- **The convolution of log-concave sequences is log-concave.** Let $(x_n)_{n \ge 0}$ and
$(y_n)_{n \ge 0}$ be sequences of positive real numbers that are log-concave, that is,
$x_{j-1} x_{j+1} \le x_j^2$ and $y_{j-1} y_{j+1} \le y_j^2$ for every $j \ge 1$. Let
$z_n = \sum_{k=0}^{n} x_k y_{n-k}$ be their convolution. Then $z_{j-1} z_{j+1} \le z_j^2$ for
every $j \ge 1$.

Positivity is the paper's standing assumption on log-concave sequences.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Lemma 3, quoting [1]
(`integers-2026-A48-lem-3`). -/
public theorem_wanted logConcave_convolution (x y : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hy : ∀ n, 0 < y n) (hxlc : ∀ j, 1 ≤ j → x (j - 1) * x (j + 1) ≤ x j ^ 2)
    (hylc : ∀ j, 1 ≤ j → y (j - 1) * y (j + 1) ≤ y j ^ 2) (j : ℕ) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.range j, x k * y (j - 1 - k)) *
        (∑ k ∈ Finset.range (j + 2), x k * y (j + 1 - k)) ≤
      (∑ k ∈ Finset.range (j + 1), x k * y (j - k)) ^ 2

/-- **Generating function of the Leonardo numbers.** Let $Le_n$ be the Leonardo numbers
($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$), and let
$L(t) = \sum_{n \ge 0} Le_n t^n$ in the ring $\mathbb{Z}[[t]]$ of formal power series. Then
$L(t)(1 - 2t + t^3) = 1 - t + t^2$ and $L(t)(1 - t - t^2)(1 - t) = 2(1 - t) - (1 - t - t^2)$.

Equivalently, $L(t) = \frac{2}{1-t-t^2} - \frac{1}{1-t} = \frac{1-t+t^2}{1-2t+t^3}$; the
identities above are this equality with the denominators cleared.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 2
(`integers-2026-A48-cor-2`). -/
public theorem_wanted leonardo_generatingFunction :
    PowerSeries.mk (fun n => genLeonardo 1 n) * (1 - 2 * X + X ^ 3) = 1 - X + X ^ 2 ∧
      PowerSeries.mk (fun n => genLeonardo 1 n) * ((1 - X - X ^ 2) * (1 - X)) =
        2 * (1 - X) - (1 - X - X ^ 2)

/-- **Generating functions of the hyper-Leonardo numbers of orders one and two.** In the ring
$\mathbb{Z}[[t]]$ of formal power series, the hyper-Leonardo numbers $Le^{(r)}_n$ satisfy
$\left(\sum_{n \ge 0} Le^{(1)}_n t^n\right)(1 - 2t + t^3)(1 - t) = 1 - t + t^2$ and
$\left(\sum_{n \ge 0} Le^{(2)}_n t^n\right)(1 - 2t + t^3)(1 - t)^2 = 1 - t + t^2$.

Equivalently, the two generating functions are $\frac{1 - t + t^2}{(1 - 2t + t^3)(1 - t)}$ and
$\frac{1 - t + t^2}{(1 - 2t + t^3)(1 - t)^2}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Corollary 3
(`integers-2026-A48-cor-3`). -/
public theorem_wanted hyperLeonardo_one_two_generatingFunction :
    PowerSeries.mk (fun n => hyperLeonardo 1 n) * ((1 - 2 * X + X ^ 3) * (1 - X)) =
        1 - X + X ^ 2 ∧
      PowerSeries.mk (fun n => hyperLeonardo 2 n) * ((1 - 2 * X + X ^ 3) * (1 - X) ^ 2) =
        1 - X + X ^ 2

/-- **Generating function of the hyper-Leonardo numbers.** For every natural number $r$, the
formal power series $\sum_{n \ge 0} \mathrm{Le}^{(r)}_n t^n$ of the hyper-Leonardo numbers of
order $r$ satisfies
$\left(\sum_{n \ge 0} \mathrm{Le}^{(r)}_n t^n\right)(1-2t+t^3)(1-t)^r = 1-t+t^2$ in
$\mathbb{Z}[[t]]$, that is,
$\sum_{n \ge 0} \mathrm{Le}^{(r)}_n t^n = \frac{1-t+t^2}{(1-2t+t^3)(1-t)^r}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Theorem 1, Equation (10)
(`integers-2026-A48-thm-1`). -/
public theorem_wanted hyperLeonardo_generatingFunction (r : ℕ) :
    PowerSeries.mk (fun n => hyperLeonardo r n) * ((1 - 2 * X + X ^ 3) * (1 - X) ^ r) =
      1 - X + X ^ 2

/-- **Hyper-Leonardo numbers in terms of hyper-Fibonacci numbers.** For all natural numbers $r$
and $n$, the hyper-Leonardo number $\mathrm{Le}^{(r)}_n$ and the hyper-Fibonacci number
$F^{(r)}_{n+1}$ satisfy $\mathrm{Le}^{(r)}_n = 2F^{(r)}_{n+1} - \binom{n+r}{r}$ as integers.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 6, Equation (9)
(`integers-2026-A48-prop-6`). -/
public theorem_wanted hyperLeonardo_eq_hyperFibonacci (r n : ℕ) :
    hyperLeonardo r n = 2 * (hyperFibonacci r (n + 1) : ℤ) - ((n + r).choose r : ℕ)

/-- **Log-convexity and log-concavity of the Leonardo numbers.** Let $Le_n$ be the Leonardo
numbers ($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$). Then
$Le_n^2 \le Le_{n-1} Le_{n+1}$ for $n = 1$ and $n = 3$, $Le_5^2 = Le_4 Le_6$, and
$Le_{n-1} Le_{n+1} \le Le_n^2$ for $n = 2$, $n = 4$ and every $n \ge 6$.

The paper's "the sequence is log-convex for $n = 1$" is read as the defining inequality at
index $n$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 10
(`integers-2026-A48-prop-10`). -/
public theorem_wanted leonardo_logConvex_logConcave_pointwise :
    (∀ n ∈ ({1, 3} : Finset ℕ),
      genLeonardo 1 n ^ 2 ≤ genLeonardo 1 (n - 1) * genLeonardo 1 (n + 1)) ∧
    genLeonardo 1 5 ^ 2 = genLeonardo 1 4 * genLeonardo 1 6 ∧
    (∀ n, n = 2 ∨ n = 4 ∨ 6 ≤ n →
      genLeonardo 1 (n - 1) * genLeonardo 1 (n + 1) ≤ genLeonardo 1 n ^ 2)

/-- **Leonardo numbers are log-balanced at index three.** Let $Le_n$ be the Leonardo numbers
($Le_0 = Le_1 = 1$ and $Le_{n+2} = Le_{n+1} + Le_n + 1$). Then $Le_3^2 \le Le_2 Le_4$ and
$\frac{Le_2}{2!} \cdot \frac{Le_4}{4!} \le \left(\frac{Le_3}{3!}\right)^2$, the second
inequality in the real numbers. That is, $(Le_n)$ satisfies the log-convexity inequality at
$n = 3$ and $(Le_n / n!)$ satisfies the log-concavity inequality at $n = 3$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 11, with the
definition of log-balanced displayed before Proposition 10 (`integers-2026-A48-prop-11`). -/
public theorem_wanted leonardo_logBalanced_three :
    genLeonardo 1 3 ^ 2 ≤ genLeonardo 1 2 * genLeonardo 1 4 ∧
      ((genLeonardo 1 2 : ℝ) / Nat.factorial 2) * ((genLeonardo 1 4 : ℝ) / Nat.factorial 4) ≤
        ((genLeonardo 1 3 : ℝ) / Nat.factorial 3) ^ 2

/-- **Log-convexity and log-concavity of the hyper-Leonardo numbers at index one.** The
hyper-Leonardo numbers $\mathrm{Le}^{(r)}_n$ satisfy
$\left(\mathrm{Le}^{(1)}_1\right)^2 \le \mathrm{Le}^{(1)}_0 \mathrm{Le}^{(1)}_2$, and for every
natural number $r \ge 2$ they satisfy
$\mathrm{Le}^{(r)}_0 \mathrm{Le}^{(r)}_2 \le \left(\mathrm{Le}^{(r)}_1\right)^2$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 12
(`integers-2026-A48-prop-12`). -/
public theorem_wanted hyperLeonardo_logConvex_logConcave_one :
    hyperLeonardo 1 1 ^ 2 ≤ hyperLeonardo 1 0 * hyperLeonardo 1 2 ∧
      ∀ r, 2 ≤ r → hyperLeonardo r 0 * hyperLeonardo r 2 ≤ hyperLeonardo r 1 ^ 2

/-- **Eventual log-concavity of the hyper-Leonardo numbers of order one.** For every natural
number $n \ge 2$, the hyper-Leonardo numbers $Le^{(1)}_n$ of order $1$ satisfy
$Le^{(1)}_{n-1} Le^{(1)}_{n+1} \le (Le^{(1)}_n)^2$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 13
(`integers-2026-A48-prop-13`). -/
public theorem_wanted hyperLeonardo_one_logConcave (n : ℕ) (hn : 2 ≤ n) :
    hyperLeonardo 1 (n - 1) * hyperLeonardo 1 (n + 1) ≤ hyperLeonardo 1 n ^ 2

/-- **Cassini-type identity for hyper-Leonardo numbers.** For all natural numbers $r \ge 1$ and
$n \ge 1$, the hyper-Leonardo numbers $Le^{(r)}_n$ satisfy
$Le^{(r)}_{n-1} Le^{(r)}_{n+1} - (Le^{(r)}_n)^2 =
Le^{(r)}_n Le^{(r-1)}_{n+1} - Le^{(r-1)}_n Le^{(r)}_{n+1}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 4
(`integers-2026-A48-prop-4`). -/
public theorem_wanted hyperLeonardo_mul_sub_sq (r n : ℕ) :
    hyperLeonardo (r + 1) n * hyperLeonardo (r + 1) (n + 2) - hyperLeonardo (r + 1) (n + 1) ^ 2 =
      hyperLeonardo (r + 1) (n + 1) * hyperLeonardo r (n + 2) -
        hyperLeonardo r (n + 1) * hyperLeonardo (r + 1) (n + 2)

/-- **Eventual log-concavity of the hyper-Leonardo numbers of positive order.** For all natural
numbers $r \ge 1$ and $n \ge 2$, the hyper-Leonardo numbers $Le^{(r)}_n$ of order $r$ satisfy
$Le^{(r)}_{n-1} Le^{(r)}_{n+1} \le (Le^{(r)}_n)^2$.

The source states this for $r \ge 0$, but it fails for the Leonardo numbers $Le_n = Le^{(0)}_n$
at $n = 3$, where $Le_2 Le_4 = 27 > 25 = Le_3^2$; the source's proof starts its induction at
$r = 1$ (Proposition 13).

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Proposition 14
(`integers-2026-A48-prop-14`). -/
public theorem_wanted hyperLeonardo_logConcave {r : ℕ} (hr : 1 ≤ r) {n : ℕ} (hn : 2 ≤ n) :
    hyperLeonardo r (n - 1) * hyperLeonardo r (n + 1) ≤ hyperLeonardo r n ^ 2

/-- **Convexity of the hyper-Leonardo numbers.** For all natural numbers $r$ and $n \ge 1$, the
hyper-Leonardo numbers $\mathrm{Le}^{(r)}_n$ satisfy
$2 \mathrm{Le}^{(r)}_n \le \mathrm{Le}^{(r)}_{n-1} + \mathrm{Le}^{(r)}_{n+1}$.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Theorem 3, with the definition
of convexity displayed before it (`integers-2026-A48-thm-3`). -/
public theorem_wanted hyperLeonardo_convex (r n : ℕ) (hn : 1 ≤ n) :
    2 * hyperLeonardo r n ≤ hyperLeonardo r (n - 1) + hyperLeonardo r (n + 1)

end

end MetaMathlibExt
