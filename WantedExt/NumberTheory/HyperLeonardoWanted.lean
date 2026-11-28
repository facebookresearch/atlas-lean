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
public import MathlibExt.NumberTheory.HyperLeonardo
public import MathlibExt.NumberTheory.HyperLeonardoHyperLeonardoConvex
public import MathlibExt.NumberTheory.HyperLeonardoHyperFibonacci
public import MathlibExt.NumberTheory.LeonardoLogBalanced
public import WantedExt.NumberTheory.GenLeonardoWanted

/-!
# Hyper-Leonardo numbers

Statements from Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
*A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48. The statement
`hyperLeonardo_convex` is proved in `MathlibExt.NumberTheory.HyperLeonardoHyperLeonardoConvex`.

The Leonardo numbers are `genLeonardo 1` (`Le₀ = Le₁ = 1`, `Le_{n+2} = Le_{n+1} + Le_n + 1`).
The hyper-Leonardo numbers are their iterated partial sums,
`Le^{(0)}_n = Le_n` and `Le^{(r)}_n = ∑_{k=0}^{n} Le^{(r-1)}_k`; the hyper-Fibonacci numbers
`F^{(r)}_n` are the iterated partial sums of `Nat.fib`.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
