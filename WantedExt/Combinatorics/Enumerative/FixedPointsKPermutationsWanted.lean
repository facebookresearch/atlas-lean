/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fixed points in permutations with a given number of cycles

Statements from Moussa Benoumhani, *The Distribution of the Number of Fixed Points in
k-Permutations*, INTEGERS 24 (2024), Article A54.

A `k`-permutation of `[n]` is a permutation with exactly `k` cycles, fixed points counted as
one-cycles (the convention of `MetaMathlibExt.card_perm_cycleCount_eq_stirlingFirst`).
`kPermFixedPointCount n k j` is the paper's `a(n, k, j)`, the number of `k`-permutations of `[n]`
with exactly `j` fixed points; the paper's `c(n, k)` is `Nat.stirlingFirst n k`, and its
`d(n, k)` (derangements of `[n]` with `k` cycles) is `kPermFixedPointCount n k 0`, as forced by
Proposition 3 (i) at `j = 0`. The number of cycles is `MetaMathlibExt.cycleQuotientCount`.
"Has only real zeros" for `p : ℝ[X]` is `p.Splits` (equivalently
`Multiset.card p.roots = p.natDegree`, `Polynomial.splits_iff_card_roots`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Combinatorics.Enumerative.Stirling

namespace MetaMathlibExt

@[expose] public section

open Filter Polynomial Topology

/-- **Permutations counted by cycles and fixed points.** For natural numbers $n$, $k$ and $j$,
$a(n, k, j)$ is the number of permutations of $\{0, 1, \dots, n - 1\}$ with exactly $k$ cycles
(fixed points counted as cycles of length one) and exactly $j$ fixed points.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (definition of `a(n, k, j)`). -/
public noncomputable def kPermFixedPointCount (n k j : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) //
    cycleQuotientCount σ = k ∧ Fintype.card (Function.fixedPoints σ) = j}

/-- **A permutation has at most as many fixed points as cycles.** Write $a(n, k, j)$ for the number
of permutations of an $n$-element set with exactly $k$ cycles (fixed points counted as cycles of
length one) and exactly $j$ fixed points. If $k < j$, then $a(n, k, j) = 0$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (range `0 ≤ j ≤ k` of `a(n, k, j)`). -/
public theorem kPermFixedPointCount_eq_zero_of_lt {n k j : ℕ} (h : k < j) :
    kPermFixedPointCount n k j = 0 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨σ, h1, h2⟩ => by rw [cycleQuotientCount_eq] at h1; omega⟩

/-- **Counting the empty permutation.** Write $a(n, k, j)$ for the number of permutations of an
$n$-element set with exactly $k$ cycles (fixed points counted as cycles of length one) and exactly
$j$ fixed points. Then $a(0, 0, 0) = 1$: the empty permutation is the only permutation of the
empty set, and it has no cycles and no fixed points.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (definition of `a(n, k, j)`, value at
`n = k = j = 0`). -/
public theorem kPermFixedPointCount_zero_zero_zero : kPermFixedPointCount 0 0 0 = 1 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, by rw [cycleQuotientCount_eq]; simp, by simp⟩,
    fun x => Subtype.ext (Subsingleton.elim _ _)⟩

/-- **Fixed points split off a derangement.** Write $a(n, k, j)$ for the number of permutations of
an $n$-element set with exactly $k$ cycles (fixed points counted as cycles of length one) and
exactly $j$ fixed points, and $d(m, i) = a(m, i, 0)$ for the number of derangements of an
$m$-element set with $i$ cycles. For all natural numbers $n$, $k$ and $j$ with $j \le k$,
$a(n, k, j) = \binom{n}{j} \, d(n - j, k - j)$, where $n - j$ is read as $0$ when $j > n$.

The paper assumes $n \ge k \ge 1$; the identity holds for all $n$ and all $k \ge j$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (i) (`integers-2024-A54-prop-3`). -/
public theorem_wanted kPermFixedPointCount_eq_choose_mul_derangement {n k j : ℕ} (hjk : j ≤ k) :
    kPermFixedPointCount n k j = n.choose j * kPermFixedPointCount (n - j) (k - j) 0

/-- **Recurrence for permutations counted by cycles and fixed points.** Write $a(n, k, j)$ for the
number of permutations of an $n$-element set with exactly $k$ cycles (fixed points counted as
cycles of length one) and exactly $j$ fixed points. For all natural numbers $n$, $k$ and $j$
with $1 \le j \le k$, $j \, a(n, k, j) = n \, a(n - 1, k - 1, j - 1)$, where $n - 1$ is read as
$0$ when $n = 0$.

The paper assumes $n \ge k \ge 1$; the identity holds for all $n$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (iii) (`integers-2024-A54-prop-3`). -/
public theorem_wanted mul_kPermFixedPointCount {n k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    j * kPermFixedPointCount n k j = n * kPermFixedPointCount (n - 1) (k - 1) (j - 1)

/-- **Stirling numbers from fixed-point counts.** For natural numbers $n$, $k$ and $j$, let
$a(n, k, j)$ be the number of permutations of an $n$-element set with exactly $k$ cycles (fixed
points counted as cycles of length one) and exactly $j$ fixed points. Then for all natural
numbers $n$ and $k$,
$$\sum_{j=0}^{k} a(n, k, j) = c(n, k),$$
where $c(n, k)$ is the unsigned Stirling number of the first kind.

The paper assumes $n \ge k \ge 1$; the identity is stated for all $n$ and $k$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (iv) (`integers-2024-A54-prop-3`). -/
public theorem_wanted sum_kPermFixedPointCount (n k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), kPermFixedPointCount n k j = Nat.stirlingFirst n k

/-- **Total number of fixed points of permutations with a given number of cycles.** For natural
numbers $n$, $k$ and $j$, let $a(n, k, j)$ be the number of permutations of an $n$-element set
with exactly $k$ cycles (fixed points counted as cycles of length one) and exactly $j$ fixed
points, and let $c(n, k)$ be the unsigned Stirling number of the first kind. Then for every
natural number $n$ and every $k \ge 1$,
$$\sum_{j=0}^{k} j \, a(n, k, j) = n \, c(n - 1, k - 1),$$
where the right-hand side is read as $0$ when $n = 0$.

Dividing by $c(n, k)$, the number of permutations of an $n$-element set with $k$ cycles, gives the
mean $\mu_{n,k} = n \, c(n - 1, k - 1) / c(n, k)$ of the number of fixed points of a uniformly
random such permutation when $n \ge k$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 4 (`integers-2024-A54-prop-4`). -/
public theorem_wanted sum_mul_kPermFixedPointCount {n k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1), j * kPermFixedPointCount n k j =
      n * Nat.stirlingFirst (n - 1) (k - 1)

/-- **Variance of the number of fixed points of a permutation with a given number of cycles.**
Write $a(n, k, j)$ for the number of permutations of an $n$-element set with exactly $k$ cycles
(fixed points counted as cycles of length one) and exactly $j$ fixed points, $c(n, k)$ for the
unsigned Stirling number of the first kind (the number of permutations of an $n$-element set
with $k$ cycles), and $\mu_{n,k} = n \, c(n - 1, k - 1) / c(n, k)$. If $2 \le k \le n$, then
$\frac{1}{c(n, k)} \sum_{j=0}^{k} j^2 \, a(n, k, j) - \mu_{n,k}^2 =
\mu_{n,k} (1 + \mu_{n-1,k-1} - \mu_{n,k})$.

Here $\mu_{n,k}$ is the mean number of fixed points of a uniformly random permutation of an
$n$-element set with $k$ cycles, so the left side is the variance of that number.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 4 (`integers-2024-A54-prop-4`). -/
public theorem_wanted kPermFixedPoint_variance {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    let μ : ℕ → ℕ → ℚ := fun n k =>
      (n : ℚ) * Nat.stirlingFirst (n - 1) (k - 1) / Nat.stirlingFirst n k
    (∑ j ∈ Finset.range (k + 1), (j : ℚ) ^ 2 * kPermFixedPointCount n k j) /
        Nat.stirlingFirst n k - μ n k ^ 2 =
      μ n k * (1 + μ (n - 1) (k - 1) - μ n k)

/-- **Newton's inequalities.** Let $p(x) = \sum_{j=0}^{n} a_j x^j$ be a real polynomial of degree
$n \ge 2$ that splits over $\mathbb{R}$, that is, all $n$ of its zeros, counted with
multiplicity, are real. Then for every $j$ with $1 \le j \le n - 1$,
$$a_j^2 \ge \frac{j + 1}{j} \cdot \frac{n - j + 1}{n - j} \, a_{j-1} a_{j+1}.$$

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 1 (`integers-2024-A54-thm-1`). -/
public theorem_wanted newton_inequality_of_real_roots {p : ℝ[X]} {n : ℕ} (hn : 2 ≤ n)
    (hdeg : p.natDegree = n) (hsplit : p.Splits) {j : ℕ} (hj : 1 ≤ j)
    (hjn : j ≤ n - 1) :
    ((j + 1 : ℝ) / j) * (((n : ℝ) - j + 1) / ((n : ℝ) - j)) *
        (p.coeff (j - 1) * p.coeff (j + 1)) ≤ p.coeff j ^ 2

/-- **Schur's composition theorem for real-rooted polynomials.** Let $f = \sum_k a_k x^k$ and
$g = \sum_k c_k x^k$ be real polynomials that split over $\mathbb{R}$, and suppose that the zeros
of $g$ are either all $\le 0$ or all $\ge 0$. Let $d = \min(\deg f, \deg g)$, where the zero
polynomial is given degree $0$. Then the polynomial $\sum_{k=0}^{d} k!\, a_k c_k x^k$ also splits
over $\mathbb{R}$.

The paper asks that the zeros of one of the two polynomials lie on the same side of the origin;
by symmetry this is taken to be $g$, and zeros at $0$ are allowed.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 2 (Schur) (`integers-2024-A54-thm-2`). -/
public theorem_wanted schur_factorial_hadamard_real_roots {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits)
    (hsign : (∀ x ∈ g.roots, x ≤ 0) ∨ (∀ x ∈ g.roots, 0 ≤ x)) :
    let h : ℝ[X] := ∑ k ∈ Finset.range (min f.natDegree g.natDegree + 1),
      C ((k.factorial : ℝ) * f.coeff k * g.coeff k) * X ^ k
    h.Splits

/-- **Real-rootedness of the derangement cycle polynomial.** Write $a(m, k, j)$ for the number of
permutations of an $m$-element set with exactly $k$ cycles (fixed points counted as cycles of
length one) and exactly $j$ fixed points, so that $d(m, k) = a(m, k, 0)$ is the number of
derangements of an $m$-element set with $k$ cycles. For every $n \ge 2$, the real polynomial
$D_n(x) = \sum_{k=1}^{n} d(n + k, k) x^{k-1}$ has only real zeros.

The terms with $k > n$ vanish, so the upper summation limit $n$ loses nothing.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 3 (`integers-2024-A54-thm-3`). -/
public theorem_wanted derangementCyclePolynomial_real_roots {n : ℕ} (hn : 2 ≤ n) :
    let D : ℝ[X] := ∑ k ∈ Finset.Icc 1 n,
      C (kPermFixedPointCount (n + k) k 0 : ℝ) * X ^ (k - 1)
    D.Splits

/-- **Positive sequences satisfying Newton's inequalities are unimodal.** Let $n$ be a natural
number and let $(a_j)_{j \ge 0}$ be a sequence of real numbers with $a_j > 0$ for every $j \le n$,
such that
$$a_j^2 \ge \frac{j + 1}{j} \cdot \frac{n - j + 1}{n - j} \, a_{j-1} a_{j+1}$$
for every $j$ with $1 \le j \le n - 1$. Then there is an $m \le n$ such that $(a_j)$ is strictly
increasing on $\{0, \dots, m\}$, and either $(a_j)$ is strictly decreasing on $\{m, \dots, n\}$,
or $m < n$, $a_m = a_{m+1}$ and $(a_j)$ is strictly decreasing on $\{m + 1, \dots, n\}$.

The paper's "SLC" conclusion is not stated (the abbreviation is not defined in the extracted
statement).

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Corollary 1 (`integers-2024-A54-cor-1`). -/
public theorem_wanted unimodal_of_newton_inequalities {a : ℕ → ℝ} {n : ℕ}
    (hpos : ∀ j ≤ n, 0 < a j)
    (hnewton : ∀ j, 1 ≤ j → j ≤ n - 1 →
      ((j + 1 : ℝ) / j) * (((n : ℝ) - j + 1) / ((n : ℝ) - j)) * (a (j - 1) * a (j + 1)) ≤
        a j ^ 2) :
    ∃ m ≤ n, StrictMonoOn a (Set.Icc 0 m) ∧
      (StrictAntiOn a (Set.Icc m n) ∨
        (m < n ∧ a m = a (m + 1) ∧ StrictAntiOn a (Set.Icc (m + 1) n)))

/-- **Unimodality of fixed-point counts for permutations with a given number of cycles.** Write
$a(n, k, j)$ for the number of permutations of an $n$-element set with exactly $k$ cycles (fixed
points counted as cycles of length one) and exactly $j$ fixed points. If $k \le n$, then there is
an $m \le k$ such that $j \mapsto a(n, k, j)$ is weakly increasing on $\{0, \dots, m\}$ and weakly
decreasing on $\{m, \dots, k\}$, and every $i \le k$ with $a(n, k, i) = a(n, k, m)$ is $m$ or
$m + 1$.

The paper's "SLC" conclusion is not stated (the abbreviation is not defined in the extracted
statement).

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Corollary 2 (`integers-2024-A54-cor-2`). -/
public theorem_wanted kPermFixedPointCount_unimodal {n k : ℕ} (hkn : k ≤ n) :
    ∃ m ≤ k, MonotoneOn (kPermFixedPointCount n k ·) (Set.Icc 0 m) ∧
      AntitoneOn (kPermFixedPointCount n k ·) (Set.Icc m k) ∧
      ∀ i ≤ k, kPermFixedPointCount n k i = kPermFixedPointCount n k m → i = m ∨ i = m + 1

/-- **Central limit theorem for polynomials with nonpositive real zeros.** Let $(Q_n)_{n \ge 0}$
be real polynomials such that every $Q_n$ has only real zeros and all of them are $\le 0$. Put
$\mu_n = Q_n'(1) / Q_n(1)$ and $\sigma_n^2 = Q_n'(1) / Q_n(1) + Q_n''(1) / Q_n(1) - \mu_n^2$, and
let $\sigma_n = \sqrt{\sigma_n^2}$. If $\sigma_n^2 \to \infty$ as $n \to \infty$, then for every
real $x$, the sum of the coefficients of $X^j$ in $Q_n$ over the indices $0 \le j \le \deg Q_n$
with $(j - \mu_n) / \sigma_n \le x$, divided by $Q_n(1)$, tends to $\Phi(x)$ as $n \to \infty$,
where $\Phi$ is the distribution function of the standard normal distribution.

The source asks for negative zeros; zeros at $0$ are also allowed here, since $Q_n = X^m R_n$ only
shifts the coefficient distribution by $m$ and leaves $\sigma_n^2$ unchanged. The local limit
theorem that accompanies this result in the source is not stated.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 5 (`integers-2024-A54-thm-5`). -/
public theorem_wanted coeff_tendsto_gaussian_cdf_of_neg_real_roots (Q : ℕ → ℝ[X])
    (hsplit : ∀ n, (Q n).Splits) (hnonpos : ∀ n, ∀ r ∈ (Q n).roots, r ≤ 0) :
    let μ : ℕ → ℝ := fun n => (Q n).derivative.eval 1 / (Q n).eval 1
    let σ2 : ℕ → ℝ := fun n =>
      (Q n).derivative.eval 1 / (Q n).eval 1 +
        (Q n).derivative.derivative.eval 1 / (Q n).eval 1 - μ n ^ 2
    Tendsto σ2 atTop atTop → ∀ x : ℝ,
      Tendsto (fun n => (∑ j ∈ Finset.range ((Q n).natDegree + 1) with
          (((j : ℕ) : ℝ) - μ n) / Real.sqrt (σ2 n) ≤ x, (Q n).coeff j) / (Q n).eval 1)
        atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x))

/-- **Real zeros of the fixed-point polynomial.** Write $a(n, k, j)$ for the number of permutations
of an $n$-element set with exactly $k$ cycles (fixed points counted as cycles of length one) and
exactly $j$ fixed points. If $1 \le k \le n$, then the real polynomial
$P(x) = \sum_{j=0}^{k} a(n, k, j) x^j$ has only real zeros.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 4 (`integers-2024-A54-thm-4`). -/
public theorem_wanted kPermFixedPointPolynomial_real_roots {n k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    let P : ℝ[X] := ∑ j ∈ Finset.range (k + 1), C (kPermFixedPointCount n k j : ℝ) * X ^ j
    P.Splits

end

end MetaMathlibExt
