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
public import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsDerangementPolynomial
public import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsDistribution
public import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutationsRecurrence
public import MathlibExt.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Sequences.NewtonInequalities

namespace MetaMathlibExt

@[expose] public section

open Filter Polynomial Topology

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
