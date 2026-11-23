/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Algebra.Polynomial.RealRooted
public import MathlibExt.LinearAlgebra.Matrix.NonnegativeMinors

/-!
# Minuscule polynomials of type A

Statements from Ming-Jian Ding and Jiang Zeng, *Some New Results on the Minuscule Polynomials
of Type A*, Journal of Integer Sequences 28 (2025), Article 25.1.2
(arXiv:2308.16782v3, which carries the same definition (1.1) and results).
-/

namespace MetaMathlibExt

open Polynomial Filter Topology

@[expose] public section

/-- **Type-A minuscule polynomial.** For a natural number $n$, the type-A minuscule polynomial
$N_n(x)$ is the polynomial with rational coefficients
$$N_n(x) = \frac{1}{4n + 2} \sum_{k=1}^{n-1} k (n - k) \binom{2n + 2}{2k + 1} x^k.$$
For $n = 0$ the sum is empty, so $N_0 = 0$.

Source: Ming-Jian Ding and Jiang Zeng, *Some New Results on the Minuscule Polynomials of
Type A*, Journal of Integer Sequences 28 (2025), Article 25.1.2, definition (1.1)
(arXiv:2308.16782v3, equation (1.1)). -/
public noncomputable def minusculePolynomialA (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.Icc 1 (n - 1),
    C ((k : ℚ) * ((n : ℚ) - k) * ((2 * n + 2).choose (2 * k + 1) : ℚ) / (4 * n + 2)) * X ^ k

/-- **The minuscule polynomial $N_1$ vanishes.** The type-A minuscule polynomial $N_1(x)$ is the
zero polynomial.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_one : minusculePolynomialA 1 = 0 := by
  simp [minusculePolynomialA]

/-- **The minuscule polynomial $N_2$.** The type-A minuscule polynomial $N_2(x)$ equals $2x$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_two : minusculePolynomialA 2 = C 2 * X := by
  simp [minusculePolynomialA, Nat.choose]
  norm_num

/-- **The minuscule polynomial $N_3$.** The type-A minuscule polynomial $N_3(x)$ equals
$8x + 8x^2$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_three :
    minusculePolynomialA 3 = C 8 * X + C 8 * X ^ 2 := by
  rw [minusculePolynomialA, show Finset.Icc 1 (3 - 1) = {1, 2} by decide]
  simp [Nat.choose]
  norm_num

/-- **Real-rootedness of the minuscule polynomials.** For every natural number $n$, the type-A
minuscule polynomial $N_n$, viewed as a complex polynomial, is real-rooted: every element of its
multiset of roots is real.

The paper states this for positive $n$; for $n \le 1$ the polynomial $N_n$ is $0$, whose multiset
of roots is taken to be empty.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 5 (first part). -/
public theorem_wanted minusculePolynomialA_isRealRooted (n : ℕ) :
    ((minusculePolynomialA n).map (algebraMap ℚ ℂ)).IsRealRooted

/-- **Interlacing of consecutive minuscule polynomials.** Let $n \ge 2$. There are nonzero real
numbers $c, d$ and real numbers $r_0 \le \dots \le r_{n-1}$ and $s_0 \le \dots \le s_{n-2}$ such
that the type-A minuscule polynomials factor over $\mathbb{R}$ as
$N_{n+1}(x) = c \prod_{i=0}^{n-1} (x - r_i)$ and $N_n(x) = d \prod_{j=0}^{n-2} (x - s_j)$, and
$r_j \le s_j \le r_{j+1}$ for every $j$ with $0 \le j \le n - 2$.

This is the interlacing $N_n \preceq N_{n+1}$, relation (1.2) of the paper written in increasing
order.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 5 (second part). -/
public theorem_wanted minusculePolynomialA_interlaces_succ (n : ℕ) (hn : 2 ≤ n) :
    ∃ (c d : ℝ) (r : Fin n → ℝ) (s : Fin (n - 1) → ℝ), c ≠ 0 ∧ d ≠ 0 ∧
      Monotone r ∧ Monotone s ∧
      (minusculePolynomialA (n + 1)).map (algebraMap ℚ ℝ) = C c * ∏ i, (X - C (r i)) ∧
      (minusculePolynomialA n).map (algebraMap ℚ ℝ) = C d * ∏ j, (X - C (s j)) ∧
      ∀ (j : ℕ) (hj : j + 1 < n),
        r ⟨j, by omega⟩ ≤ s ⟨j, by omega⟩ ∧ s ⟨j, by omega⟩ ≤ r ⟨j + 1, hj⟩

/-- **Log-concavity of the coefficients of the minuscule polynomials.** Let $N_{n,k}$ be the
coefficient of $x^k$ in the type-A minuscule polynomial $N_n(x)$. For all natural numbers $n$
and $k$, $N_{n,k-1} N_{n,k+1} \le N_{n,k}^2$, where for $k = 0$ the index $k - 1$ is read as $0$.

The cases outside $n \ge 1$, $1 \le k \le n - 1$ hold because the coefficients involved vanish.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 7. -/
public theorem_wanted minusculePolynomialA_coeff_logConcave (n k : ℕ) :
    (minusculePolynomialA n).coeff (k - 1) * (minusculePolynomialA n).coeff (k + 1) ≤
      (minusculePolynomialA n).coeff k ^ 2

/-- **Gamma-positivity of the minuscule polynomials.** For every natural number $n$ there are
non-negative integers $\gamma_{n,0}, \dots, \gamma_{n,\lfloor n/2 \rfloor}$ such that the type-A
minuscule polynomial $N_n$ satisfies
$N_n(x) = \sum_{k=0}^{\lfloor n/2 \rfloor} \gamma_{n,k}\, x^k (1 + x)^{n-2k}$.

For $n = 0$ this holds with every $\gamma_{0,k} = 0$, since $N_0 = 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 8. -/
public theorem_wanted minusculePolynomialA_gamma_positive (n : ℕ) :
    ∃ γ : ℕ → ℕ, minusculePolynomialA n =
      ∑ k ∈ Finset.range (n / 2 + 1), C (γ k : ℚ) * X ^ k * (1 + X) ^ (n - 2 * k)

/-- **Binomial closed form of the minuscule polynomials.** For every natural number $n$, the
type-A minuscule polynomial $N_n$ satisfies the identity of polynomials with rational
coefficients
$16x\, N_n(x^2) = 2(n+1)x \bigl((1+x)^{2n} + (1-x)^{2n}\bigr) -
\bigl((1+x)^{2n+2} - (1-x)^{2n+2}\bigr)$.

Dividing by $16x$ gives $N_n(x^2) = \frac{n+1}{8} \bigl((1+x)^{2n} + (1-x)^{2n}\bigr) -
\frac{1}{16x} \bigl((1+x)^{2n+2} - (1-x)^{2n+2}\bigr)$; both sides vanish at $n = 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Proposition 9. -/
public theorem_wanted minusculePolynomialA_comp_sq (n : ℕ) :
    C 16 * X * (minusculePolynomialA n).comp (X ^ 2) =
      C (2 * ((n : ℚ) + 1)) * X * ((1 + X) ^ (2 * n) + (1 - X) ^ (2 * n)) -
        ((1 + X) ^ (2 * n + 2) - (1 - X) ^ (2 * n + 2))

/-- **Exponential generating function of the minuscule polynomials.** For all real numbers $x$
and $z$ with $x \ne 0$, the series $\sum_{n \ge 0} N_n(x^2)\, z^n / n!$ built from the type-A
minuscule polynomials $N_n$ has sum
$\frac{2x(1+x)^2 z - 1 - x^2}{16x} e^{(1+x)^2 z} +
\frac{2x(1-x)^2 z + 1 + x^2}{16x} e^{(1-x)^2 z}$.

The sum starts at $n = 0$, where $N_0 = 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Proposition 10. -/
public theorem_wanted minusculePolynomialA_egf (x z : ℝ) (hx : x ≠ 0) :
    HasSum (fun n : ℕ => aeval (x ^ 2) (minusculePolynomialA n) * z ^ n / n.factorial)
      ((2 * x * (1 + x) ^ 2 * z - 1 - x ^ 2) / (16 * x) * Real.exp ((1 + x) ^ 2 * z) +
        (2 * x * (1 - x) ^ 2 * z + 1 + x ^ 2) / (16 * x) * Real.exp ((1 - x) ^ 2 * z))

/-- **Bourn–Erickson formula for the minuscule polynomials at one.** For every integer $n \ge 1$,
the type-A minuscule polynomial $N_n$ satisfies $N_n(1) = (n - 1)\, 2^{2n-3}$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 11. -/
public theorem_wanted minusculePolynomialA_eval_one (n : ℕ) (hn : 1 ≤ n) :
    (minusculePolynomialA n).eval 1 = ((n : ℚ) - 1) * 2 ^ ((2 * n : ℤ) - 3)

/-- **Bender's central limit theorem for polynomials with non-positive real zeros.** For each
natural number $n$ let $r_{n,0}, \dots, r_{n,n-1}$ be non-negative real numbers, and let $a(n,k)$
be the coefficient of $x^k$ in the real polynomial $A_n(x) = \prod_{i<n} (x + r_{n,i})$. Put
$\mu_n = \sum_{i<n} 1/(1 + r_{n,i})$ and $\sigma_n^2 = \sum_{i<n} r_{n,i}/(1 + r_{n,i})^2$, and let
$\sigma_n \ge 0$ be the square root of $\sigma_n^2$. Then for every $n$,
$\sum_{k=0}^{n} k\, a(n,k) / \sum_{k=0}^{n} a(n,k) = \mu_n$ and
$\sum_{k=0}^{n} (k - \mu_n)^2 a(n,k) / \sum_{k=0}^{n} a(n,k) = \sigma_n^2$. Moreover, if
$\sigma_n^2 \to \infty$ as $n \to \infty$, then for every real $x$,
$\sum_{0 \le k \le n,\ k \le \mu_n + x \sigma_n} a(n,k) / \sum_{k=0}^{n} a(n,k)$ tends to $\Phi(x)$
as $n \to \infty$, where $\Phi$ is the distribution function of the standard normal distribution.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 12 (Bender, Theorem 2). -/
public theorem_wanted bender_asymptotic_normality (r : (n : ℕ) → Fin n → ℝ)
    (hr : ∀ n i, 0 ≤ r n i) :
    let a : ℕ → ℕ → ℝ := fun n k => (∏ i, (X + C (r n i))).coeff k
    let μ : ℕ → ℝ := fun n => ∑ i, 1 / (1 + r n i)
    let σ2 : ℕ → ℝ := fun n => ∑ i, r n i / (1 + r n i) ^ 2
    (∀ n, (∑ k ∈ Finset.range (n + 1), (k : ℝ) * a n k) /
          (∑ k ∈ Finset.range (n + 1), a n k) = μ n ∧
        (∑ k ∈ Finset.range (n + 1), ((k : ℝ) - μ n) ^ 2 * a n k) /
          (∑ k ∈ Finset.range (n + 1), a n k) = σ2 n) ∧
    (Tendsto σ2 atTop atTop → ∀ x : ℝ,
      Tendsto (fun n => (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ μ n + x * √(σ2 n)),
            a n k) /
          (∑ k ∈ Finset.range (n + 1), a n k))
        atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x)))

/-- **Asymptotic normality of the coefficients of the minuscule polynomials.** Let $N_{n,k}$ be
the coefficient of $x^k$ in the type-A minuscule polynomial $N_n(x)$, and let
$\sigma_n = \sqrt{(n^2 - n - 2)/(8(n - 1))}$. Then for every real $x$, the sum of the
coefficients $N_{n,k}$ over $0 \le k < n$ with $k \le n/2 + x \sigma_n$, divided by $N_n(1)$,
tends to $\Phi(x)$ as $n \to \infty$, where $\Phi$ is the distribution function of the standard
normal distribution.

The centring $n/2$ and the scale $\sigma_n^2$ are the mean and the variance of the coefficient
distribution $k \mapsto N_{n,k}/N_n(1)$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 13. -/
public theorem_wanted minusculePolynomialA_asymptotically_normal (x : ℝ) :
    Tendsto (fun n : ℕ =>
        (∑ k ∈ (Finset.range n).filter (fun k : ℕ =>
            (k : ℝ) ≤ n / 2 + x * √(((n : ℝ) ^ 2 - n - 2) / (8 * ((n : ℝ) - 1)))),
          ((minusculePolynomialA n).coeff k : ℝ)) / (((minusculePolynomialA n).eval 1 : ℚ) : ℝ))
      atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x))

/-- **$x$-log-concavity of the minuscule polynomials.** Let $N_n$ denote the type-A minuscule
polynomial. For all natural numbers $n$ and $k$, the coefficient of $x^k$ in
$N_n(x)^2 - N_{n+1}(x) N_{n-1}(x)$ is non-negative, where $N_{n-1}$ is read as $N_0$ when $n = 0$.

For $n \le 1$ the polynomial is $0$ since $N_0 = N_1 = 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 14. -/
public theorem_wanted minusculePolynomialA_x_logConcave (n k : ℕ) :
    0 ≤ (minusculePolynomialA n ^ 2 -
      minusculePolynomialA (n + 1) * minusculePolynomialA (n - 1)).coeff k

/-- **Total positivity of the coefficient matrix of the minuscule polynomials.** Let $N_{n,k}$
be the coefficient of $x^k$ in the type-A minuscule polynomial $N_n(x)$. The infinite real matrix
$[N_{n,k}]_{n,k \ge 1}$, whose entry in row $i$ and column $j$ ($i, j \ge 0$) is
$N_{i+1,j+1}$, has nonnegative minors: every square submatrix obtained by choosing finitely many
rows and finitely many columns, each in increasing order, has nonnegative determinant.

The matrix vanishes on and above its diagonal, since $N_n$ has degree at most $n - 1$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 19. -/
public theorem_wanted minusculePolynomialA_coeffMatrix_hasNonnegativeMinors :
    Matrix.HasNonnegativeMinors
      (Matrix.of fun i j : ℕ => ((minusculePolynomialA (i + 1)).coeff (j + 1) : ℝ))

/-- **Craven–Csordas characterization of multiplier $n$-sequences.** Let $n$ be a natural number
and $t_0, t_1, \dots$ real numbers. Say a real polynomial splits over $\mathbb{R}$ if it is a
constant times a product of linear factors $x - r$ with $r$ real (the zero polynomial splits).
Then the following are equivalent: for every real polynomial $\sum_k a_k x^k$ of degree at most
$n$ that splits over $\mathbb{R}$, the polynomial $\sum_{k=0}^n a_k t_k x^k$ splits over
$\mathbb{R}$; and the polynomial $\sum_{k=0}^n \binom{n}{k} t_k x^k$ splits over $\mathbb{R}$ and
its roots are either all $\ge 0$ or all $\le 0$.

Only $t_0, \dots, t_n$ matter.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 3 (Craven and Csordas, Theorem 3.7). -/
public theorem_wanted multiplier_n_sequence_iff (n : ℕ) (t : ℕ → ℝ) :
    (∀ p : ℝ[X], p.natDegree ≤ n → p.Splits →
      (∑ k ∈ Finset.range (n + 1), C (p.coeff k * t k) * X ^ k).Splits) ↔
    ((∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).Splits ∧
      ((∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots, 0 ≤ x) ∨
        ∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots, x ≤ 0))

/-- **Pólya–Schur characterization of multiplier sequences.** Let $t_0, t_1, \dots$ be
non-negative real numbers. Say a real polynomial splits over $\mathbb{R}$ if it is a constant
times a product of linear factors $x - r$ with $r$ real (the zero polynomial splits). Then the
following are equivalent: for every real polynomial $\sum_k a_k x^k$ that splits over
$\mathbb{R}$, the polynomial $\sum_k a_k t_k x^k$ splits over $\mathbb{R}$; and for every
$n \ge 1$, the polynomial $\sum_{k=0}^n \binom{n}{k} t_k x^k$ splits over $\mathbb{R}$ and its
roots are either all $\ge 0$ or all $\le 0$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 18 (Pólya and Schur). -/
public theorem_wanted multiplier_sequence_iff (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k) :
    (∀ p : ℝ[X], p.Splits →
      (∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k * t k) * X ^ k).Splits) ↔
    ∀ n, 1 ≤ n →
      (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).Splits ∧
        ((∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots,
            0 ≤ x) ∨
          ∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots, x ≤ 0)

/-- **Aissen–Schoenberg–Whitney–Edrei theorem.** Let $a_0, a_1, \dots$ be non-negative real
numbers with $a_0 \ne 0$. All minors of the infinite lower-triangular Toeplitz matrix
$(a_{n-k})_{n,k \ge 0}$, with zeros above the diagonal, are non-negative (that is, the sequence is
a Pólya frequency sequence) if and only if there are a real $\gamma \ge 0$, non-negative reals
$\alpha_0, \alpha_1, \dots$ and $\beta_0, \beta_1, \dots$ with
$\sum_i (\alpha_i + \beta_i) < \infty$, and a real $\varepsilon > 0$ such that for every real $x$
with $|x| < \varepsilon$ the series $\sum_{n \ge 0} a_n x^n$ converges to
$a_0 e^{\gamma x} \prod_{i \ge 0} (1 + \alpha_i x) / \prod_{i \ge 0} (1 - \beta_i x)$.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 16 (Schoenberg–Edrei Theorem, Karlin p. 154). -/
public theorem_wanted polyaFrequency_iff_hasSum_edrei_product (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 ≠ 0) :
    Matrix.HasNonnegativeMinors (Matrix.of fun n k : ℕ => if k ≤ n then a (n - k) else 0) ↔
      ∃ (γ : ℝ) (α β : ℕ → ℝ), 0 ≤ γ ∧ (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
        Summable (fun i => α i + β i) ∧ ∃ ε > 0, ∀ x : ℝ, |x| < ε →
          HasSum (fun n => a n * x ^ n)
            (a 0 * Real.exp (γ * x) * (∏' i, (1 + α i * x)) / ∏' i, (1 - β i * x))

/-- **Pólya–Schur transcendental characterization of multiplier sequences.** Let
$t_0, t_1, \dots$ be non-negative real numbers with $t_0 \ne 0$. Say a real polynomial splits
over $\mathbb{R}$ if it is a constant times a product of linear factors $x - r$ with $r$ real
(the zero polynomial splits). Then the following are equivalent: for every real polynomial
$\sum_k a_k x^k$ that splits over $\mathbb{R}$, the polynomial $\sum_k a_k t_k x^k$ splits over
$\mathbb{R}$; and there are a real $\gamma \ge 0$ and non-negative reals
$\alpha_0, \alpha_1, \dots$ with $\sum_i \alpha_i < \infty$ such that for every real $x$ the series
$\sum_{n \ge 0} t_n x^n / n!$ converges to $t_0 e^{\gamma x} \prod_{i \ge 0} (1 + \alpha_i x)$.

Convergence at every real $x$ encodes that the exponential generating function is entire.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 17 (Pólya and Schur, PS14 p. 93). -/
public theorem_wanted multiplier_sequence_iff_hasSum_exp_mul_tprod (t : ℕ → ℝ)
    (ht : ∀ k, 0 ≤ t k) (ht0 : t 0 ≠ 0) :
    (∀ p : ℝ[X], p.Splits →
      (∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k * t k) * X ^ k).Splits) ↔
      ∃ (γ : ℝ) (α : ℕ → ℝ), 0 ≤ γ ∧ (∀ i, 0 ≤ α i) ∧ Summable α ∧ ∀ x : ℝ,
        HasSum (fun n => t n / n.factorial * x ^ n)
          (t 0 * Real.exp (γ * x) * ∏' i, (1 + α i * x))

end

end MetaMathlibExt
