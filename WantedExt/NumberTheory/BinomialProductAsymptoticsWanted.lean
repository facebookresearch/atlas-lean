/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Glaisher–Kinkelin constant.** The Glaisher–Kinkelin constant is the real number
$$A = \exp\left(\frac{1}{12} - \operatorname{Re} \zeta'(-1)\right),$$
where $\zeta'$ is the complex derivative of the Riemann zeta function $\zeta$. Since $\zeta'(-1)$
is real, $\log A = \frac{1}{12} - \zeta'(-1)$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public noncomputable def glaisherKinkelinConstant : ℝ :=
  Real.exp (1 / 12 - (deriv riemannZeta (-1 : ℂ)).re)

/-- **Logarithm of the Glaisher–Kinkelin constant.** The Glaisher–Kinkelin constant $A$ satisfies
$\log A = \frac{1}{12} - \operatorname{Re} \zeta'(-1)$, where $\zeta'$ is the complex derivative
of the Riemann zeta function.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public theorem log_glaisherKinkelinConstant :
    Real.log glaisherKinkelinConstant = 1 / 12 - (deriv riemannZeta (-1 : ℂ)).re :=
  Real.log_exp _

/-- **Factorial-product constants.** For a natural number $k \ge 1$, the constant $F_k$ is the
positive real number defined by
$$\log F_k = \frac{k}{4} \log(2\pi) - \frac{k^2+1}{k} \log A + \frac{1 - \log k}{12k} -
\sum_{\nu=1}^{k-1} \frac{\nu}{k} \log \Gamma\left(\frac{\nu}{k}\right),$$
where $A$ is the Glaisher–Kinkelin constant and $\Gamma$ is the gamma function. For $k = 0$ the
definition gives $F_0 = 1$.

The constant $F_k$ appears in the asymptotic formula for $\prod_{\nu=1}^{n} (k\nu)!$ as
$n \to \infty$; that formula is a separate statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, equation (3) (Kellner 2009, Theorems 12
and 13). -/
public noncomputable def factorialProductConstant (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) / 4 * Real.log (2 * Real.pi) -
    ((k : ℝ) ^ 2 + 1) / k * Real.log glaisherKinkelinConstant +
    (1 - Real.log k) / (12 * k) -
    ∑ ν ∈ Finset.Ico 1 k, (ν : ℝ) / k * Real.log (Real.Gamma ((ν : ℝ) / k)))

/-- **Logarithm of the first factorial product constant.** The factorial product constant $F_1$
satisfies $\log F_1 = \frac{1}{4} \log(2\pi) + \frac{1}{12} - 2 \log A$, where $A$ is the
Glaisher–Kinkelin constant.

Equivalently, $F_1 = (2\pi)^{1/4} e^{1/12} A^{-2}$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Table 1. -/
public theorem log_factorialProductConstant_one :
    Real.log (factorialProductConstant 1) =
      1 / 4 * Real.log (2 * Real.pi) + 1 / 12 - 2 * Real.log glaisherKinkelinConstant := by
  rw [factorialProductConstant, Real.log_exp]
  norm_num
  ring

/-- **Positivity of the factorial-product constants.** For every natural number $k$, the
factorial-product constant $F_k$ is positive.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Section 2. -/
public theorem factorialProductConstant_pos (k : ℕ) : 0 < factorialProductConstant k :=
  Real.exp_pos _

/-- **Comparison function for products of factorials.** For a natural number $k$, the comparison
function $P_k \colon \mathbb{R} \to \mathbb{R}$ is defined by
$$P_k(x) = (k^k)^{x(x+1)/2} \left(\frac{2\pi k x}{e}\right)^{x/2} x^{(3k+1)/(12k)}.$$

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public noncomputable def factorialProductComparison (k : ℕ) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ k) ^ (x * (x + 1) / 2) * (2 * Real.pi * k / Real.exp 1 * x) ^ (x / 2) *
    x ^ ((3 * (k : ℝ) + 1) / (12 * k))

/-- **Value of the factorial-product comparison function at $1$.** For every natural number
$k$, the factorial-product comparison function $P_k$ satisfies $P_k(1) = k^k (2\pi k/e)^{1/2}$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public theorem factorialProductComparison_one (k : ℕ) :
    factorialProductComparison k 1 =
      (k : ℝ) ^ k * (2 * Real.pi * k / Real.exp 1) ^ ((1 : ℝ) / 2) := by
  simp [factorialProductComparison]

/-- **Comparison function for products of binomial coefficients.** For natural numbers $a$ and
$b$, let $c = a - b$ if $b \le a$ and $c = 0$ otherwise. The comparison function
$P_{a,b} \colon \mathbb{R} \to \mathbb{R}$ is defined by
$$P_{a,b}(x) = \left(\frac{a^a}{b^b c^c}\right)^{x(x+1)/2} x^{(1/a - a/(bc))/12 - 1/4} \Big/
\left(\frac{2\pi}{e} \cdot \frac{bc}{a} \cdot x\right)^{x/2}.$$

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public noncomputable def binomialProductComparison (a b : ℕ) (x : ℝ) : ℝ :=
  ((a : ℝ) ^ a / ((b : ℝ) ^ b * ((a - b : ℕ) : ℝ) ^ (a - b))) ^ (x * (x + 1) / 2) *
    x ^ ((1 / (a : ℝ) - a / (b * ((a - b : ℕ) : ℝ))) / 12 - 1 / 4) /
    (2 * Real.pi / Real.exp 1 * (b * ((a - b : ℕ) : ℝ) / a) * x) ^ (x / 2)

/-- **Value of the binomial-product comparison function at $1$.** For natural numbers $a$ and
$b$, let $c = a - b$ if $b \le a$ and $c = 0$ otherwise. Then the binomial-product comparison
function $P_{a,b}$ satisfies
$$P_{a,b}(1) = \frac{a^a / (b^b c^c)}{\bigl((2\pi/e)(bc/a)\bigr)^{1/2}}.$$

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public theorem binomialProductComparison_one (a b : ℕ) :
    binomialProductComparison a b 1 =
      (a : ℝ) ^ a / ((b : ℝ) ^ b * ((a - b : ℕ) : ℝ) ^ (a - b)) /
        (2 * Real.pi / Real.exp 1 * (b * ((a - b : ℕ) : ℝ) / a)) ^ ((1 : ℝ) / 2) := by
  simp [binomialProductComparison]

/-- **Asymptotics of products of factorials of multiples.** Let $k \ge 1$ be a natural number, let
$F_k$ be the $k$-th factorial product constant and $A$ the Glaisher–Kinkelin constant. As
$n \to \infty$, the ratio of $\prod_{\nu=1}^{n} (k\nu)!$ to
$$A^k (2\pi)^{1/4} \left(k e^{-3/2} n\right)^{k n(n+1)/2}
\left(2\pi k e^{k/2-1} n\right)^{n/2} n^{(k^2+3k+1)/(12k)}$$
tends to $F_k$.

The divergent asymptotic expansion (4) of the source is not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 1 (Kellner 2009, Theorems 12 and
13). -/
public theorem_wanted tendsto_prod_factorial_mul_div (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => (∏ ν ∈ Finset.Icc 1 n, ((k * ν).factorial : ℝ)) /
        (glaisherKinkelinConstant ^ k * (2 * Real.pi) ^ ((1 : ℝ) / 4) *
          ((k : ℝ) * Real.exp (-3 / 2) * n) ^ ((k : ℝ) * (n * (n + 1) / 2)) *
          (2 * Real.pi * k * Real.exp ((k : ℝ) / 2 - 1) * n) ^ ((n : ℝ) / 2) *
          (n : ℝ) ^ (((k : ℝ) ^ 2 + 3 * k + 1) / (12 * k))))
      atTop (𝓝 (factorialProductConstant k))

/-- **The factorial-product constants decrease strictly to $1$.** The sequence
$(F_k)_{k \ge 1}$ of factorial-product constants is strictly decreasing, and $F_k \to 1$ as
$k \to \infty$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Corollary 2. -/
public theorem_wanted factorialProductConstant_strictAnti_tendsto_one :
    StrictAnti (fun k : ℕ => factorialProductConstant (k + 1)) ∧
      Tendsto factorialProductConstant atTop (𝓝 1)

/-- **Bounds for $1/a + 1/b - 1/(a+b)$.** Let $a$ and $b$ be natural numbers with $a, b \ge 1$
and $a + b \ge 3$, and put $g(a,b) = 1/a + 1/b - 1/(a+b)$. Then $0 < g(a,b) \le 7/6$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Lemma 3. -/
public theorem_wanted inv_add_inv_sub_inv_add_bounds (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 3 ≤ a + b) :
    0 < (1 / a + 1 / b - 1 / (a + b) : ℚ) ∧ (1 / a + 1 / b - 1 / (a + b) : ℚ) ≤ 7 / 6

/-- **Bounds for the binomial-product constants.** Let $a$ and $b$ be natural numbers with
$1 \le b < a$, and let $F_k$ denote the factorial-product constants. Then
$c_{a,b} = F_a / (F_b F_{a-b})$ satisfies
$$\frac{F_2}{F_1^2} \le c_{a,b} < 1,$$
that is, $c_{2,1} \le c_{a,b} < 1$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Lemma 4. -/
public theorem_wanted factorialProductConstant_ratio_mem_Ico (a b : ℕ) (hb : 1 ≤ b)
    (hab : b < a) :
    factorialProductConstant a / (factorialProductConstant b * factorialProductConstant (a - b))
      ∈ Set.Ico (factorialProductConstant 2 / factorialProductConstant 1 ^ 2) 1

/-- **Asymptotics of products of multinomial coefficients.** Let $r \ge 2$, let
$b_1, \dots, b_r \ge 1$ be natural numbers with $a = b_1 + \dots + b_r$, let $F_k$ denote the
factorial product constants and $P_k$ the factorial comparison functions, and put
$c_{a,b} = F_a / (F_{b_1} \cdots F_{b_r})$. As $m \to \infty$, the ratio of
$\prod_{n=1}^{m} \binom{an}{b_1 n, \dots, b_r n}$ to $P_a(m) / (P_{b_1}(m) \cdots P_{b_r}(m))$
tends to $c_{a,b} (2\pi)^{(1-r)/4}$; moreover $0 < c_{a,b} < 1$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5. -/
public theorem_wanted tendsto_prod_multinomial_div (r : ℕ) (hr : 2 ≤ r) (b : Fin r → ℕ)
    (hb : ∀ i, 1 ≤ b i) :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m,
        (Nat.multinomial Finset.univ (fun i => b i * n) : ℝ)) /
        (factorialProductComparison (∑ i, b i) m /
          ∏ i, factorialProductComparison (b i) m))
      atTop (𝓝 (factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) *
        (2 * Real.pi) ^ ((1 - (r : ℝ)) / 4))) ∧
      factorialProductConstant (∑ i, b i) / (∏ i, factorialProductConstant (b i)) ∈
        Set.Ioo 0 1

/-- **Asymptotics of products of binomial coefficients $\binom{an}{bn}$.** Let $a > b \ge 1$ be
natural numbers, let $F_k$ denote the factorial product constants and $P_{a,b}$ the binomial
comparison function, and put $c_{a,b} = F_a / (F_b F_{a-b})$ and
$C_{a,b} = c_{a,b} (2\pi)^{-1/4}$. Then $\prod_{n=1}^{m} \binom{an}{bn} / P_{a,b}(m) \to C_{a,b}$
as $m \to \infty$; moreover $C_{2,1} \le C_{a,b} < (2\pi)^{-1/4}$ and $c_{2,1} \le c_{a,b} < 1$,
where $c_{2,1} = F_2 / F_1^2$ and $C_{2,1} = c_{2,1} (2\pi)^{-1/4}$.

The decimal approximations of the constants are not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6. -/
public theorem_wanted tendsto_prod_choose_div (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, ((a * n).choose (b * n) : ℝ)) /
        binomialProductComparison a b m)
      atTop (𝓝 (factorialProductConstant a /
        (factorialProductConstant b * factorialProductConstant (a - b)) *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4))) ∧
      factorialProductConstant a /
          (factorialProductConstant b * factorialProductConstant (a - b)) *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4) ∈
        Set.Ico (factorialProductConstant 2 / factorialProductConstant 1 ^ 2 *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4)) ((2 * Real.pi) ^ (-(1 : ℝ) / 4)) ∧
      factorialProductConstant a /
          (factorialProductConstant b * factorialProductConstant (a - b)) ∈
        Set.Ico (factorialProductConstant 2 / factorialProductConstant 1 ^ 2) 1

/-- **Asymptotics of products of central binomial coefficients and Catalan numbers.** Let $A$ be
the Glaisher–Kinkelin constant, let $\mathrm{Cat}_n$ denote the $n$-th Catalan number, and put
$C_{2,1} = 2^{5/24} A^{3/2} / \left((2\pi)^{1/2} e^{1/8}\right)$. As $m \to \infty$, the ratio of
$\prod_{n=1}^{m} \binom{2n}{n}$ to $2^{m^2} (4e/\pi)^{m/2} / m^{m/2 + 3/8}$ tends to $C_{2,1}$,
and the ratio of $\prod_{n=1}^{m} \mathrm{Cat}_n$ to
$2^{m^2} (4e^3/\pi)^{m/2} / m^{3m/2 + 15/8}$ tends to $C_{2,1} (2\pi)^{-1/2}$.

The decimal approximations of the constants are not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Corollary 7. -/
public theorem_wanted tendsto_prod_centralBinom_catalan_div :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (n.centralBinom : ℝ)) /
        (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 1 / Real.pi) ^ ((m : ℝ) / 2) /
          (m : ℝ) ^ ((m : ℝ) / 2 + 3 / 8)))
      atTop (𝓝 (2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
        ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8)))) ∧
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (catalan n : ℝ)) /
        (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 3 / Real.pi) ^ ((m : ℝ) / 2) /
          (m : ℝ) ^ (3 * (m : ℝ) / 2 + 15 / 8)))
      atTop (𝓝 (2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
        ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8)) * (2 * Real.pi) ^ (-(1 : ℝ) / 2)))

/-- **Asymptotics of the product of a row of Pascal's triangle.** Let $F_1$ be the first factorial
product constant and $A$ the Glaisher–Kinkelin constant, and put
$C_{\mathrm{row}} = \left(F_1 (2\pi)^{1/4}\right)^{-1}$. As $n \to \infty$, the ratio of
$\prod_{\nu=0}^{n} \binom{n}{\nu}$ to $e^{n^2/2 + n} / \left((2\pi)^{n/2} n^{n/2 + 1/3}\right)$
tends to $C_{\mathrm{row}}$, and $C_{\mathrm{row}} = A^2 / \left((2\pi)^{1/2} e^{1/12}\right)$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 10. -/
public theorem_wanted tendsto_prod_choose_row_div :
    Tendsto (fun n : ℕ => (∏ ν ∈ Finset.range (n + 1), (n.choose ν : ℝ)) /
        (Real.exp ((n : ℝ) ^ 2 / 2 + n) /
          ((2 * Real.pi) ^ ((n : ℝ) / 2) * (n : ℝ) ^ ((n : ℝ) / 2 + 1 / 3))))
      atTop (𝓝 ((factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹)) ∧
    (factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹ =
      glaisherKinkelinConstant ^ 2 / ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 12))

/-- **Pascal-row asymptotics as a limit of binomial-product asymptotics.** Let $F_k$ denote the
factorial product constants and $P_{a,b}$ the binomial comparison functions, and let $n \ge 1$
be a natural number and $x > 0$ a real number. Then, as $a \to \infty$ through the natural
numbers, $\frac{F_a}{F_1 F_{a-1}} (2\pi)^{-1/4} \to \left(F_1 (2\pi)^{1/4}\right)^{-1}$,
$a^{-n(n+1)/2} \prod_{\nu=1}^{n} \binom{a\nu}{\nu} \to \prod_{\nu=1}^{n} \binom{n}{\nu}$, and
$a^{-x(x+1)/2} P_{a,1}(x) \to e^{x^2/2 + x} / \left((2\pi)^{x/2} x^{x/2 + 1/3}\right)$.

The source does not state the range of $x$; the hypothesis $x > 0$ is added here.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 11. -/
public theorem_wanted tendsto_binomialProduct_limit_row (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : 0 < x) :
    Tendsto (fun a : ℕ => factorialProductConstant a /
        (factorialProductConstant 1 * factorialProductConstant (a - 1)) *
          (2 * Real.pi) ^ (-(1 : ℝ) / 4))
      atTop (𝓝 ((factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹)) ∧
    Tendsto (fun a : ℕ => (a : ℝ) ^ (-((n : ℝ) * (n + 1) / 2)) *
        ∏ ν ∈ Finset.Icc 1 n, ((a * ν).choose ν : ℝ))
      atTop (𝓝 (∏ ν ∈ Finset.Icc 1 n, (n.choose ν : ℝ))) ∧
    Tendsto (fun a : ℕ => (a : ℝ) ^ (-(x * (x + 1) / 2)) * binomialProductComparison a 1 x)
      atTop (𝓝 (Real.exp (x ^ 2 / 2 + x) / ((2 * Real.pi) ^ (x / 2) * x ^ (x / 2 + 1 / 3))))

/-- **Hirschhorn's constant.** Let $A$ be the Glaisher–Kinkelin constant and $F_1$ the first
factorial product constant. As $n \to \infty$,
$$n^{-1/12} \prod_{k=1}^{n} \frac{k!}{\sqrt{2\pi k}\,(k/e)^k}
\to \frac{(2\pi)^{1/4} e^{1/12}}{A^2},$$
and this limit equals $F_1$.

Hirschhorn's asymptotic expansion with divergent Bernoulli sums is not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 12 (Hirschhorn) and the discussion
after it. -/
public theorem_wanted tendsto_hirschhorn_constant :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 12) *
        ∏ k ∈ Finset.Icc 1 n, ((k.factorial : ℝ) /
          (Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k)))
      atTop (𝓝 ((2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) /
        glaisherKinkelinConstant ^ 2)) ∧
    (2 * Real.pi) ^ ((1 : ℝ) / 4) * Real.exp (1 / 12) / glaisherKinkelinConstant ^ 2 =
      factorialProductConstant 1

end

end MetaMathlibExt
