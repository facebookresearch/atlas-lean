/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Choose.Multinomial
public import MathlibExt.NumberTheory.CentralBinomialProductAsymptotics
public import MathlibExt.NumberTheory.BinomialProductAsymptoticsTendstoProdMultinomialDiv
public import MathlibExt.NumberTheory.HirschhornConstant

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

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

end

end MetaMathlibExt
