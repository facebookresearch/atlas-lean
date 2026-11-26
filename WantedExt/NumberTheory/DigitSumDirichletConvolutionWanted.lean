/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Digits.DigitSumDirichletConvolution
public import MathlibExt.NumberTheory.Digits.TrollopeDelange
public import MathlibExt.NumberTheory.DigitSumDirichletConvolutionDigitSumAuxiliaryIsBigO

namespace MetaMathlibExt

@[expose] public section

open Filter Asymptotics Real

/-- **Trollope–Delange formula for real $x$.** Let $q \ge 2$ be an integer, let $s_q(n)$ denote
the sum of the base-$q$ digits of $n$, and let $F$ be the Trollope–Delange fluctuation and $h$
Delange's series in base $q$. For every real number $x \ge 1$,
$$\sum_{n=1}^{\lfloor x \rfloor} s_q(n) = \frac{q - 1}{2 \log q} \, x \log x +
x F\left(\frac{\log x}{\log q}\right) - h(x) +
(1 + \lfloor x \rfloor - x) \, s_q(\lfloor x \rfloor).$$

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (`integers-2026-A43-thm-1`), equation (1). -/
public theorem_wanted digitSum_partialSum_trollopeDelange (q : ℕ) (hq : 2 ≤ q) (x : ℝ)
    (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) =
      ((q : ℝ) - 1) / (2 * log q) * x * log x +
        x * trollopeDelangeFluctuation q (log x / log q) - trollopeDelangeSeries q x +
          (1 + ⌊x⌋₊ - x) * ((Nat.digits q ⌊x⌋₊).sum : ℝ)

/-- **Exact formulas for the reciprocal digit sums.** Let $q \ge 2$ be an integer and let $s_q(n)$
denote the sum of the base-$q$ digits of $n$. Let $F$ be the Trollope–Delange fluctuation and $J$
the remainder of the Trollope–Delange formula in base $q$, and for real $x$ put
$G(x) = \int_1^x F(\log u / \log q) \, du / u$, $H(x) = \int_1^x G(u) \, du / u$,
$K(x) = \int_1^x J(u) \, du / u^2$ and $L(x) = \int_1^x K(u) \, du / u$. Then for every real
number $x \ge 1$,
$$\sum_{n=1}^{\lfloor x \rfloor} \frac{s_q(n)}{n} = \frac{(q - 1) \log^2 x}{4 \log q} +
\frac{(q - 1) \log x}{2 \log q} + F\left(\frac{\log x}{\log q}\right) + G(x) + \frac{J(x)}{x} +
K(x)$$
and
$$\sum_{n=1}^{\lfloor x \rfloor} \frac{s_q(n) \log n}{n} = \frac{(q - 1) \log^3 x}{6 \log q} +
\frac{(q - 1) \log^2 x}{4 \log q} + \log x \cdot F\left(\frac{\log x}{\log q}\right) +
(\log x - 1) \, G(x) - H(x) + \frac{J(x) \log x}{x} + (\log x - 1) \, K(x) - L(x).$$

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (`integers-2026-A43-lem-1`), equations (4) and (5). -/
public theorem_wanted digitSum_reciprocal_sums_eq (q : ℕ) (hq : 2 ≤ q) (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) / n =
        ((q : ℝ) - 1) * log x ^ 2 / (4 * log q) + ((q : ℝ) - 1) * log x / (2 * log q) +
          trollopeDelangeFluctuation q (log x / log q) + digitSumFluctuationIntegral q x +
          digitSumRemainder q x / x + digitSumRemainderIntegral q x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) * log n / n =
        ((q : ℝ) - 1) * log x ^ 3 / (6 * log q) + ((q : ℝ) - 1) * log x ^ 2 / (4 * log q) +
          log x * trollopeDelangeFluctuation q (log x / log q) +
          (log x - 1) * digitSumFluctuationIntegral q x -
          digitSumFluctuationDoubleIntegral q x + digitSumRemainder q x * log x / x +
          (log x - 1) * digitSumRemainderIntegral q x - digitSumRemainderDoubleIntegral q x

/-- **Reciprocal digit sums weighted by powers of the logarithm.** Let $q \ge 2$ and $j \ge 1$ be
integers, and let $s_q(n)$ denote the sum of the base-$q$ digits of $n$. As the real number $x$
tends to infinity,
$$\sum_{n=1}^{\lfloor x \rfloor} \frac{s_q(n)}{n} \log^j n =
\frac{(q - 1) \log^{j+2} x}{2 (j + 2) \log q} + O\left(\log^{j+1} x\right).$$

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 5 (`integers-2026-A43-lem-5`). -/
public theorem_wanted digitSum_reciprocal_log_pow_sum_isBigO (q : ℕ) (hq : 2 ≤ q) (j : ℕ)
    (hj : 1 ≤ j) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) / n * log n ^ j -
        ((q : ℝ) - 1) * log x ^ (j + 2) / (2 * (j + 2) * log q)) =O[atTop]
      (fun x => log x ^ (j + 1))

/-- **Partial sums of the second digit-sum convolution.** Let $q \ge 2$ be an integer, let
$s_q(n)$ be the sum of the base-$q$ digits of $n$, and let $s_q^{(2)} = s_q * s_q$ be its
Dirichlet square, so $s_q^{(2)}(n) = \sum_{de = n} s_q(d) \, s_q(e)$. Then
$$\sum_{1 \le n \le x} s_q^{(2)}(n) = \frac{(q - 1)^2}{24 \log^2 q} \, x \log^3 x + O(x \log^2 x)$$
as $x \to \infty$ through the reals.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 2 (`integers-2026-A43-thm-2`). -/
public theorem_wanted digitSumArith_sq_partialSum_isBigO (q : ℕ) (hq : 2 ≤ q) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ 2) n : ℝ) -
        ((q : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log q ^ 2)) =O[atTop]
      (fun x => x * log x ^ 2)

/-- **Partial sums of the iterated digit-sum convolutions.** Let $q \ge 2$ be an integer, let
$s_q(n)$ be the sum of the base-$q$ digits of $n$, let $s_q^{(k)}$ be the $k$-fold Dirichlet
convolution $s_q * \cdots * s_q$, and let $a(k)$ be the base-$q$ digit-convolution coefficients.
For every integer $k \ge 2$,
$$\sum_{1 \le n \le x} s_q^{(k)}(n) = a(k) \, x \log^{2k-1} x + O(x \log^{2k-2} x)$$
as $x \to \infty$ through the reals.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3 (`integers-2026-A43-thm-3`), equation (2). -/
public theorem_wanted digitSumArith_pow_partialSum_isBigO (q : ℕ) (hq : 2 ≤ q) (k : ℕ)
    (hk : 2 ≤ k) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ k) n : ℝ) -
        digitConvolutionCoeff q k * x * log x ^ (2 * k - 1)) =O[atTop]
      (fun x => x * log x ^ (2 * k - 2))

end

end MetaMathlibExt
