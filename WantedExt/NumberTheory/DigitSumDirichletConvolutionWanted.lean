/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

namespace MetaMathlibExt

@[expose] public section

open Filter Asymptotics Real

/-- **Digit-sum arithmetic function.** For a natural number $q$, $s_q$ is the arithmetic function
that sends $n$ to $s_q(n)$, the sum of the digits of $n$ in base $q$. Its $k$-th Dirichlet power
is the $k$-fold Dirichlet convolution $s_q^{(k)}$, so $s_q^{(1)} = s_q$ and
$s_q^{(k)} = s_q * s_q^{(k-1)}$ for $k \ge 2$.

For $q \le 1$ the base-$q$ digit expansion is degenerate and $s_q(n) = n$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Section 1 (definition of `s_q` and of `s_q^{(k)}`). -/
def digitSumArith (q : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => (Nat.digits q n).sum, by simp⟩

/-- **Value of the digit-sum arithmetic function.** For natural numbers $q$ and $n$, the
base-$q$ digit-sum arithmetic function $s_q$ takes at $n$ the value $s_q(n)$, the sum of the
digits of $n$ in base $q$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Section 1. -/
theorem digitSumArith_apply (q n : ℕ) : digitSumArith q n = (Nat.digits q n).sum := rfl

/-- **The second digit-sum convolution.** For natural numbers $q$ and $n$, the Dirichlet square
$s_q^{(2)} = s_q * s_q$ of the base-$q$ digit-sum function $s_q$ satisfies
$s_q^{(2)}(n) = \sum_{de = n} s_q(d) \, s_q(e)$, where the sum runs over the pairs $(d, e)$ of
positive integers with $de = n$ (there are none for $n = 0$, and then both sides are $0$).

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Section 1 (definition of `s_q^{(2)}`). -/
theorem digitSumArith_sq_apply (q n : ℕ) :
    (digitSumArith q ^ 2) n =
      ∑ x ∈ n.divisorsAntidiagonal, (Nat.digits q x.1).sum * (Nat.digits q x.2).sum := by
  rw [sq, ArithmeticFunction.mul_apply]
  rfl

/-- **Delange's function.** For a natural number $q$, Delange's function in base $q$ is the
function of a real number $x$ given by
$g(x) = \int_0^x \left(\lfloor q t \rfloor - q \lfloor t \rfloor - \frac{q - 1}{2}\right) dt$,
where $\lfloor \cdot \rfloor$ is the floor function.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `g`). -/
noncomputable def trollopeDelangeIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, ((⌊(q : ℝ) * t⌋ : ℝ) - q * ⌊t⌋ - ((q : ℝ) - 1) / 2)

/-- **Delange's function vanishes at zero.** For every natural number $q$, Delange's function $g$
in base $q$ satisfies $g(0) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1. -/
theorem trollopeDelangeIntegral_zero (q : ℕ) : trollopeDelangeIntegral q 0 = 0 :=
  intervalIntegral.integral_same

/-- **Delange's series.** For a natural number $q$, let $g$ be Delange's function in base $q$.
Delange's series in base $q$ is the function of a real number $x$ given by
$h(x) = \sum_{r \ge 0} g(q^r x)/q^r$, where the sum is taken to be $0$ when the series is not
summable.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `h`). -/
noncomputable def trollopeDelangeSeries (q : ℕ) (x : ℝ) : ℝ :=
  ∑' r : ℕ, trollopeDelangeIntegral q ((q : ℝ) ^ r * x) / (q : ℝ) ^ r

/-- **Delange's series vanishes at zero.** For every natural number $q$, Delange's series $h$ in
base $q$ satisfies $h(0) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1. -/
theorem trollopeDelangeSeries_zero (q : ℕ) : trollopeDelangeSeries q 0 = 0 := by
  simp [trollopeDelangeSeries, trollopeDelangeIntegral_zero]

/-- **Trollope–Delange fluctuation.** Let $q$ be a natural number and let $h$ be Delange's series
in base $q$. The Trollope–Delange fluctuation in base $q$ is the function of a real number $x$
given by $F(x) = \frac{q - 1}{2}(1 + \lfloor x \rfloor - x) +
q^{1 + \lfloor x \rfloor - x}\, h(q^{x - \lfloor x \rfloor - 1})$, where $\lfloor x \rfloor$ is
the floor of $x$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `F`). -/
noncomputable def trollopeDelangeFluctuation (q : ℕ) (x : ℝ) : ℝ :=
  ((q : ℝ) - 1) / 2 * (1 + ⌊x⌋ - x) +
    (q : ℝ) ^ (1 + ⌊x⌋ - x) * trollopeDelangeSeries q ((q : ℝ) ^ (x - ⌊x⌋ - 1))

/-- **Periodicity of the Trollope–Delange fluctuation.** For every natural number $q$ and every
real number $x$, the Trollope–Delange fluctuation $F$ in base $q$ satisfies $F(x + 1) = F(x)$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (`F` is `1`-periodic). -/
theorem trollopeDelangeFluctuation_add_one (q : ℕ) (x : ℝ) :
    trollopeDelangeFluctuation q (x + 1) = trollopeDelangeFluctuation q x := by
  have h1 : (1 + ((⌊x + 1⌋ : ℤ) : ℝ) - (x + 1)) = 1 + ⌊x⌋ - x := by
    rw [Int.floor_add_one]; push_cast; ring
  have h2 : (x + 1 - ((⌊x + 1⌋ : ℤ) : ℝ) - 1) = x - ⌊x⌋ - 1 := by
    rw [Int.floor_add_one]; push_cast; ring
  simp only [trollopeDelangeFluctuation, h1, h2]

/-- **Trollope–Delange remainder.** Let $q$ be a natural number, write $s_q(n)$ for the sum of the
base-$q$ digits of a natural number $n$ (with $s_q(n) = n$ when $q \le 1$), and let $h$ be
Delange's series in base $q$. For a real number $x$, let $n_x$ be the floor of $x$ when
$x \ge 0$ and $n_x = 0$ when $x < 0$. The remainder of the Trollope–Delange formula is
$J(x) = (1 + n_x - x)\, s_q(n_x) - h(x)$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `J`). -/
noncomputable def digitSumRemainder (q : ℕ) (x : ℝ) : ℝ :=
  (1 + ⌊x⌋₊ - x) * ((Nat.digits q ⌊x⌋₊).sum : ℝ) - trollopeDelangeSeries q x

/-- **The Trollope–Delange remainder vanishes at zero.** For every natural number $q$, the
remainder $J$ of the Trollope–Delange formula in base $q$ satisfies $J(0) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumRemainder_zero (q : ℕ) : digitSumRemainder q 0 = 0 := by
  simp [digitSumRemainder, trollopeDelangeSeries_zero]

/-- **Integral of the Trollope–Delange fluctuation.** For a natural number $q$ and a real number
$x$, let $F$ be the Trollope–Delange fluctuation in base $q$. Then $G(x)$ is the real number
$$G(x) = \int_1^x \frac{F(\log u / \log q)}{u} \, du,$$
where the integral is oriented, so that $\int_1^x = -\int_x^1$ when $x < 1$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `G`). -/
noncomputable def digitSumFluctuationIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, trollopeDelangeFluctuation q (log u / log q) / u

/-- **The fluctuation integral vanishes at $1$.** For every natural number $q$, let $F$ be the
Trollope–Delange fluctuation in base $q$ and $G(x) = \int_1^x F(\log u / \log q) \, du / u$.
Then $G(1) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumFluctuationIntegral_one (q : ℕ) : digitSumFluctuationIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- **Double integral of the Trollope–Delange fluctuation.** For a natural number $q$ and a real
number $x$, let $F$ be the Trollope–Delange fluctuation in base $q$. Then $H(x)$ is the real number
$$H(x) = \int_1^x \frac{1}{u} \left( \int_1^u \frac{F(\log v / \log q)}{v} \, dv \right) du,$$
where the integrals are oriented, so that $\int_a^b = -\int_b^a$ when $b < a$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `H`). -/
noncomputable def digitSumFluctuationDoubleIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, (∫ v in (1 : ℝ)..u, trollopeDelangeFluctuation q (log v / log q) / v) / u

/-- **The double fluctuation integral vanishes at 1.** For every natural number $q$, the double
integral $H(x) = \int_1^x \int_1^u F(\log v / \log q) \, dv/v \, du/u$ of the Trollope–Delange
fluctuation $F$ for base $q$ satisfies $H(1) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumFluctuationDoubleIntegral_one (q : ℕ) :
    digitSumFluctuationDoubleIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- **Weighted integral of the Trollope–Delange remainder.** For a natural number $q$, let $J$
be the remainder of the Trollope–Delange formula in base $q$. For a real number $x$, define
$K(x) = \int_1^x J(u)/u^2 \, du$, an oriented interval integral (so
$K(x) = -\int_x^1 J(u)/u^2 \, du$ when $x < 1$) that is taken to be $0$ when $J(u)/u^2$ is not
integrable on the interval between $1$ and $x$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `K`). -/
noncomputable def digitSumRemainderIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, digitSumRemainder q u / u ^ 2

/-- **The remainder integral vanishes at $1$.** For every natural number $q$, let $J$ be the
remainder of the Trollope–Delange formula in base $q$ and $K(x) = \int_1^x J(u) \, du / u^2$.
Then $K(1) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumRemainderIntegral_one (q : ℕ) : digitSumRemainderIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- **Double integral of the Trollope–Delange remainder.** For a natural number $q$ and a real
number $x$, let $J$ be the remainder of the Trollope–Delange formula in base $q$. Then $L(x)$ is
the real number
$$L(x) = \int_1^x \frac{1}{u} \left( \int_1^u \frac{J(v)}{v^2} \, dv \right) du,$$
where the integrals are oriented, so that $\int_a^b = -\int_b^a$ when $b < a$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `L`). -/
noncomputable def digitSumRemainderDoubleIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, (∫ v in (1 : ℝ)..u, digitSumRemainder q v / v ^ 2) / u

/-- **The double remainder integral vanishes at $1$.** For every natural number $q$, let $J$ be
the remainder of the Trollope–Delange formula in base $q$ and
$L(x) = \int_1^x \frac{1}{u} \int_1^u \frac{J(v)}{v^2} \, dv \, du$. Then $L(1) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumRemainderDoubleIntegral_one (q : ℕ) :
    digitSumRemainderDoubleIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- **Digit-convolution coefficients.** For a natural number $q$, the base-$q$ digit-convolution
coefficients are the real numbers $a(k)$, $k \ge 0$, given by $a(0) = a(1) = 0$,
$a(2) = \frac{(q - 1)^2}{24 \log^2 q}$ and, for every $k \ge 3$,
$$a(k) = a(k - 1) \cdot \frac{q - 1}{2 \log q}
\sum_{j=0}^{2k-3} \binom{2k-3}{j} \frac{(-1)^j}{j + 2},$$
where $\log$ is the natural logarithm and division by $0$ is read as $0$ (this matters only for
$q \le 1$). The values $a(0)$ and $a(1)$ are placeholders; only $a(k)$ with $k \ge 2$ is used.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3 (definition of `a(k)`). -/
noncomputable def digitConvolutionCoeff (q : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => ((q : ℝ) - 1) ^ 2 / (24 * log q ^ 2)
  | k + 3 =>
    digitConvolutionCoeff q (k + 2) * (((q : ℝ) - 1) / (2 * log q)) *
      ∑ j ∈ Finset.range (2 * (k + 3) - 3 + 1),
        ((2 * (k + 3) - 3).choose j : ℝ) * (-1) ^ j / ((j : ℝ) + 2)

/-- **Second digit-convolution coefficient.** For every natural number $q$, the base-$q$
digit-convolution coefficient $a(2)$ equals $\frac{(q - 1)^2}{24 \log^2 q}$, with division by
$0$ read as $0$ (this matters only for $q \le 1$).

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3. -/
theorem digitConvolutionCoeff_two (q : ℕ) :
    digitConvolutionCoeff q 2 = ((q : ℝ) - 1) ^ 2 / (24 * log q ^ 2) := rfl

/-- **Recurrence for the digit-convolution coefficients.** For every natural number $q$ and
every integer $k \ge 2$, the base-$q$ digit-convolution coefficients $a(k)$ satisfy
$$a(k + 1) = a(k) \cdot \frac{q - 1}{2 \log q}
\sum_{j=0}^{2k-1} \binom{2k-1}{j} \frac{(-1)^j}{j + 2},$$
where division by $0$ is read as $0$ (this matters only for $q \le 1$).

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3. -/
theorem digitConvolutionCoeff_succ (q : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    digitConvolutionCoeff q (k + 1) =
      digitConvolutionCoeff q k * (((q : ℝ) - 1) / (2 * log q)) *
        ∑ j ∈ Finset.range (2 * (k + 1) - 3 + 1),
          ((2 * (k + 1) - 3).choose j : ℝ) * (-1) ^ j / ((j : ℝ) + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rfl

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

/-- **Delange's function is eventually bounded.** For every natural number $q \ge 2$, Delange's
function $g$ in base $q$ satisfies $g(x) = O(1)$ as $x \to +\infty$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 2 (`integers-2026-A43-lem-2`). -/
public theorem_wanted trollopeDelangeIntegral_isBigO_one (q : ℕ) (hq : 2 ≤ q) :
    trollopeDelangeIntegral q =O[atTop] (fun _ => (1 : ℝ))

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

/-- **Size bounds for the Trollope–Delange auxiliary functions.** Let $q \ge 2$ be an integer.
For base $q$, let $h$ be Delange's series, $F$ the Trollope–Delange fluctuation, $J$ the
remainder of the Trollope–Delange formula, and
$G(x) = \int_1^x F(\log u / \log q) \, du/u$,
$H(x) = \int_1^x \int_1^u F(\log v / \log q) \, dv/v \, du/u$,
$K(x) = \int_1^x J(u) \, du/u^2$ and $L(x) = \int_1^x \int_1^u J(v) \, dv/v^2 \, du/u$.
Then $F$ is bounded on $\mathbb{R}$, and as $x \to \infty$ through the reals, $h(x) = O(1)$,
$J(x) = O(\log x)$, $G(x) = O(\log x)$, $H(x) = O(\log^2 x)$, $K(x) = O(1)$ and
$L(x) = O(\log x)$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 3 (`integers-2026-A43-lem-3`). -/
public theorem_wanted digitSum_auxiliary_isBigO (q : ℕ) (hq : 2 ≤ q) :
    trollopeDelangeSeries q =O[atTop] (fun _ => (1 : ℝ)) ∧
      (∃ C : ℝ, ∀ x : ℝ, |trollopeDelangeFluctuation q x| ≤ C) ∧
      digitSumRemainder q =O[atTop] log ∧
      digitSumFluctuationIntegral q =O[atTop] log ∧
      digitSumFluctuationDoubleIntegral q =O[atTop] (fun x => log x ^ 2) ∧
      digitSumRemainderIntegral q =O[atTop] (fun _ => (1 : ℝ)) ∧
      digitSumRemainderDoubleIntegral q =O[atTop] log

/-- **Bound for a weighted sum of the fluctuation.** Let $q \ge 2$ be an integer, let $s_q(n)$
denote the sum of the base-$q$ digits of $n$, let $F$ be the Trollope–Delange fluctuation in base
$q$, and let $F_M = \sup_{t \in \mathbb{R}} |F(t)|$ (taken to be $0$ if $|F|$ is unbounded). For
all real numbers $x > 0$ and $y$,
$$\sum_{n=1}^{\lfloor y \rfloor} \frac{s_q(n)}{n} \, F\left(\frac{\log(x/n)}{\log q}\right) \le
F_M \sum_{n=1}^{\lfloor y \rfloor} \frac{s_q(n)}{n}.$$

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 4 (`integers-2026-A43-lem-4`). -/
public theorem_wanted digitSum_reciprocal_fluctuation_sum_le (q : ℕ) (hq : 2 ≤ q) (x y : ℝ)
    (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ((Nat.digits q n).sum : ℝ) / n * trollopeDelangeFluctuation q (log (x / n) / log q) ≤
      (⨆ t : ℝ, |trollopeDelangeFluctuation q t|) *
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((Nat.digits q n).sum : ℝ) / n

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
