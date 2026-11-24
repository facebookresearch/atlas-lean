/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.TrollopeDelange
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Dirichlet convolutions of digit sums

This module defines the digit-sum arithmetic function, the auxiliary integrals for its
partial sums, and the recurrence for the leading coefficients of its Dirichlet powers.
-/

namespace MetaMathlibExt

@[expose] public section

open Real

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

end

end MetaMathlibExt
