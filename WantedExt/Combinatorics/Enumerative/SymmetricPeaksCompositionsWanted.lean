/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Heights of symmetric peaks and depths of symmetric valleys over compositions

Statements from Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the
Depths of Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026),
Article A65.

In a word `w₁ w₂ ⋯` of positive integers, a *symmetric peak* is a factor `a b a` with
`b > a`, of height `b - a`, and a *symmetric valley* is a factor `a b a` with `b < a`, of
depth `a - b`. These are the readings fixed by the paper's worked examples (the five
compositions of `5` and the fourteen compositions of `8` listed after Corollaries 1 and 2)
and by its Maple coefficient lists; the extracted text does not display the definitions.
`hsp(n)` (`dsv(n)`) sums the heights (depths) over all compositions of `n`, and
`hsp(n, k)` (`dsv(n, k)`) over those with exactly `k` parts.

The paper's geometric variables take values in `{1, 2, …}`; Mathlib's
`ProbabilityTheory.geometricMeasure` lives on `{0, 1, …}`. The shift does not change any
of the four statistics.

The trivariate generating functions of Theorems 1 and 3 are stated coefficientwise as
multivariate power series; Theorem 3 uses the corrected reading recorded in its docstring
and audit row.

Not stated (see the source audit table): the bivariate part of Lemma 2 (false as
extracted), Theorem 2(b) (false as extracted) and the variances of Theorem 6 (false as printed in the journal).
-/

open MeasureTheory ProbabilityTheory PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Number of symmetric peaks.** For a finite word $w = w_1 w_2 \cdots w_m$ of natural
numbers, a symmetric peak is a factor $w_i w_{i+1} w_{i+2}$ of three consecutive letters with
$w_i = w_{i+2} < w_{i+1}$. The number of symmetric peaks of $w$ is the number of indices $i$
with $1 \le i \le m - 2$ at which $w$ has a symmetric peak (overlapping peaks all count); it
is $0$ when $m < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (symmetric peaks). -/
def symmetricPeakCount : List ℕ → ℕ
  | a :: b :: c :: t => (if a = c ∧ a < b then 1 else 0) + symmetricPeakCount (b :: c :: t)
  | _ => 0

/-- **Sum of the heights of symmetric peaks.** For a finite word $w = w_1 w_2 \cdots w_m$ of
natural numbers, a symmetric peak is a factor $w_i w_{i+1} w_{i+2}$ of three consecutive
letters with $w_i = w_{i+2} < w_{i+1}$, and its height is $w_{i+1} - w_i$. The symmetric peak
height sum of $w$ is the sum of the heights of the symmetric peaks of $w$ over all indices $i$
with $1 \le i \le m - 2$ at which one occurs; it is $0$ when $m < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (heights of symmetric peaks). -/
def symmetricPeakHeightSum : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a = c ∧ a < b then b - a else 0) + symmetricPeakHeightSum (b :: c :: t)
  | _ => 0

/-- **Number of symmetric valleys of a word.** For a word $w = w_1 w_2 \cdots w_\ell$ of natural
numbers, a symmetric valley is a position $i$ with $1 < i < \ell$ such that $w_{i-1} = w_{i+1}$
and $w_i < w_{i-1}$, that is, a factor $a\,b\,a$ with $b < a$. The symmetric valley count of $w$
is the number of such positions; in particular it is $0$ when $\ell < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (symmetric valleys). -/
def symmetricValleyCount : List ℕ → ℕ
  | a :: b :: c :: t => (if a = c ∧ b < a then 1 else 0) + symmetricValleyCount (b :: c :: t)
  | _ => 0

/-- **Total depth of the symmetric valleys of a word.** For a word $w = w_1 w_2 \cdots w_\ell$ of
natural numbers, a symmetric valley is a position $i$ with $1 < i < \ell$ such that
$w_{i-1} = w_{i+1}$ and $w_i < w_{i-1}$; its depth is $w_{i-1} - w_i$. The symmetric valley depth
sum of $w$ is the sum of the depths of all its symmetric valleys; in particular it is $0$ when
$\ell < 3$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (depths of symmetric valleys). -/
def symmetricValleyDepthSum : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a = c ∧ b < a then a - b else 0) + symmetricValleyDepthSum (b :: c :: t)
  | _ => 0

/-- **Symmetric peak examples among the compositions of 5.** The symmetric peak height sums of
the words $1\,3\,1$, $1\,2\,1\,1$, $1\,1\,2\,1$ and $1\,1\,1\,1\,1$ are $2$, $1$, $1$ and $0$
respectively, and the word $1\,3\,1$ has exactly one symmetric peak.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
example after Corollary 1. -/
theorem symmetricPeakHeightSum_examples :
    symmetricPeakHeightSum [1, 3, 1] = 2 ∧ symmetricPeakHeightSum [1, 2, 1, 1] = 1 ∧
      symmetricPeakHeightSum [1, 1, 2, 1] = 1 ∧ symmetricPeakHeightSum [1, 1, 1, 1, 1] = 0 ∧
      symmetricPeakCount [1, 3, 1] = 1 := by
  decide

/-- **Symmetric valleys in three compositions of eight.** The word $2\,1\,2\,1\,2$ has two
symmetric valleys and total symmetric valley depth $2$, the word $3\,1\,3\,1$ has total symmetric
valley depth $2$, and the word $3\,2\,3$ has total symmetric valley depth $1$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
example after Corollary 2. -/
theorem symmetricValleyDepthSum_examples :
    symmetricValleyDepthSum [2, 1, 2, 1, 2] = 2 ∧ symmetricValleyCount [2, 1, 2, 1, 2] = 2 ∧
      symmetricValleyDepthSum [3, 1, 3, 1] = 2 ∧ symmetricValleyDepthSum [3, 2, 3] = 1 := by
  decide

/-- **Generating function of the total symmetric peak height over compositions.** For
$n \ge 0$ let $\mathrm{hsp}(n)$ be the sum, over all compositions $c$ of $n$, of the symmetric
peak height sum of the sequence of parts of $c$. Then in $\mathbb{Z}[[x]]$
$$
\left(\sum_{n \ge 0} \mathrm{hsp}(n)\, x^n\right)(1 - 2x)^2 (1 - x^3) = x^4,
$$
that is, $\sum_{n \ge 0} \mathrm{hsp}(n)\, x^n = x^4 / ((1 - 2x)^2 (1 - x^3))$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 1, (5) (`integers-2026-A65-lem-1`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_genFun :
    PowerSeries.mk (fun n => ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 - X ^ 3)) = X ^ 4

/-- **Bivariate generating function of the total symmetric peak height over compositions.**
For $n, k \ge 0$ let $\mathrm{hsp}(n, k)$ be the sum, over all compositions $c$ of $n$ with
exactly $k$ parts, of the symmetric peak height sum of the sequence of parts of $c$. Then in
the ring $\mathbb{Z}[y][[x]]$ of formal power series in $x$ over $\mathbb{Z}[y]$,
$$
\left(\sum_{n \ge 0} \sum_{k \ge 0} \mathrm{hsp}(n, k)\, y^k x^n\right)
(1 - x^3)(1 - x - yx)^2 = y^3 x^4,
$$
that is, $\sum_{n, k \ge 0} \mathrm{hsp}(n, k)\, x^n y^k = y^3 x^4 / ((1 - x^3)(1 - x - yx)^2)$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 1 (`integers-2026-A65-lem-1`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_bivariate_genFun :
    PowerSeries.mk (fun n => ∑ c : Composition n,
        Polynomial.C ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) * Polynomial.X ^ c.length) *
        ((1 - X ^ 3) * (1 - X - PowerSeries.C (Polynomial.X : Polynomial ℤ) * X) ^ 2) =
      PowerSeries.C (Polynomial.X ^ 3 : Polynomial ℤ) * X ^ 4

/-- **Generating function for the total depth of symmetric valleys over compositions.** For
$n \ge 0$, let $\operatorname{dsv}(n)$ be the sum, over all compositions $c$ of $n$, of the total
depth of the symmetric valleys of the sequence of parts of $c$. Then in the ring $\mathbb{Z}[[x]]$
of formal power series,
$$\Big(\sum_{n \ge 0} \operatorname{dsv}(n)\, x^n\Big)(1-2x)^2(1-x^3)(1-x^2)^2 = x^5 - 2x^6 + x^7,$$
that is, $\sum_{n \ge 0} \operatorname{dsv}(n)\, x^n$ equals
$(x^5 - 2x^6 + x^7)/((1-2x)^2(1-x^3)(1-x^2)^2)$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 2, (11) (`integers-2026-A65-lem-2`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_genFun :
    PowerSeries.mk (fun n => ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 - X ^ 3) * (1 - X ^ 2) ^ 2) = X ^ 5 - 2 * X ^ 6 + X ^ 7

/-- **Closed form for the total symmetric peak height over compositions.** For $n \ge 0$ let
$\mathrm{hsp}(n)$ be the sum, over all compositions $c$ of $n$, of the symmetric peak height
sum of the sequence of parts of $c$, and let $\omega_\pm = 1 \pm i\sqrt{3}$. Then for every
$n \ge 0$, as complex numbers,
$$
\mathrm{hsp}(n) = \frac{2^n}{2} \cdot \frac{7n - 24}{49} +
\frac{(-33 - 15 i \sqrt{3})(-2)^n}{441\, \omega_+^{n+1}} +
\frac{(-33 + 15 i \sqrt{3})(-2)^n}{441\, \omega_-^{n+1}} + \frac{1}{3}.
$$

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Corollary 1, (6) (`integers-2026-A65-cor-1`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_closed_form (n : ℕ) :
    ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℂ) =
      (2 : ℂ) ^ n / 2 * (7 * n - 24) / 49 +
        (-33 - 15 * Complex.I * (Real.sqrt 3 : ℂ)) * (-2) ^ n /
          (441 * (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) +
        (-33 + 15 * Complex.I * (Real.sqrt 3 : ℂ)) * (-2) ^ n /
          (441 * (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) + 1 / 3

/-- **Closed form for the total depth of symmetric valleys over compositions.** For $n \ge 0$,
let $\operatorname{dsv}(n)$ be the sum, over all compositions $c$ of $n$, of the total depth of
the symmetric valleys of the sequence of parts of $c$, and write $\omega_\pm = 1 \pm i\sqrt{3}$.
Then, as complex numbers,
$$\operatorname{dsv}(n) = \frac{(-6n+7)(-1)^n}{108} + \frac{2^n(21n-79)}{1323} +
\frac{(-33-15\sqrt{3}\,i)(-2)^n}{441\,\omega_+^{n+1}} +
\frac{(-33+15\sqrt{3}\,i)(-2)^n}{441\,\omega_-^{n+1}} + \frac{1}{12}.$$

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Corollary 2, (12) (`integers-2026-A65-cor-2`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_closed_form (n : ℕ) :
    ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℂ) =
      (-6 * n + 7) / 108 * (-1) ^ n + (2 : ℂ) ^ n * (21 * n - 79) / 1323 +
        (-33 - 15 * (Real.sqrt 3 : ℂ) * Complex.I) * (-2) ^ n /
          (441 * (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) +
        (-33 + 15 * (Real.sqrt 3 : ℂ) * Complex.I) * (-2) ^ n /
          (441 * (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) + 1 / 12

/-- **Total symmetric peak height over compositions with a fixed number of parts.** For
$n, k \ge 0$ let $\mathrm{hsp}(n, k)$ be the sum, over all compositions $c$ of $n$ with exactly
$k$ parts, of the symmetric peak height sum of the sequence of parts of $c$. If $k > 3$, then
for every $n \ge 0$
$$
\mathrm{hsp}(n, k) = (k - 2) \sum_{m=2}^{n-k+1} \sum_{b=1}^{\min(m-1,\, t_m)}
\binom{n - 2b - m - 1}{k - 4} (m - b),
\qquad t_m = \left\lfloor \frac{n - m - k + 3}{2} \right\rfloor,
$$
where an empty sum is $0$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 2(a) (`integers-2026-A65-thm-2`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_length (n k : ℕ) (hk : 3 < k) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = k),
        symmetricPeakHeightSum c.blocks =
      (k - 2) * ∑ m ∈ Finset.Icc 2 (n - k + 1),
        ∑ b ∈ Finset.Icc 1 (min (m - 1) ((n - m - k + 3) / 2)),
          (n - 2 * b - m - 1).choose (k - 4) * (m - b)

/-- **Total depth of symmetric valleys over compositions with $k > 3$ parts.** For natural
numbers $n$ and $k$ with $k > 3$, the sum, over all compositions $c$ of $n$ with exactly $k$
parts, of the total depth of the symmetric valleys of the sequence of parts of $c$ equals
$$(k-2) \sum_{m=1}^{\lfloor (n-k+1)/3 \rfloor} \sum_{b=m+1}^{\lfloor (n-m-(k-3))/2 \rfloor}
\binom{n-2b-m-1}{k-4}(b-m),$$
where a difference of natural numbers that would be negative is read as $0$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 4(a) (`integers-2026-A65-thm-4`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_length (n k : ℕ) (hk : 3 < k) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = k),
        symmetricValleyDepthSum c.blocks =
      (k - 2) * ∑ m ∈ Finset.Icc 1 ((n - k + 1) / 3),
        ∑ b ∈ Finset.Icc (m + 1) ((n - m - (k - 3)) / 2),
          (n - 2 * b - m - 1).choose (k - 4) * (b - m)

/-- **Total depth of symmetric valleys over compositions with three parts.** For every natural
number $n$, the sum, over all compositions $c$ of $n$ with exactly three parts, of the total
depth of the symmetric valleys of the sequence of parts of $c$ equals
$\sum_{m=1}^{\lfloor (n-2)/3 \rfloor} d_m$, where $d_m = (n-3m)/2$ if $n - m$ is even and
$d_m = 0$ otherwise.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 4(b) (`integers-2026-A65-thm-4`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_length_three (n : ℕ) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = 3),
        symmetricValleyDepthSum c.blocks =
      ∑ m ∈ Finset.Icc 1 ((n - 2) / 3), if Even (n - m) then (n - 3 * m) / 2 else 0

/-- **Expected symmetric peaks and valleys in geometric words.** Let $n \ge 2$, let
$0 < p < 1$ and $q = 1 - p$, and let $X_1, \dots, X_n$ be independent random variables, each
geometric on $\{0, 1, 2, \dots\}$ with $\Pr(X_i = k) = q^k p$, and consider the word
$X_1 X_2 \cdots X_n$. The expected number of its symmetric peaks is
$p^2 q (n - 2)/(1 - q^3)$, the expected number of its symmetric valleys is
$p^2 \left(\frac{1}{1 - q^2} - \frac{1}{1 - q^3}\right)(n - 2)$, the expected sum of the
heights of its symmetric peaks is $p q (n - 2)/(1 - q^3)$, and the expected sum of the depths
of its symmetric valleys is $q \left(\frac{p}{1 - q^3} - \frac{1}{(1 + q)^2}\right)(n - 2)$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 5 (`integers-2026-A65-thm-5`). -/
public theorem_wanted integral_symmetricPeakValley_geometric (n : ℕ) (hn : 2 ≤ n)
    (p : unitInterval) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    let q : ℝ := 1 - p
    let μ := Measure.pi fun _ : Fin n => geometricMeasure p
    ∫ x, (symmetricPeakCount (List.ofFn x) : ℝ) ∂μ = p ^ 2 * q / (1 - q ^ 3) * (n - 2) ∧
      ∫ x, (symmetricValleyCount (List.ofFn x) : ℝ) ∂μ =
        p ^ 2 * (1 / (1 - q ^ 2) - 1 / (1 - q ^ 3)) * (n - 2) ∧
      ∫ x, (symmetricPeakHeightSum (List.ofFn x) : ℝ) ∂μ = p * q / (1 - q ^ 3) * (n - 2) ∧
      ∫ x, (symmetricValleyDepthSum (List.ofFn x) : ℝ) ∂μ =
        q * (p / (1 - q ^ 3) - 1 / (1 + q) ^ 2) * (n - 2)


/-- **Trivariate generating function for symmetric peaks in compositions.** For a composition
$c$ write $\ell(c)$ for its number of parts, $\mathrm{sp}(c)$ for the number of symmetric peaks
and $\mathrm{hsp}(c)$ for the symmetric peak height sum of its sequence of parts. In the ring
$\mathbb{Z}[y, q, h][[x]]$ of formal power series in $x$ whose coefficients are polynomials in
$y, q, h$ with integer coefficients,
$$
\sum_{n \ge 0} \sum_{c \models n} x^n y^{\ell(c)} q^{\mathrm{sp}(c)} h^{\mathrm{hsp}(c)} =
\frac{1}{1 - \sum_{a \ge 1} \frac{x^a y}{1 - y^2 x^{2a+1} \left(\frac{qh}{1 - hx} -
\frac{1}{1 - x}\right)}},
$$
where $c \models n$ ranges over the compositions of $n$ and
$\frac{qh}{1 - hx} - \frac{1}{1 - x}$ stands for the series $\sum_{j \ge 0} (q h^{j+1} - 1) x^j$.
Precisely: for every $n \ge 0$ the coefficients of $x^n$ on the two sides agree when the sum
over $a$ is restricted to $1 \le a \le n$ (the terms with $a > n$ do not contribute to them).

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 1 (`integers-2026-A65-thm-1`). -/
public theorem_wanted symmetricPeak_compositions_trivariate_genFun (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk fun m => ∑ c : Composition m,
        MvPolynomial.X (0 : Fin 3) ^ c.length * MvPolynomial.X 1 ^ symmetricPeakCount c.blocks *
          MvPolynomial.X 2 ^ symmetricPeakHeightSum c.blocks : PowerSeries (MvPolynomial (Fin 3) ℤ)) =
      PowerSeries.coeff n (PowerSeries.invOfUnit (1 - ∑ a ∈ Finset.Icc 1 n,
        X ^ a * PowerSeries.C (MvPolynomial.X 0) *
          PowerSeries.invOfUnit (1 - PowerSeries.C (MvPolynomial.X 0 ^ 2) * X ^ (2 * a + 1) *
            PowerSeries.mk fun j =>
              MvPolynomial.X 1 * MvPolynomial.X 2 ^ (j + 1) - 1) 1) 1)

/-- **Trivariate generating function for symmetric valleys in compositions.** For a composition
$c$ write $\ell(c)$ for its number of parts, $\mathrm{sv}(c)$ for the number of symmetric
valleys and $\mathrm{dsv}(c)$ for the symmetric valley depth sum of its sequence of parts. In
the ring $\mathbb{Z}[y, p, d][[x]]$ of formal power series in $x$ whose coefficients are
polynomials in $y, p, d$ with integer coefficients,
$$
\sum_{n \ge 0} \sum_{c \models n} x^n y^{\ell(c)} p^{\mathrm{sv}(c)} d^{\mathrm{dsv}(c)} =
\frac{1}{1 - \sum_{a \ge 1} \frac{x^a y}{1 - y^2 x^{a+1}
\sum_{b=1}^{a-1} (p d^{a-b} - 1) x^{b-1}}},
$$
where $c \models n$ ranges over the compositions of $n$. Precisely: for every $n \ge 0$ the
coefficients of $x^n$ on the two sides agree when the sum over $a$ is restricted to
$1 \le a \le n$ (the terms with $a > n$ do not contribute to them). The inner sum equals
$p(x^{a-1} - d^{a-1})/(x/d - 1) - (x^{a-1} - 1)/(x - 1)$.

Corrected reading: the paper prints $(p x^{a-1} - d^{a-1})/(x/d - 1)$, with $p$ on the first
term only; that is false (at $n = 3$ it gives the composition $111$ a symmetric valley of depth
$0$). The corrected term $p(x^{a-1} - d^{a-1})/(x/d - 1)$ is the penultimate line of the
paper's proof, $x^a y^2 p d^a ((x/d)^a - x/d)/(x/d - 1)$, and agrees with the paper's
specialization $d = 1$, $(x^{a-1} - 1)(p - 1)/(x - 1)$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 3 (`integers-2026-A65-thm-3`). -/
public theorem_wanted symmetricValley_compositions_trivariate_genFun (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk fun m => ∑ c : Composition m,
        MvPolynomial.X (0 : Fin 3) ^ c.length * MvPolynomial.X 1 ^ symmetricValleyCount c.blocks *
          MvPolynomial.X 2 ^ symmetricValleyDepthSum c.blocks :
        PowerSeries (MvPolynomial (Fin 3) ℤ)) =
      PowerSeries.coeff n (PowerSeries.invOfUnit (1 - ∑ a ∈ Finset.Icc 1 n,
        X ^ a * PowerSeries.C (MvPolynomial.X 0) *
          PowerSeries.invOfUnit (1 - PowerSeries.C (MvPolynomial.X 0 ^ 2) * X ^ (a + 1) *
            ∑ b ∈ Finset.Ico 1 a,
              PowerSeries.C (MvPolynomial.X 1 * MvPolynomial.X 2 ^ (a - b) - 1) * X ^ (b - 1)) 1) 1)

end

end MetaMathlibExt
