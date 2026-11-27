/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeaksCompositions
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightBivariateGeneratingFunction
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightClosedForm
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightGeneratingFunction
public import MathlibExt.Combinatorics.Enumerative.SymmetricValleyDepthClosedForm
public import MathlibExt.Combinatorics.Enumerative.SymmetricValleyDepthGeneratingFunction

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

The univariate generating function of `hsp(n)` in Lemma 1, (5) is proved in
`MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightGeneratingFunction`, and the bivariate
generating function of `hsp(n, k)` in Lemma 1 in
`MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightBivariateGeneratingFunction`.
The closed form of `hsp(n)` in Corollary 1, (6) is proved in
`MathlibExt.Combinatorics.Enumerative.SymmetricPeakHeightClosedForm`.

Not stated (see the source audit table): the bivariate part of Lemma 2 (false as
extracted), Theorem 2(b) (false as extracted) and the variances of Theorem 6 (false as printed in the journal).
-/

open MeasureTheory ProbabilityTheory PowerSeries

namespace MetaMathlibExt

@[expose] public section

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
