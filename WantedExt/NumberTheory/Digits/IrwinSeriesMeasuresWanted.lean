/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Analysis.Series.RiemannRearrangement
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
public import MathlibExt.NumberTheory.Digits.IrwinSeriesLeadingIntegral
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresLocalMass
public import MathlibExt.NumberTheory.Digits.OrdinaryMomentRecurrence
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresIrwinSumZeroLowerBounds
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasuresComplementaryMomentRecurrenceProperties

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators ENNReal
open Filter MeasureTheory Set
open MathlibExt.Analysis.Series.RiemannRearrangementWanted (OrderedHasSum)

/-- **Alternating series for the Irwin sum.** Let $b > 1$ and $d < b$ be natural numbers, let
$(u_{j;m})_{j, m \in \mathbb{N}}$ be a family of real numbers satisfying the ordinary moment
recurrence for $b$ and $d$, and let $k$ and $l \ge 1$ be natural numbers. For a natural number
$n$ write $c(n)$ for the number of occurrences of the digit $d$ in the base-$b$ expansion of $n$,
and let $H^{(k)}_{b,d}$ be the Irwin sum, the sum of $1/n$ over the positive integers $n$ with
$c(n) = k$. For $m \ge 1$ put
$$
a_m = (-1)^m \sum_{\substack{b^{l-1} \le n < b^l \\ c(n) \le k}} \frac{u_{k - c(n);m}}{n^{m+1}}.
$$
Then the partial sums $a_1 + \dots + a_M$ converge, as $M \to \infty$, to
$$
H^{(k)}_{b,d} - \sum_{\substack{1 \le n < b^{l-1} \\ c(n) = k}} \frac{1}{n} -
b \sum_{\substack{b^{l-1} \le n < b^l \\ c(n) \le k}} \frac{1}{n}.
$$
Only the convergence of these ordered partial sums is asserted, not unconditional (absolute)
summability: for $l = 1$ the series can converge only conditionally, for example for $b = 10$,
$d = 0$ and $k = 0$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Theorem 1. -/
public theorem_wanted irwinSum_orderedHasSum_alternating
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (u : ℕ → ℕ → ℝ)
    (hu : OrdinaryMomentRecurrence b d u) (k l : ℕ) (hl : 1 ≤ l) :
    OrderedHasSum
      (fun m : ℕ =>
        if 1 ≤ m then
          (-1 : ℝ) ^ m *
            ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
              if digitCount b d n ≤ k then
                u (k - digitCount b d n) m / (n : ℝ) ^ (m + 1)
              else 0
        else 0)
      (irwinSum b d k -
        (∑ n ∈ Finset.Ico 1 (b ^ (l - 1)),
          if digitCount b d n = k then (1 : ℝ) / n else 0) -
        (b : ℝ) *
          ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
            if digitCount b d n ≤ k then (1 : ℝ) / n else 0)

/-- **Complementary-moment series for the Irwin sums.** Let $b > 1$ and $d < b$ be natural
numbers, let $k$ and $l \ge 1$ be natural numbers, and let $(v_{j,m})_{j, m \ge 0}$ be a family
of real numbers satisfying the complementary moment recurrence for $b$ and $d$. For a natural
number $n$ let $k(n)$ be the number of occurrences of $d$ in the base-$b$ representation of $n$,
and let $H^{(k)}$ be the Irwin sum, the sum of $1/n$ over the positive integers $n$ with
$k(n) = k$. Then the family indexed by $m \ge 1$ of
$$\sum_{b^{l-1} \le n < b^l,\ k(n) \le k} \frac{v_{k - k(n), m}}{(n + 1)^{m + 1}}$$
is summable, with sum
$$H^{(k)} - \sum_{1 \le n < b^{l-1},\ k(n) = k} \frac{1}{n} -
b \sum_{b^{l-1} \le n < b^l,\ k(n) \le k} \frac{1}{n + 1}.$$

The hypothesis $b > 1$ is the paper's standing assumption, in place of an isolated $b > 0$ in the
statement of Theorem 2.

Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Theorem 2. -/
public theorem_wanted irwinSum_hasSum_positive
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (v : ℕ → ℕ → ℝ)
    (hv : ComplementaryMomentRecurrence b d v) (k l : ℕ) (hl : 1 ≤ l) :
    HasSum
      (fun m : ℕ =>
        if 1 ≤ m then
          ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
            if digitCount b d n ≤ k then
              v (k - digitCount b d n) m / ((n : ℝ) + 1) ^ (m + 1)
            else 0
        else 0)
      (irwinSum b d k -
        (∑ n ∈ Finset.Ico 1 (b ^ (l - 1)),
          if digitCount b d n = k then (1 : ℝ) / n else 0) -
        (b : ℝ) *
          ∑ n ∈ Finset.Ico (b ^ (l - 1)) (b ^ l),
            if digitCount b d n ≤ k then (1 : ℝ) / ((n : ℝ) + 1) else 0)

/-- **Monotonicity and limit of the Irwin sums.** Let $b > 1$ be a base and $d < b$ a digit, and
for $k \ge 0$ let $H^{(k)}$ be the Irwin sum, the sum of $1/n$ over the positive integers $n$ whose
base-$b$ expansion contains exactly $k$ occurrences of $d$. If $d \ne 0$, then $k \mapsto H^{(k)}$
is strictly decreasing on $k \ge 1$; if $d = 0$, it is strictly decreasing on all $k \ge 0$. In
both cases $H^{(k)} \to b \log b$ as $k \to \infty$.

Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Proposition 1. -/
public theorem_wanted irwinSum_strictAnti_and_tendsto
    (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    (d ≠ 0 → StrictAntiOn (irwinSum b d) (Set.Ici 1)) ∧
    (d = 0 → StrictAnti (irwinSum b d)) ∧
    Tendsto (irwinSum b d) atTop (nhds ((b : ℝ) * Real.log b))

/-- **Prefix sums as alternating ordinary-moment series.** Let $b > 1$, let $d < b$ be a digit, let
$n$ be a positive integer, let $k(n)$ be the number of occurrences of $d$ in the base-$b$
expansion of $n$, and let $k \ge k(n)$. Write $u_{j;m} = \int_{[0,1)} x^m \, d\mu_j(x)$ for the
ordinary moments of the Irwin measure $\mu_j$. Then there is a real number $S$ such that the
reciprocals $1/N$ of the positive integers $N$ whose base-$b$ expansion begins with that of $n$
and contains exactly $k$ occurrences of $d$ have sum $S$, and the partial sums
$\sum_{m=0}^{M} (-1)^m u_{k - k(n);m} / n^{m+1}$ converge to $S$ as $M \to \infty$. The first
sum is unconditional; for the alternating series only the convergence of the ordered partial
sums is asserted, since for $n = 1$ it can converge only conditionally (for example for
$b = 10$, $d = 0$ and $k = 0$).

Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Corollary 1. -/
public theorem_wanted leadingReciprocal_hasSum_ordinaryMoments
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (k n : ℕ)
    (hn : 0 < n) (hnk : digitCount b d n ≤ k) :
    ∃ S : ℝ,
      HasSum (leadingReciprocalTerm b d k n) S ∧
      OrderedHasSum
        (fun m : ℕ =>
          (-1 : ℝ) ^ m * ordinaryMoment b d (k - digitCount b d n) m hd /
            (n : ℝ) ^ (m + 1)) S

/-- **Prefix sums as complementary-moment series.** Let $b > 1$, let $d < b$ be a digit, let $n$
be a positive integer, let $k(n)$ be the number of occurrences of $d$ in the base-$b$ expansion
of $n$, and let $k \ge k(n)$. Write $v_{j;m} = \int_{[0,1)} (1 - x)^m \, d\mu_j(x)$ for the
complementary moments of the Irwin measure $\mu_j$. Then there is a real number $S$ such that
the reciprocals $1/N$ of the positive integers $N$ whose base-$b$ expansion begins with that of
$n$ and contains exactly $k$ occurrences of $d$ have sum $S$, and the series
$\sum_{m \ge 0} v_{k - k(n);m} / (n+1)^{m+1}$ also has sum $S$. Moreover every term
$v_{k - k(n);m} / (n+1)^{m+1}$ of this series is positive, and the series is summable.

Positivity plus summability renders the paper's phrase "positive series with geometric
convergence"; no explicit ratio is asserted.

Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, Corollary 2. -/
public theorem_wanted leadingReciprocal_hasSum_complementaryMoments
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (k n : ℕ)
    (hn : 0 < n) (hnk : digitCount b d n ≤ k) :
    ∃ S : ℝ,
      HasSum (leadingReciprocalTerm b d k n) S ∧
      HasSum
        (fun m : ℕ =>
          complementaryMoment b d (k - digitCount b d n) m hd /
            ((n : ℝ) + 1) ^ (m + 1)) S ∧
      (∀ m : ℕ, 0 <
        complementaryMoment b d (k - digitCount b d n) m hd /
          ((n : ℝ) + 1) ^ (m + 1)) ∧
      Summable (fun m : ℕ =>
        complementaryMoment b d (k - digitCount b d n) m hd /
          ((n : ℝ) + 1) ^ (m + 1))

/-- **Digit decomposition of the Irwin measures, positive index.** Let $b > 1$ and $d < b$ be
natural numbers, and for each natural number $j$ let $\mu_j$ be the Irwin measure of base $b$ and
digit $d$ with index $j$. Let $f : \mathbb{R} \to \mathbb{R}$ be measurable and bounded on
$[0, b)$, and let $k \ge 1$. Then
$$\int_{[0,1)} f(bx)\, d\mu_k(x) =
\frac{1}{b} \sum_{a \ne d} \int_{[0,1)} f(a + x)\, d\mu_k(x) +
\frac{1}{b} \int_{[0,1)} f(d + x)\, d\mu_{k-1}(x),$$
where $a$ ranges over the digits $0, 1, \dots, b - 1$ other than $d$.

Measurability of $f$ is a hypothesis added to the paper's boundedness assumption.

Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Lemma 1. -/
public theorem_wanted integral_irwinMeasure_succ
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (f : ℝ → ℝ)
    (hf_measurable : Measurable f)
    (hf_bounded : Bornology.IsBounded (f '' Set.Ico (0 : ℝ) b))
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ x in Set.Ico (0 : ℝ) 1, f (b * x) ∂irwinMeasure b d k hd) =
      (1 / (b : ℝ)) *
        (∑ a ∈ Finset.range b,
          if a = d then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, f (a + x) ∂irwinMeasure b d k hd) +
      (1 / (b : ℝ)) *
        ∫ x in Set.Ico (0 : ℝ) 1, f (d + x) ∂irwinMeasure b d (k - 1) hd

/-- **Digit decomposition of the Irwin measure, zero index.** Let $b > 1$ and $d < b$ be natural
numbers, and let $\mu_0$ be the Irwin measure of base $b$ and digit $d$ with index $0$. For every
measurable function $f : \mathbb{R} \to \mathbb{R}$ that is bounded on $[0, b)$,
$$\int_{[0,1)} f(bx)\, d\mu_0(x) = f(0) +
\frac{1}{b} \sum_{a \ne d} \int_{[0,1)} f(a + x)\, d\mu_0(x),$$
where $a$ ranges over the digits $0, 1, \dots, b - 1$ other than $d$.

Measurability of $f$ is a hypothesis added to the paper's boundedness assumption.

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Lemma 1. -/
public theorem_wanted integral_irwinMeasure_zero
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (f : ℝ → ℝ)
    (hf_measurable : Measurable f)
    (hf_bounded : Bornology.IsBounded (f '' Set.Ico (0 : ℝ) b)) :
    (∫ x in Set.Ico (0 : ℝ) 1, f (b * x) ∂irwinMeasure b d 0 hd) =
      f 0 + (1 / (b : ℝ)) *
        ∑ a ∈ Finset.range b,
          if a = d then 0 else
            ∫ x in Set.Ico (0 : ℝ) 1, f (a + x) ∂irwinMeasure b d 0 hd

/-- **Local structure of the Irwin measures on half-open intervals.** Let $b > 1$ and $d < b$ be
natural numbers, and for each natural number $k$ let $\mu_k$ be the Irwin measure of base $b$ and
digit $d$ with index $k$. Let $x \in [0, 1)$ have base-$b$ depth $l$, that is, $l$ is the least
natural number such that $b^l x$ is an integer; let $X$ be a string of $l$ base-$b$ digits, read
most significant digit first, whose value $n(X)$ satisfies $n(X)/b^l = x$; and let $j$ be the
number of occurrences of $d$ in $X$. Let $l' \ge l$ be a natural number, put $j' = j$ if $d > 0$
and $j' = j + l' - l$ if $d = 0$, and let $k \ge j'$ be a natural number such that, if $d > 0$,
then $l' = l$ or $j < k$. Then for every set $U \subseteq [x, x + b^{-l'})$, as real numbers,
$\mu_k(U) = b^{-l'} \mu_{k-j'}(b^{l'} U - b^{l'} x)$, where $b^{l'} U - b^{l'} x$ is the image
of $U$ under $y \mapsto b^{l'} y - b^{l'} x$.

The paper's Lemma 3 omits the condition that $l' = l$ or $j < k$ when $d > 0$. Without it the
identity fails at the atom at $x$: for $b = 2$, $d = 1$, $x = 0$, $l = 0$, $l' = 1$, $j = k = 0$
and $U = \{0\}$ the left side is $2$ and the right side is $1$.

Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Lemma 3. -/
public theorem_wanted irwinMeasure_halfOpen_deeper_local_mass
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (x : ℝ) (l : ℕ)
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hdepth : HasBaseDepth b x l)
    (X : List (Fin b)) (hXlen : X.length = l)
    (hXval : normalizedStringValue b X = x) (j : ℕ)
    (hj : j = X.count ⟨d, hd⟩) (l' : ℕ) (hll' : l ≤ l')
    (k : ℕ) (hk : (if 0 < d then j else j + l' - l) ≤ k)
    (hatom : 0 < d → l' = l ∨ j < k)
    (U : Set ℝ)
    (hU : U ⊆ Set.Ico x (x + (b : ℝ) ^ (-(l' : ℤ)))) :
    (irwinMeasure b d k hd U).toReal =
      (b : ℝ) ^ (-(l' : ℤ)) *
        (irwinMeasure b d (k - (if 0 < d then j else j + l' - l)) hd
          (affineScaleSet b l' x U)).toReal

/-- **Masses of intervals under the Irwin measures.** Let $b > 1$ and $d < b$ be natural numbers,
and for each natural number $k$ let $\mu_k$ be the Irwin measure of base $b$ and digit $d$ with
index $k$; masses below are taken as real numbers. First, for all reals $0 \le t < u \le 1$ and
every natural number $l'$ such that $b^{l'} t$ and $b^{l'} u$ are integers,
$\mu_k([t, u)) = bu - bt$ for every $k \ge l'$. Second, for every nonempty interval
$I \subseteq [0, 1)$, $\mu_k(I)$ tends to $b(\sup I - \inf I)$ as $k \to \infty$.

Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, Proposition 9. -/
public theorem_wanted irwinMeasure_interval_convergence
    (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    (∀ t u : ℝ, t < u → t ∈ Set.Icc (0 : ℝ) 1 → u ∈ Set.Icc (0 : ℝ) 1 →
      ∀ l' : ℕ,
        (∃ z : ℤ, (b : ℝ) ^ l' * t = z) →
        (∃ z : ℤ, (b : ℝ) ^ l' * u = z) →
        ∀ k : ℕ, l' ≤ k →
          (irwinMeasure b d k hd (Set.Ico t u)).toReal = b * u - b * t) ∧
    (∀ I : Set ℝ, I.Nonempty → Set.OrdConnected I → I ⊆ Set.Ico (0 : ℝ) 1 →
      Tendsto (fun k : ℕ => (irwinMeasure b d k hd I).toReal) atTop
        (nhds ((b : ℝ) * (sSup I - sInf I))))

/-- **Limit of the prefix-restricted Irwin sums.** Let $b > 1$, let $d < b$ be a digit and let $n$
be a positive integer. For every $k \ge 0$, the family of reciprocals $1/m$ of the positive
integers $m$ whose base-$b$ expansion begins with the base-$b$ expansion of $n$ and contains
exactly $k$ occurrences of $d$ is summable, and its sum tends to $b \log(1 + 1/n)$ as
$k \to \infty$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Theorem 3. -/
public theorem_wanted leadingIrwinSum_tendsto
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (n : ℕ) (hn : 0 < n) :
    (∀ k : ℕ, Summable (leadingReciprocalTerm b d k n)) ∧
    Tendsto (fun k : ℕ => leadingIrwinSum b d k n) atTop
      (nhds ((b : ℝ) * Real.log (1 + 1 / (n : ℝ))))

end

end MetaMathlibExt
