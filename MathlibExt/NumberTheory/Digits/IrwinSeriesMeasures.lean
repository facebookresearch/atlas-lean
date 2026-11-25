/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.NumberTheory.Digits.OrdinaryMomentRecurrence

/-!
# Irwin measures and digit strings

This module defines Irwin sums, digit-string measures, and their ordinary and complementary
moments. It gives the digit count of zero and the value and Dirac mass of the empty string.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- **Digit count.** For natural numbers $b$, $d$ and $n$, the digit count of $d$ in $n$ is the
number of occurrences of the digit $d$ in the minimal base-$b$ representation of $n$ (its base-$b$
digits without leading zeros). The representation of $0$ is empty, so $0$ has digit count $0$.

For the degenerate bases, the representation of $n \ne 0$ is the single digit $n$ when $b = 0$
and a string of $n$ ones when $b = 1$.

Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public def digitCount (b d n : ℕ) : ℕ :=
  (Nat.digits b n).count d

/-- **Integer length.** For natural numbers $b$ and $n$, the integer length of $n$ in base $b$ is
the number of digits in the minimal base-$b$ representation of $n$ (its base-$b$ digits without
leading zeros); in particular $0$ has length $0$.

For the degenerate bases, the representation of $n \ne 0$ is the single digit $n$ when $b = 0$
and a string of $n$ ones when $b = 1$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public def integerLength (b n : ℕ) : ℕ :=
  (Nat.digits b n).length

/-- **Irwin sum.** For natural numbers $b$, $d$ and $k$, the Irwin sum $H^{(k)}_{b,d}$ is the sum
of $1/n$ over the positive integers $n$ whose base-$b$ expansion contains exactly $k$ occurrences
of the digit $d$. It is taken as an unconditional sum of real numbers, with the value $0$ if this
family is not summable; positivity and convergence are results, not part of the definition.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public noncomputable def irwinSum (b d k : ℕ) : ℝ :=
  ∑' n : ℕ, if 0 < n ∧ digitCount b d n = k then (1 : ℝ) / n else 0

/-- **Value of a digit string.** For a natural number $b$ and a base-$b$ digit string
$X = x_1 x_2 \cdots x_\ell$ with digits $x_i \in \{0, \dots, b-1\}$, written with the most
significant digit first, the integer value of $X$ is

$$
n(X) = \sum_{i=1}^{\ell} x_i\, b^{\ell - i},
$$

so the last digit $x_\ell$ has weight $b^0 = 1$.

These exponents correct a typo in the corresponding displayed formula of the source.

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Notation and Terminology. -/
public def stringValue (b : ℕ) (X : List (Fin b)) : ℕ :=
  X.foldl (fun n a => b * n + a.val) 0

/-- **Normalized value of a digit string.** For a base $b$ and a string $X$ of base-$b$ digits,
written most significant digit first, with integer value $n(X)$ and length $|X|$, the normalized
value of $X$ is the real number $n(X) / b^{|X|}$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def normalizedStringValue (b : ℕ) (X : List (Fin b)) : ℝ :=
  (stringValue b X : ℝ) / (b : ℝ) ^ X.length

/-- **Weight of a digit string.** For a natural number $b$ and a base-$b$ digit string $X$ of
length $|X|$, the weight of $X$ is $b^{-|X|}$, regarded as an element of $[0, \infty]$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def stringWeight (b : ℕ) (X : List (Fin b)) : ℝ≥0∞ :=
  ENNReal.ofReal ((b : ℝ) ^ (-(X.length : ℤ)))

/-- **Atom of a digit string.** For a natural number $b$ and a base-$b$ digit string $X$ of
length $|X|$ and integer value $n(X)$, the atom of $X$ is the measure
$b^{-|X|}\,\delta_{n(X)/b^{|X|}}$ on $\mathbb{R}$: the Dirac measure at the point $n(X)/b^{|X|}$,
scaled by the weight $b^{-|X|}$.

The Irwin measures are sums of these atoms.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def stringAtom (b : ℕ) (X : List (Fin b)) : Measure ℝ :=
  stringWeight b X • Measure.dirac (normalizedStringValue b X)

/-- **Irwin measure.** Let $b$, $d$ and $k$ be natural numbers with $d < b$. For a finite string
$X$ of base-$b$ digits (of any length, including the empty string, with leading zeros allowed),
read most significant digit first, let $|X|$ be its length and $n(X)$ the integer it represents.
The Irwin measure $\mu_k$ of base $b$ and digit $d$ with index $k$ is the measure on $\mathbb{R}$
obtained by summing, over all strings $X$ containing exactly $k$ occurrences of the digit $d$,
the point mass of weight $b^{-|X|}$ at $n(X)/b^{|X|}$.

Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, definition of `μ_k`. -/
public noncomputable def irwinMeasure (b d k : ℕ) (hd : d < b) : Measure ℝ :=
  Measure.sum (fun X : {X : List (Fin b) // X.count ⟨d, hd⟩ = k} =>
    stringAtom b X.1)

/-- **Leading digits.** For natural numbers $b$, $l$ and $m$, let $L$ be the number of digits of
$m$ in base $b$. The leading-digits integer of $m$ is the natural-number quotient of $m$ by
$b^{\max(L - l,\, 0)}$, rounded down (with quotient $0$ when the divisor is $0$). For $b \ge 2$
and $L \ge l$ this is the integer formed by the first $l$ base-$b$ digits of $m$; when $L < l$
it is $m$ itself, and statements using this notion separately require $L \ge l$.

Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, notation before Proposition 4. -/
public def leadingDigits (b l m : ℕ) : ℕ :=
  m / b ^ (integerLength b m - l)

/-- **Prefix-restricted reciprocal terms.** For natural numbers $b$, $d$, $k$, $n$ and $m$, write
$L(x)$ for the number of base-$b$ digits of $x$. The term is $1/m$ when $m$ is positive,
$L(n) \le L(m)$, the leading-digits integer of $m$ keeping its first $L(n)$ digits equals $n$,
and $m$ has exactly $k$ occurrences of $d$ in base $b$; otherwise the term is $0$. For $b \ge 2$
the leading-digits condition says that the base-$b$ expansion of $m$ begins with that of $n$.

Source: Jean-François Burnol, *Measures for the
Summation of Irwin Series*, INTEGERS 26 (2026), Article A11, notation before
Proposition 4. -/
public noncomputable def leadingReciprocalTerm (b d k n m : ℕ) : ℝ :=
  if 0 < m ∧ integerLength b n ≤ integerLength b m ∧
      leadingDigits b (integerLength b n) m = n ∧ digitCount b d m = k then
    (1 : ℝ) / m
  else
    0

/-- **Prefix-restricted Irwin sum.** For natural numbers $b$, $d$, $k$ and $n$, this is the sum of
the prefix-restricted reciprocal terms over all natural numbers $m$: the sum of $1/m$ over the
positive integers $m$ with at least as many base-$b$ digits as $n$, whose leading-digits integer
keeping as many digits as $n$ has equals $n$, and with exactly $k$ occurrences of $d$ in base
$b$. For $b \ge 2$ the middle condition says that the base-$b$ expansion of $m$ begins with that
of $n$. It is taken as an unconditional sum of real numbers, with the value $0$ if this family is
not summable; the results that take a limit of this sum also assert summability.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Theorem 3. -/
public noncomputable def leadingIrwinSum (b d k n : ℕ) : ℝ :=
  ∑' m : ℕ, leadingReciprocalTerm b d k n m

/-- **Ordinary moments of the Irwin measures.** For natural numbers $b$, $d$, $k$, $m$ with
$d < b$, the ordinary moment $u_{k;m}$ is the integral of $x^m$ over $[0,1)$ with respect to the
Irwin measure $\mu_k$ of base $b$ and digit $d$:

$$
u_{k;m} = \int_{[0,1)} x^m \, d\mu_k(x).
$$

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, definition before Corollary 1. -/
public noncomputable def ordinaryMoment (b d k m : ℕ) (hd : d < b) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, x ^ m ∂irwinMeasure b d k hd

/-- **Complementary moment.** For natural numbers $b$, $d$, $k$ and $m$ with $d < b$, let $\mu_k$
be the Irwin measure for base $b$, digit $d$ and digit count $k$. The complementary moment is
$$
v_{k;m} = \int_{[0,1)} (1 - x)^m \, d\mu_k(x).
$$

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, definition before Corollary 2. -/
public noncomputable def complementaryMoment (b d k m : ℕ) (hd : d < b) : ℝ :=
  ∫ x in Set.Ico (0 : ℝ) 1, (1 - x) ^ m ∂irwinMeasure b d k hd

/-- **Complementary digit power sum.** For natural numbers $b$, $d$ and $j$, let $d' = b - 1 - d$,
computed by natural-number subtraction (so $d' = 0$ when $d \ge b - 1$). The complementary digit
power sum $\gamma'_j$ is the real number $\sum_{0 \le a < b,\ a \ne d'} a^j$, the sum of the
$j$-th powers of the base-$b$ digits other than $d'$, with the convention $0^0 = 1$.

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Theorem 2. -/
public def complementaryDigitPowerSum (b d j : ℕ) : ℝ :=
  digitPowerSum b (b - 1 - d) j

/-- **Complementary moment recurrence.** Let $b$ and $d$ be natural numbers, let $d' = b - 1 - d$
(natural-number subtraction), and let $\gamma'_i$ be the complementary digit power sum for $b$ and
$d$. A family $(v_{j,m})_{j, m \ge 0}$ of real numbers satisfies the complementary moment
recurrence when, for every $m \ge 0$,
$$
(b^{m+1} - b + 1)\, v_{0,m} = b^{m+1} + \sum_{i=1}^{m} \binom{m}{i} \gamma'_i \, v_{0,m-i},
$$
and, for every $j \ge 1$ and every $m \ge 0$,
$$
(b^{m+1} - b + 1)\, v_{j,m} = \sum_{i=1}^{m} \binom{m}{i} \gamma'_i \, v_{j,m-i} +
\sum_{i=0}^{m} \binom{m}{i} (d')^i \, v_{j-1,m-i},
$$
with the convention $0^0 = 1$.

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Theorem 2. -/
public def ComplementaryMomentRecurrence (b d : ℕ) (v : ℕ → ℕ → ℝ) : Prop :=
  (∀ m,
    (((b : ℝ) ^ (m + 1) - b + 1) * v 0 m =
      (b : ℝ) ^ (m + 1) +
        ∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * complementaryDigitPowerSum b d i * v 0 (m - i))) ∧
    (∀ j, 1 ≤ j → ∀ m,
      (((b : ℝ) ^ (m + 1) - b + 1) * v j m =
        (∑ i ∈ Finset.Icc 1 m,
          (Nat.choose m i : ℝ) * complementaryDigitPowerSum b d i * v j (m - i)) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.choose m i : ℝ) * (b - 1 - d : ℕ) ^ i * v (j - 1) (m - i)))

/-- **Base depth of a real number.** For a natural number $b$, a real number $x$ and a natural
number $l$, the number $x$ has base-$b$ depth $l$ when $x = z / b^l$ for some integer $z$, and for
no $q < l$ is there an integer $z$ with $x = z / b^q$. Thus $l$ is the least exponent for which
$x$ can be written as an integer divided by $b^l$.

Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Notation and Terminology. -/
public def HasBaseDepth (b : ℕ) (x : ℝ) (l : ℕ) : Prop :=
  (∃ z : ℤ, x = (z : ℝ) / (b : ℝ) ^ l) ∧
    ∀ q < l, ¬ ∃ z : ℤ, x = (z : ℝ) / (b : ℝ) ^ q

/-- **Scaled translate of a set.** For natural numbers $b$ and $l$, a real number $x$ and a set
$U \subseteq \mathbb{R}$, the affine scale set $b^l U - b^l x$ is the image of $U$ under the map
$y \mapsto b^l y - b^l x$, that is, $\{\, b^l y - b^l x : y \in U \,\}$.

Source: Jean-François Burnol,
*Measures for the Summation of Irwin Series*, INTEGERS 26 (2026), Article A11,
Lemma 2. -/
public def affineScaleSet (b l : ℕ) (x : ℝ) (U : Set ℝ) : Set ℝ :=
  (fun y : ℝ => (b : ℝ) ^ l * y - (b : ℝ) ^ l * x) '' U

/-- **Zero has no digits.** For all natural numbers $b$ and $d$, the digit $d$ occurs $0$ times in
the minimal base-$b$ representation of $0$, which is empty.

Source: Jean-François Burnol, *Measures for the Summation of
Irwin Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public theorem digitCount_zero (b d : ℕ) : digitCount b d 0 = 0 := by
  simp [digitCount]

/-- **The empty digit string has value zero.** For every natural number $b$, the integer value
of the empty base-$b$ digit string is $0$.

Source: Jean-François Burnol, *Measures for the Summation of Irwin
Series*, INTEGERS 26 (2026), Article A11, Notation and Terminology. -/
public theorem stringValue_nil (b : ℕ) : stringValue b [] = 0 := by
  rfl

/-- **The atom of the empty string is the unit Dirac mass at the origin.** For every natural
number $b$, the atom $b^{-|X|}\,\delta_{n(X)/b^{|X|}}$ of a base-$b$ digit string $X$ is the
Dirac measure $\delta_0$ when $X$ is the empty string.

This concerns the summand of the empty string alone, not the total mass that an Irwin measure
places at $0$ once all strings with the same value are combined.

Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, definition of `μ_k` and Remark `rem:zero`. -/
public theorem stringAtom_nil (b : ℕ) : stringAtom b [] = Measure.dirac 0 := by
  simp [stringAtom, stringWeight, normalizedStringValue, stringValue]

end

end MetaMathlibExt
