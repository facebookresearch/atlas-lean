/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.QuadraticForms.Reduced
public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares

namespace MetaMathlibExt

@[expose] public section

/-- Gauss reducedness of `a * x ^ 2 + b * x * y + c * y ^ 2` is decidable: it is a
conjunction of integer comparisons.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1
(reduced forms `-a < b ≤ a < c` or `0 ≤ b ≤ a = c`, which is
`BinaryQuadraticForm.IsGaussReduced` together with positive definiteness). The instance is
local to this file, so importing it does not change instance search elsewhere. -/
public local instance decidableIsGaussReduced (a b c : ℤ) :
    Decidable (BinaryQuadraticForm.IsGaussReduced a b c) :=
  inferInstanceAs (Decidable (0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)))

/-- **Reduced forms of a given discriminant.** For an integer $d$, $R(d)$ is the finite set of
integer triples $(a, b, c)$ such that the binary quadratic form $a x^2 + b x y + c y^2$ is Gauss
reduced (that is, $a > 0$, $b^2 - 4ac < 0$, $|b| \le a \le c$, and $b \ge 0$ whenever $|b| = a$ or
$a = c$) and has discriminant $b^2 - 4ac = d$. In particular $R(d)$ is empty when $d \ge 0$.

The set is computed by a finite search: a reduced form satisfies $-d = 4ac - b^2 \ge 3a^2$, so
$1 \le a \le \lfloor \sqrt{-d} \rfloor$ and $|b| \le a$, and $c = (b^2 - d) / (4a)$ is determined
by $a$ and $b$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public def reducedFormsOfDiscriminant (d : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (Nat.sqrt (-d).toNat)).biUnion fun a =>
      (Finset.Icc (-a) a).image fun b => (a, b, (b ^ 2 - d) / (4 * a))).filter fun q =>
    BinaryQuadraticForm.IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = d

/-- **Gauss class number of a discriminant.** For an integer $d$, the Gauss class number $h(d)$
is the number of integer triples $(a, b, c)$ with $b^2 - 4ac = d$ for which the binary quadratic
form $ax^2 + bxy + cy^2$ is positive definite ($a > 0$ and $d < 0$), reduced ($|b| \le a \le c$,
with $b \ge 0$ whenever $|b| = a$ or $a = c$) and primitive ($\gcd(a, b, c) = 1$).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public def gaussClassNumber (d : ℤ) : ℕ :=
  ((reducedFormsOfDiscriminant d).filter fun q =>
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1).card

/-- **Unweighted Hurwitz class number.** For an integer $d$, the unweighted Hurwitz class number
$H(d)$ is the number of elements of the set $R(d)$ of reduced forms of discriminant $d$, that is,
the number of integer triples $(a, b, c)$, primitive or not, for which $a x^2 + b x y + c y^2$ is
a Gauss-reduced binary quadratic form of discriminant $b^2 - 4ac = d$. Every reduced form is
counted with weight $1$; in particular $H(d) = 0$ when $d \ge 0$.

This differs from the weighted Hurwitz class number, which counts forms equivalent to a multiple
of $x^2 + y^2$ or of $x^2 + x y + y^2$ with weight $1/2$ or $1/3$ (the paper remarks that the
literature uses several conventions).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (1). -/
public def unweightedHurwitzClassNumber (d : ℤ) : ℕ :=
  (reducedFormsOfDiscriminant d).card

/-- **Weight of a reduced binary quadratic form.** The weight of an integer triple $(a, b, c)$,
standing for the form $ax^2 + bxy + cy^2$, is $1/2$ if $a = c$ and $b = 0$, $1/3$ if
$a = b = c \ne 0$, and $1$ otherwise.

On reduced forms the weight is $1/2$ for $a(x^2 + y^2)$, $1/3$ for $a(x^2 + xy + y^2)$, and $1$
for every other form.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (3). -/
public def reducedFormWeight (q : ℤ × ℤ × ℤ) : ℚ :=
  if q.1 = q.2.2 ∧ q.2.1 = 0 then 1 / 2
  else if q.1 = q.2.1 ∧ q.2.1 = q.2.2 then 1 / 3 else 1

/-- **Kronecker's sum $F_o(n)$.** For a natural number $n$, $F_o(n)$ is the sum of the weights of
the reduced positive-definite integral binary quadratic forms $ax^2 + bxy + cy^2$ of
discriminant $b^2 - 4ac = -4n$ in which $a$ or $c$ is odd. Here a form is reduced when
$|b| \le a \le c$, with $b \ge 0$ whenever $|b| = a$ or $a = c$, and its weight is $1/2$ if
$a = c$ and $b = 0$, $1/3$ if $a = b = c$, and $1$ otherwise.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (4). -/
public def kroneckerFOdd (n : ℕ) : ℚ :=
  ∑ q ∈ (reducedFormsOfDiscriminant (-4 * n)).filter (fun q => Odd q.1 ∨ Odd q.2.2),
    reducedFormWeight q

/-- **Kronecker's sum $F_e(n)$.** For a natural number $n$, $F_e(n)$ is the sum of the weights of
the reduced positive-definite integral binary quadratic forms $ax^2 + bxy + cy^2$ of
discriminant $b^2 - 4ac = -4n$ in which $a$ and $c$ are both even. Here a form is reduced when
$|b| \le a \le c$, with $b \ge 0$ whenever $|b| = a$ or $a = c$, and its weight is $1/2$ if
$a = c$ and $b = 0$, $1/3$ if $a = b = c$, and $1$ otherwise.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equation (5). -/
public def kroneckerFEven (n : ℕ) : ℚ :=
  ∑ q ∈ (reducedFormsOfDiscriminant (-4 * n)).filter (fun q => Even q.1 ∧ Even q.2.2),
    reducedFormWeight q

/-- **The discriminant $d(\alpha, g)$ attached to $n = 2^\alpha g h^2$.** For natural numbers
$\alpha$ and $g$, let $d(\alpha, g) = -8g$ if $\alpha$ is odd; if $\alpha$ is even, let
$d(\alpha, g) = -4g$ when $g \equiv 1 \pmod 4$ and $d(\alpha, g) = -g$ otherwise.

In the paper $n = 2^\alpha g h^2$ with $g$ and $h$ odd and $g$ squarefree, so the last case is
$g \equiv 3 \pmod 4$; the paper writes $d(n)$ for $d(\alpha, g)$, the fundamental discriminant of
$\mathbb{Q}(\sqrt{-n})$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1, after
equation (17). -/
public def kroneckerDiscriminant (α g : ℕ) : ℤ :=
  if Even α then (if g % 4 = 1 then -4 * g else -g) else -8 * g

/-- **Kronecker's class-number multiplier.** For an integer $d$ and a natural number $h \ge 1$,
$\ell(d, h)$ is the product, over the primes $p$ dividing $h$, of
$$\sum_{i=0}^{v} p^i - \left(\frac{d}{p}\right) \sum_{i=0}^{v-1} p^i,$$
where $v$ is the exponent of $p$ in $h$ and $\left(\frac{d}{p}\right)$ is the Jacobi symbol; in
particular $\ell(d, 1) = 1$. Also $\ell(d, 0) = 1$.

In the paper $h$ is odd, so each $p$ is an odd prime, the symbol is the Legendre symbol, and the
factor equals $\frac{p^{v+1} - 1}{p - 1} - \left(\frac{d}{p}\right) \frac{p^v - 1}{p - 1}$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1, definition
of `ℓ(n)`. -/
public def kroneckerClassMultiplier (d : ℤ) (h : ℕ) : ℤ :=
  ∏ p ∈ h.primeFactors,
    ((∑ i ∈ Finset.range (h.factorization p + 1), (p : ℤ) ^ i) -
      jacobiSym d p * ∑ i ∈ Finset.range (h.factorization p), (p : ℤ) ^ i)

/-- **Class numbers of the discriminants $-3$, $-4$ and $-12$.** The Gauss class numbers satisfy
$h(-3) = h(-4) = h(-12) = 1$, and the unweighted Hurwitz class number satisfies $H(-12) = 2$.

The two reduced forms of discriminant $-12$ are $x^2 + 3y^2$ and the imprimitive form
$2x^2 + 2xy + 2y^2$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public theorem gaussClassNumber_small :
    gaussClassNumber (-3) = 1 ∧ gaussClassNumber (-4) = 1 ∧ gaussClassNumber (-12) = 1 ∧
      unweightedHurwitzClassNumber (-12) = 2 := by
  decide +kernel

/-- **Kronecker's sums at $n = 1$ and $n = 3$.** Kronecker's sums $F_o$ and $F_e$ satisfy
$F_o(1) = 1/2$, $F_e(1) = 0$, $F_o(3) = 1$ and $F_e(3) = 1/3$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, equations (4)
and (5). -/
public theorem kroneckerF_small :
    kroneckerFOdd 1 = 1 / 2 ∧ kroneckerFEven 1 = 0 ∧ kroneckerFOdd 3 = 1 ∧
      kroneckerFEven 3 = 1 / 3 := by
  decide +kernel

/-- **Small values of the discriminant $d(\alpha, g)$ and the multiplier $\ell(d, h)$.** The
discriminant attached to $n = 2^\alpha g h^2$ satisfies $d(0, 1) = -4$, $d(0, 3) = -3$ and
$d(1, 1) = -8$, and Kronecker's class-number multiplier satisfies $\ell(-4, 1) = 1$ and
$\ell(-4, 3) = 5$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public theorem kroneckerDiscriminant_kroneckerClassMultiplier_small :
    kroneckerDiscriminant 0 1 = -4 ∧ kroneckerDiscriminant 0 3 = -3 ∧
      kroneckerDiscriminant 1 1 = -8 ∧ kroneckerClassMultiplier (-4) 1 = 1 ∧
      kroneckerClassMultiplier (-4) 3 = 5 := by
  decide +kernel

/-- **Gauss's three-square formula after Aygin and Williams.** Let $n$, $\alpha$, $g$, $h$ be
natural numbers with $n = 2^\alpha g h^2$, where $g$ and $h$ are odd and $g$ is squarefree. Let
$d$ be the Kronecker discriminant of $(\alpha, g)$, namely $d = -4g$ if $\alpha$ is even and
$g \equiv 1 \pmod 4$, $d = -g$ if $\alpha$ is even and $g \equiv 3 \pmod 4$, and $d = -8g$ if
$\alpha$ is odd. Put $L = \ell(d, h) \, h(d)$, where $\ell(d, h)$ is the Kronecker class
multiplier and $h(d)$ is the Gauss class number of $d$, and let $r_3(n)$ be the number of ordered
triples $(x, y, z)$ of integers with $x^2 + y^2 + z^2 = n$. Then: if $\alpha$ is even and $g = 1$,
then $r_3(n) = 6L$; if $\alpha$ is even and $g = 3$, then $r_3(n) = 8L$; if $\alpha$ is even,
$g \equiv 1 \pmod 4$ and $g \ne 1$, then $r_3(n) = 12L$; if $\alpha$ is even, $g \equiv 3 \pmod 8$
and $g \ne 3$, then $r_3(n) = 24L$; if $\alpha$ is even and $g \equiv 7 \pmod 8$, then
$r_3(n) = 0$; and if $\alpha$ is odd, then $r_3(n) = 12L$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Theorem 1
(`integers-2026-A29-thm-1`). -/
public theorem_wanted threeSquareRepresentationCount_eq_kronecker_classNumber
    (n α g h : ℕ) (hn : n = 2 ^ α * g * h ^ 2) (hg : Odd g) (hgsq : Squarefree g)
    (hh : Odd h) :
    let L : ℤ := kroneckerClassMultiplier (kroneckerDiscriminant α g) h *
      gaussClassNumber (kroneckerDiscriminant α g)
    let r : ℤ := Nat.threeSquareRepresentationCount n
    (Even α → g = 1 → r = 6 * L) ∧
    (Even α → g = 3 → r = 8 * L) ∧
    (Even α → g % 4 = 1 → g ≠ 1 → r = 12 * L) ∧
    (Even α → g % 8 = 3 → g ≠ 3 → r = 24 * L) ∧
    (Even α → g % 8 = 7 → r = 0) ∧
    (Odd α → r = 12 * L)

/-- **Aygin–Williams evaluation of Kronecker's sums.** Let $n = 2^\alpha g h^2$ with $g$ and $h$
odd natural numbers and $g$ squarefree. Let $d = -4g$ if $\alpha$ is even and
$g \equiv 1 \pmod 4$, $d = -g$ if $\alpha$ is even and $g \equiv 3 \pmod 4$, and $d = -8g$ if
$\alpha$ is odd. Let $L = \ell(d, h) \cdot h(d)$, where $\ell(d, h)$ is Kronecker's class-number
multiplier and $h(d)$ is the Gauss class number of $d$, and for even $\alpha$ let
$t = 2^{\alpha/2}$. Then Kronecker's sums $F_o$ and $F_e$ satisfy:

- if $\alpha$ is even and $g = 1$, then $F_o(n) = \frac{t}{2} L$ and
  $F_e(n) = \left(\frac{t}{2} - \frac{1}{2}\right) L$;
- if $\alpha$ is even and $g = 3$, then $F_o(n) = tL$ and $F_e(n) = \left(t - \frac{2}{3}\right) L$;
- if $\alpha$ is even, $g \equiv 1 \pmod 4$ and $g \ne 1$, then $F_o(n) = tL$ and
  $F_e(n) = (t - 1) L$;
- if $\alpha$ is even, $g \equiv 3 \pmod 8$ and $g \ne 3$, then $F_o(n) = 3tL$ and
  $F_e(n) = (3t - 2) L$;
- if $\alpha$ is even and $g \equiv 7 \pmod 8$, then $F_o(n) = F_e(n) = tL$;
- if $\alpha$ is odd, then $F_o(n) = 2^{(\alpha - 1)/2} L$ and
  $F_e(n) = \left(2^{(\alpha - 1)/2} - 1\right) L$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Theorem 2
(`integers-2026-A29-thm-2`). -/
public theorem_wanted kroneckerFOdd_kroneckerFEven_eq_classNumber
    (n α g h : ℕ) (hn : n = 2 ^ α * g * h ^ 2) (hg : Odd g) (hgsq : Squarefree g)
    (hh : Odd h) :
    let L : ℚ := (kroneckerClassMultiplier (kroneckerDiscriminant α g) h : ℚ) *
      gaussClassNumber (kroneckerDiscriminant α g)
    let t : ℚ := 2 ^ (α / 2)
    (Even α → g = 1 →
      kroneckerFOdd n = t / 2 * L ∧ kroneckerFEven n = (t / 2 - 1 / 2) * L) ∧
    (Even α → g = 3 →
      kroneckerFOdd n = t * L ∧ kroneckerFEven n = (t - 2 / 3) * L) ∧
    (Even α → g % 4 = 1 → g ≠ 1 →
      kroneckerFOdd n = t * L ∧ kroneckerFEven n = (t - 1) * L) ∧
    (Even α → g % 8 = 3 → g ≠ 3 →
      kroneckerFOdd n = 3 * t * L ∧ kroneckerFEven n = (3 * t - 2) * L) ∧
    (Even α → g % 8 = 7 →
      kroneckerFOdd n = t * L ∧ kroneckerFEven n = t * L) ∧
    (Odd α →
      kroneckerFOdd n = (2 : ℚ) ^ ((α - 1) / 2) * L ∧
        kroneckerFEven n = ((2 : ℚ) ^ ((α - 1) / 2) - 1) * L)

/-- **Unweighted Hurwitz class numbers via Gauss class numbers.** Let $n$, $\alpha$, $g$, $h$ be
natural numbers with $n = 2^\alpha g h^2$, where $g$ and $h$ are odd and $g$ is squarefree. Let
$d$ be the Kronecker discriminant of $(\alpha, g)$, namely $d = -4g$ if $\alpha$ is even and
$g \equiv 1 \pmod 4$, $d = -g$ if $\alpha$ is even and $g \equiv 3 \pmod 4$, and $d = -8g$ if
$\alpha$ is odd. Put $L = \ell(d, h) \, h(d)$, where $\ell(d, h)$ is the Kronecker class
multiplier and $h(d)$ is the Gauss class number of $d$, and let $H(-4n)$ be the unweighted
Hurwitz class number of $-4n$. Then, with $\alpha / 2$ and $(\alpha + 1) / 2$ exact quotients in
the cases where they occur: if $\alpha$ is even and $g = 1$, then
$H(-4n) = (2^{\alpha/2} - 1/2) L + 1/2$; if $\alpha$ is even and $g = 3$, then
$H(-4n) = (2^{\alpha/2 + 1} - 2/3) L + 2/3$; if $\alpha$ is even, $g \ne 1$ and
$g \equiv 1 \pmod 4$, then $H(-4n) = (2^{\alpha/2 + 1} - 1) L$; if $\alpha$ is even, $g \ne 3$ and
$g \equiv 3 \pmod 8$, then $H(-4n) = (3 \cdot 2^{\alpha/2 + 1} - 2) L$; if $\alpha$ is even and
$g \equiv 7 \pmod 8$, then $H(-4n) = 2^{\alpha/2 + 1} L$; and if $\alpha$ is odd, then
$H(-4n) = (2^{(\alpha + 1)/2} - 1) L$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Theorem 3
(`integers-2026-A29-thm-3`). -/
public theorem_wanted unweightedHurwitzClassNumber_neg_four_mul_eq_classNumber
    (n α g h : ℕ) (hn : n = 2 ^ α * g * h ^ 2) (hg : Odd g) (hgsq : Squarefree g)
    (hh : Odd h) :
    let L : ℚ := (kroneckerClassMultiplier (kroneckerDiscriminant α g) h : ℚ) *
      gaussClassNumber (kroneckerDiscriminant α g)
    let H : ℚ := unweightedHurwitzClassNumber (-4 * n)
    (Even α → g = 1 → H = ((2 : ℚ) ^ (α / 2) - 1 / 2) * L + 1 / 2) ∧
    (Even α → g = 3 → H = ((2 : ℚ) ^ (α / 2 + 1) - 2 / 3) * L + 2 / 3) ∧
    (Even α → g ≠ 1 → g % 4 = 1 → H = ((2 : ℚ) ^ (α / 2 + 1) - 1) * L) ∧
    (Even α → g ≠ 3 → g % 8 = 3 → H = (3 * (2 : ℚ) ^ (α / 2 + 1) - 2) * L) ∧
    (Even α → g % 8 = 7 → H = (2 : ℚ) ^ (α / 2 + 1) * L) ∧
    (Odd α → H = ((2 : ℚ) ^ ((α + 1) / 2) - 1) * L)

end

end MetaMathlibExt
