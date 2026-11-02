/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.OrdinaryEhrhartCount
public import WantedExt.Combinatorics.WeightedProjectiveSimplexIDPWanted
import Mathlib

namespace MetaMathlibExt

open scoped BigOperators
open Filter Polynomial Set

@[expose] public noncomputable section

/-! # Ehrhart polynomials with roots on the canonical line -/

/-- **Canonical line.** The canonical line $\mathrm{CL}$ is the vertical line of complex numbers
with real part $-1/2$, that is, $\mathrm{CL} = \{z \in \mathbb{C} : \operatorname{Re} z = -1/2\}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Definition of `CL`.
-/
public def canonicalLine : Set ℂ := {z | z.re = -(1 / 2 : ℝ)}

/-- **The h-star coefficients of a polynomial.** Let $f$ be a complex polynomial of degree $d$,
with $d = 0$ for the zero polynomial. For a natural number $i$, the $i$-th $h^*$-coefficient of
$f$ is
$$h^*_i(f) = \sum_{j=0}^{i} (-1)^j \binom{d+1}{j} f(i-j),$$
the coefficient of $t^i$ in the power series $(1-t)^{d+1} \sum_{k \ge 0} f(k)\, t^k$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of the `h*`-polynomial.
-/
public def hStarCoeff (f : Polynomial ℂ) (i : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (i + 1),
    (-1 : ℂ) ^ j * (Nat.choose (f.natDegree + 1) j : ℂ) * f.eval (i - j : ℂ)

/-- **SNN polynomials.** For a complex polynomial $f$ of degree $d$ and a natural number $i$, let
$h^*_i(f)$ be the coefficient of $t^i$ in $(1 - t)^{d+1} \sum_{k \ge 0} f(k)\, t^k$. Then $f$ is
SNN when $f \ne 0$ and its $h^*$-coefficients $h^*_0(f), \dots, h^*_d(f)$ are real and
nonnegative.

Coefficients beyond the degree, which vanish by the generating-series identity, are not part of
the condition.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of SNN-polynomial.
-/
public def IsSNN (f : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧ ∀ i ≤ f.natDegree, 0 ≤ (hStarCoeff f i).re ∧ (hStarCoeff f i).im = 0

/-- **Product of quadratic canonical-line factors.** For a finite list $c_1, \dots, c_m$ of real
numbers, this is the monic complex polynomial $\prod_{k=1}^{m} (X^2 + X + c_k)$; the empty list
gives the constant polynomial $1$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, factored definition of CL-polynomials.
-/
public def clQuadraticProduct (cs : List ℝ) : Polynomial ℂ :=
  (cs.map fun c => X ^ 2 + X + C (c : ℂ)).prod

/-- **CL-polynomials with given parameters.** Let $f$ be a complex polynomial of degree $d$, let
$a$ be a real number, and let $c_1, \dots, c_m$ be a list of real numbers. Then $f$ is a
CL-polynomial with scale $a$ and parameters $c_1, \dots, c_m$ when $a \ne 0$, every $c_i \ge 1/4$,
$m = \lfloor d/2 \rfloor$, and $f = a \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is even and
$f = a (2X + 1) \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is odd.

The parameters form a list so that later statements can refer to individual parameters.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-polynomial.
-/
public def IsCLWithParameters (f : Polynomial ℂ) (a : ℝ) (cs : List ℝ) : Prop :=
  a ≠ 0 ∧
    (∀ c ∈ cs, (1 / 4 : ℝ) ≤ c) ∧
    if Even f.natDegree then
      f = C (a : ℂ) * clQuadraticProduct cs ∧ cs.length = f.natDegree / 2
    else
      f = C (a : ℂ) * (2 * X + 1) * clQuadraticProduct cs ∧
        cs.length = f.natDegree / 2

/-- **CL-polynomials.** A complex polynomial $f$ of degree $d$ is a CL-polynomial when there are
a real number $a \ne 0$ and real numbers $c_1, \dots, c_m \ge 1/4$ with $m = \lfloor d/2 \rfloor$
such that $f = a \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is even and
$f = a (2X + 1) \prod_{i=1}^{m} (X^2 + X + c_i)$ if $d$ is odd.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-polynomial.
-/
public def IsCL (f : Polynomial ℂ) : Prop := ∃ a cs, IsCLWithParameters f a cs

/-- **The basis polynomials $b^d_j$.** For natural numbers $d$ and $j$, $b^d_j$ is the complex
polynomial $b^d_j = \prod_{i=0}^{d-1} (X + d - j - i)$.

Integer constants are used before mapping to $\mathbb{C}$, avoiding any convention about rising
versus falling Pochhammer symbols.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `bᵈⱼ`.
-/
public def bBasis (d j : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range d, (X + C (((d : ℤ) - (j : ℤ) - (i : ℤ) : ℤ) : ℂ))

/-- **Symmetric basis polynomials.** For natural numbers $d$ and $j$, let $b^d_j$ be the complex
polynomial $\prod_{i=0}^{d-1} (X + d - j - i)$. The polynomial $p^d_j$ is $b^d_j$ if $2j = d$, and
$b^d_j + b^d_{d-j}$ otherwise, where $d - j$ is truncated at $0$ (so $p^d_j = b^d_j + b^d_0$ when
$j > d$).

Statements that use $p^d_j$ assume $j \le d$, where the truncation plays no role.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `pᵈⱼ`.
-/
public def pBasis (d j : ℕ) : Polynomial ℂ :=
  if 2 * j = d then bBasis d j else bBasis d j + bBasis d (d - j)

/-- **The basis polynomial $p^1_0$.** The symmetric basis polynomial $p^1_0$ equals the complex
polynomial $2X + 1$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, characteristic case of the `pᵈⱼ` definition.
-/
public theorem pBasis_one_zero : pBasis 1 0 = 2 * X + 1 := by
  simp [pBasis, bBasis]
  ring

/-- **The basis polynomial $p^2_0$.** The symmetric basis polynomial $p^2_0$ equals the complex
polynomial $2(X^2 + X + 1)$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, characteristic case of the `pᵈⱼ` definition.
-/
public theorem pBasis_two_zero : pBasis 2 0 = 2 * (X ^ 2 + X + 1) := by
  simp [pBasis, bBasis, Finset.prod_range_succ]
  have hC2 : (C (2 : ℂ) : Polynomial ℂ) = 2 := by
    rw [show (2 : ℂ) = 1 + 1 by ring, map_add, C_1]
    ring
  rw [hC2]
  ring

/-- **Interlacing lists.** Let $r$ be a binary relation on a type $\alpha$ and let $d \ge 0$.
A list $(a_1, \dots, a_d)$ interlaces a list $(b_1, \dots, b_{d+1})$ with respect to $r$ when
$b_1 \mathrel{r} a_1 \mathrel{r} b_2 \mathrel{r} \cdots \mathrel{r} a_d \mathrel{r} b_{d+1}$,
that is, $b_k \mathrel{r} a_k$ and $a_k \mathrel{r} b_{k+1}$ for $1 \le k \le d$. Two lists
interlace only when the second has exactly one more entry than the first; in particular the
empty list interlaces every one-element list.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of interlacing.
-/
public def ListInterlaces {α : Type*} (r : α → α → Prop) : List α → List α → Prop
  | [], [_] => True
  | a :: as, b :: b' :: bs => r b a ∧ r a b' ∧ ListInterlaces r as (b' :: bs)
  | _, _ => False

/-- **Alternating lists of equal length.** Let $r$ be a binary relation on a type $\alpha$ and
let $n \ge 0$. A list $(a_1, \dots, a_n)$ alternates with a list $(b_1, \dots, b_n)$ with
respect to $r$ when
$a_1 \mathrel{r} b_1 \mathrel{r} a_2 \mathrel{r} \cdots \mathrel{r} a_n \mathrel{r} b_n$,
that is, $a_k \mathrel{r} b_k$ for $1 \le k \le n$ and $b_k \mathrel{r} a_{k+1}$ for
$1 \le k < n$. Two empty lists alternate, and lists of different lengths never alternate.

This equal-length companion of interlacing is used only for the same-degree clauses in Fisk's
Leibniz rule.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 2 (quoting Fisk, Lemma 1.26).
-/
public def ListAlternates {α : Type*} (r : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | [a], [b] => r a b
  | a :: a' :: as, b :: bs => r a b ∧ r b a' ∧ ListAlternates r (a' :: as) bs
  | _, _ => False

/-- **Real interlacing.** Let $f$ and $g$ be real polynomials. Then $f$ interlaces $g$ when $f$ and
$g$ are nonzero with $\deg g = \deg f + 1$, the real roots of $f$, listed with multiplicity, are
exactly $a_1 \le \dots \le a_d$ where $d = \deg f$, the real roots of $g$, listed with
multiplicity, are exactly $b_1 \le \dots \le b_{d+1}$ (so all roots of $f$ and $g$ are real), and
the roots alternate as $b_1 \le a_1 \le b_2 \le a_2 \le \dots \le a_d \le b_{d+1}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of real interlacing.
-/
public def RealInterlaces (f g : Polynomial ℝ) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ f.natDegree + 1 = g.natDegree ∧
    ∃ as bs : List ℝ,
      (as : Multiset ℝ) = f.roots ∧ (bs : Multiset ℝ) = g.roots ∧
        as.length = f.natDegree ∧ bs.length = g.natDegree ∧
        List.Pairwise (· ≤ ·) as ∧ List.Pairwise (· ≤ ·) bs ∧
        ListInterlaces (· ≤ ·) as bs

/-- **Alternating roots of equal-degree real polynomials.** Let $f$ and $g$ be real polynomials.
Their roots alternate when $f$ and $g$ are nonzero of the same degree $n$, the real roots of $f$,
listed with multiplicity, are exactly $a_1 \le \dots \le a_n$, those of $g$ are exactly
$b_1 \le \dots \le b_n$ (so all roots of $f$ and $g$ are real), and either
$a_1 \le b_1 \le a_2 \le b_2 \le \dots \le a_n \le b_n$ or
$b_1 \le a_1 \le b_2 \le a_2 \le \dots \le b_n \le a_n$.

This equal-degree notion is used for two clauses of Fisk's Leibniz rule.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 2 (quoting Fisk, Lemma 1.26).
-/
public def RealAlternates (f g : Polynomial ℝ) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ f.natDegree = g.natDegree ∧
    ∃ as bs : List ℝ,
      (as : Multiset ℝ) = f.roots ∧ (bs : Multiset ℝ) = g.roots ∧
        as.length = f.natDegree ∧ bs.length = g.natDegree ∧
        List.Pairwise (· ≤ ·) as ∧ List.Pairwise (· ≤ ·) bs ∧
        (ListAlternates (· ≤ ·) as bs ∨ ListAlternates (· ≤ ·) bs as)

/-- **Interlacing on the canonical line.** A complex polynomial $f$ CL-interlaces a complex
polynomial $g$ when $f$ and $g$ are nonzero, $\deg g = \deg f + 1$, all roots of $f$ and of $g$
lie on the canonical line, and, writing $d = \deg f$ and listing the roots with multiplicity as
$a_1, \dots, a_d$ for $f$ and $b_1, \dots, b_{d+1}$ for $g$, each list sorted by increasing
imaginary part, they alternate:
$\operatorname{Im} b_1 \le \operatorname{Im} a_1 \le \operatorname{Im} b_2 \le \cdots \le
\operatorname{Im} a_d \le \operatorname{Im} b_{d+1}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-interlacing.
-/
public def CLInterlaces (f g : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ f.natDegree + 1 = g.natDegree ∧
    ∃ as bs : List ℂ,
      (as : Multiset ℂ) = f.roots ∧ (bs : Multiset ℂ) = g.roots ∧
        as.length = f.natDegree ∧ bs.length = g.natDegree ∧
        (∀ z ∈ as, z ∈ canonicalLine) ∧ (∀ z ∈ bs, z ∈ canonicalLine) ∧
        List.Pairwise (fun x y => x.im ≤ y.im) as ∧
        List.Pairwise (fun x y => x.im ≤ y.im) bs ∧
        ListInterlaces (fun x y => x.im ≤ y.im) as bs

/-- **Real-rooted polynomials.** A real polynomial $f$ has only real roots when $f \ne 0$ and the
number of real roots of $f$, counted with multiplicity, equals the degree of $f$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 2 (quoting Fisk, Lemma 1.26).
-/
public def HasOnlyRealRoots (f : Polynomial ℝ) : Prop :=
  f ≠ 0 ∧ f.roots.card = f.natDegree

/-- **Lattice points as real points.** A lattice point $x = (x_1, \dots, x_d) \in \mathbb{Z}^d$
is regarded as the point of $\mathbb{R}^d$ with the same coordinates $x_1, \dots, x_d$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of a lattice polytope.
-/
public def latticePointToReal {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ := fun i => x i

/-- **Lattice polytopes.** The lattice polytope spanned by a finite set $V \subseteq \mathbb{Z}^d$
is the convex hull in $\mathbb{R}^d$ of the points of $V$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of a lattice polytope.
-/
public def latticePolytope {d : ℕ} (vertices : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  convexHull ℝ (latticePointToReal '' (vertices : Set (Fin d → ℤ)))

/-- **Full-dimensional sets.** A subset $P$ of $\mathbb{R}^d$ is full-dimensional when it is
nonempty and the direction of its affine span is all of $\mathbb{R}^d$ (equivalently, the affine
span of $P$ is $\mathbb{R}^d$).

Nonemptiness matters only for $d = 0$: the empty subset of $\mathbb{R}^0$ has an affine span
whose direction $\{0\}$ is all of $\mathbb{R}^0$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, full-dimensional lattice-polytope convention.
-/
public def IsFullDimensional {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  P.Nonempty ∧ (affineSpan ℝ P).direction = ⊤

/-- **Polynomial counting the lattice points of dilates.** Let $V \subseteq \mathbb{Z}^d$ be a
finite set and let $P \subseteq \mathbb{R}^d$ be the lattice polytope spanned by $V$, its convex
hull. A complex polynomial $E$ counts the lattice points of $P$ when, for every natural number
$k$, $E(k)$ equals the ordinary Ehrhart count $|kP \cap \mathbb{Z}^d|$, the number of points of
$\mathbb{Z}^d$ of the form $kx$ with $x$ a rational point of $P$.

By Ehrhart's theorem such a polynomial exists, and it is unique.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of the Ehrhart polynomial.
-/
public def EhrhartCounts {d : ℕ} (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ) : Prop :=
  ∀ k : ℕ, E.eval (k : ℂ) =
    (ordinaryEhrhartCount d
      {x : Fin d → ℚ | (fun i => (x i : ℝ)) ∈ latticePolytope vertices} k : ℂ)

/-- **Binomial polynomial.** For an integer $n$ and a natural number $d$, the binomial polynomial
$\binom{X+n}{d}$ is the real polynomial $\frac{1}{d!} \prod_{i=0}^{d-1} (X + n - i)$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 7.
-/
public def binomialPolynomial (n : ℤ) (d : ℕ) : Polynomial ℝ :=
  ((d.factorial : ℝ)⁻¹) •
    ∏ i ∈ Finset.range d, (X + C ((n - (i : ℤ) : ℤ) : ℝ))

/-- **Complex binomial polynomial.** For an integer $n$ and a natural number $d$, the complex
binomial polynomial $\binom{X+n}{d} \in \mathbb{C}[X]$ is
$$\binom{X+n}{d} = \frac{1}{d!} \prod_{i=0}^{d-1} (X + n - i).$$

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 3 (quoting Braun and Develin, Theorem 2.3).
-/
public def complexBinomialPolynomial (n : ℤ) (d : ℕ) : Polynomial ℂ :=
  ((d.factorial : ℂ)⁻¹) •
    ∏ i ∈ Finset.range d, (X + C ((n - (i : ℤ) : ℤ) : ℂ))

/-- **Model polynomial.** For a natural number $d$, the model polynomial is the complex
polynomial $M_d = \binom{X+d}{d} + \binom{X}{d}$, where for an integer $n$ the binomial
polynomial $\binom{X+n}{d}$ is $\frac{1}{d!}\prod_{i=0}^{d-1} (X + n - i)$.

For $d \ge 1$, $d!\,M_d$ is the symmetric basis polynomial $p^d_0$; the paper emphasizes that
$M_d$ need not be an Ehrhart polynomial.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 3 (quoting Braun and Develin, Theorem 2.3).
-/
public def modelPolynomial (d : ℕ) : Polynomial ℂ :=
  complexBinomialPolynomial d d + complexBinomialPolynomial 0 d

/-- **Property (♢).** For a complex polynomial $f$ of degree $d$ and a natural number $i$, let
$h^*_i(f)$ be the coefficient of $t^i$ in $(1 - t)^{d+1} \sum_{k \ge 0} f(k)\, t^k$. Then $f$ has
property (♢) when $f \ne 0$ and its $h^*$-coefficients $h^*_0(f), \dots, h^*_d(f)$ are real,
nonnegative and palindromic, that is, $h^*_i(f) = h^*_{d-i}(f)$ for $0 \le i \le d$.

For CL-polynomials the paper notes that palindromicity is automatic; it is kept here as part of
the property.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `(♢)`.
-/
public def HasDiamond (f : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧
    (∀ i ≤ f.natDegree, hStarCoeff f i = hStarCoeff f (f.natDegree - i)) ∧
    ∀ i ≤ f.natDegree, 0 ≤ (hStarCoeff f i).re ∧ (hStarCoeff f i).im = 0

/-- **The set $\Omega_d$ of attainable canonical-line roots.** For a natural number $d$,
$\Omega_d$ is the set of complex numbers $z$ on the canonical line such that $z$ is a root of
some CL-polynomial of degree $d$ satisfying $(\diamondsuit)$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `Ω_d`.
-/
public def canonicalLineRootSet (d : ℕ) : Set ℂ :=
  {z | z ∈ canonicalLine ∧
    ∃ f : Polynomial ℂ, f.natDegree = d ∧ IsCL f ∧ HasDiamond f ∧ f.IsRoot z}

/-- **Functional equation versus palindromic h-star coefficients.** Let $f$ be a nonzero complex
polynomial of degree $d$ with $h^*$-coefficients $h^*_0(f), \dots, h^*_d(f)$. Then
$f(X-1) = (-1)^d f(-X)$ as polynomials if and only if $h^*_i(f) = h^*_{d-i}(f)$ for every
$i \le d$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 1 (quoting Corollary 2.2 in Kölbl's [11]).
-/
public theorem_wanted functionalEquation_iff_hStar_palindromic (f : Polynomial ℂ) (hf : f ≠ 0) :
    f.comp (X - 1) = C ((-1 : ℂ) ^ f.natDegree) * f.comp (-X) ↔
      ∀ i ≤ f.natDegree, hStarCoeff f i = hStarCoeff f (f.natDegree - i)

/-- **Values of CL-polynomials on the canonical line.** If $f$ is a CL-polynomial of degree $d$,
then for every $z$ on the canonical line there is a real number $r$ with $f(z) = r\, i^d$; that
is, $f$ maps the canonical line into $\mathbb{R}\, i^d$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 2.
-/
public theorem_wanted cl_value_on_canonicalLine (f : Polynomial ℂ) (hf : IsCL f)
    (z : ℂ) (hz : z ∈ canonicalLine) :
    ∃ r : ℝ, f.eval z = (r : ℂ) * Complex.I ^ f.natDegree

/-- **$p^d_0$ CL-interlaces $p^{d+1}_0$.** For every natural number $d \ge 1$, the symmetric
basis polynomial $p^d_0$ CL-interlaces $p^{d+1}_0$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 4.
-/
public theorem_wanted pBasis_zero_interlaces_succ (d : ℕ) (hd : 0 < d) :
    CLInterlaces (pBasis d 0) (pBasis (d + 1) 0)

/-- **CL-interlacing of $p^d_0$ with a perturbation of $p^{d+1}_0$.** For every natural number
$d \ge 1$ and every real number $w > 0$, the symmetric basis polynomial $p^d_0$ CL-interlaces
the polynomial $p^{d+1}_0 + w \, (2X + 1) \, p^d_0$.

The orientation follows the numbered statement in the INTEGERS version; the arXiv wording
differs.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 5.
-/
public theorem_wanted pBasis_zero_interlaces_perturbation (d : ℕ) (hd : 0 < d)
    (w : ℝ) (hw : 0 < w) :
    CLInterlaces (pBasis d 0)
      (pBasis (d + 1) 0 + C (w : ℂ) * (2 * X + 1) * pBasis d 0)

/-- **Multiplying by $2X+1$ preserves SNN.** For every complex polynomial $f$, if $f$ is an SNN
polynomial, then so is $(2X + 1) f$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 6.
-/
public theorem_wanted two_mul_X_add_one_preserves_snn (f : Polynomial ℂ) (hf : IsSNN f) :
    IsSNN ((2 * X + 1) * f)

/-- **Multiplying a binomial polynomial by a quadratic.** For an integer $n$ and a natural number
$k$, write $\binom{X+n}{k} = \frac{1}{k!} \prod_{i=0}^{k-1} (X + n - i)$ for the real binomial
polynomial. Let $d$ and $j$ be natural numbers with $0 < d$ and $j \le d$, and let $c$ be a real
number. Then
$$
(X^2 + X + c) \binom{X+d-j}{d} = \alpha \binom{X+d-j+2}{d+2} + \beta \binom{X+d-j+1}{d+2} +
\gamma \binom{X+d-j}{d+2},
$$
where $\alpha = j^2 + j + c$, $\beta = 2(dj - j^2 + d + 1 - c)$ and
$\gamma = d^2 - 2dj - j + j^2 + d + c$.

The paper assumes $c \ge 1/4$; the identity holds for every real $c$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 7.
-/
public theorem_wanted quadratic_mul_binomialPolynomial (d j : ℕ) (hd : 0 < d) (hj : j ≤ d)
    (c : ℝ) :
    (X ^ 2 + X + C c) * binomialPolynomial ((d : ℤ) - (j : ℤ)) d =
      C ((j : ℝ) ^ 2 + (j : ℝ) + c) *
          binomialPolynomial ((d : ℤ) - (j : ℤ) + 2) (d + 2) +
        C (2 * ((d : ℝ) * (j : ℝ) - (j : ℝ) ^ 2 + (d : ℝ) + 1 - c)) *
          binomialPolynomial ((d : ℤ) - (j : ℤ) + 1) (d + 2) +
        C ((d : ℝ) ^ 2 - 2 * (d : ℝ) * (j : ℝ) - (j : ℝ) +
            (j : ℝ) ^ 2 + (d : ℝ) + c) *
          binomialPolynomial ((d : ℤ) - (j : ℤ)) (d + 2)

/-- **Fisk's Leibniz rule for interlacing.** Let $f, f_1, g, g_1$ be real polynomials with
positive leading coefficients, each having only real roots, such that $f$ and $g$ have no common
real root, $f_1$ interlaces $f$, and $g_1$ interlaces $g$. Then $f_1 g_1$ interlaces
$f g_1 + f_1 g$, the polynomial $f g_1 + f_1 g$ interlaces $f g$, the roots of $f g_1 + f_1 g$
alternate with those of $f g_1$ and with those of $f_1 g$, and $f g_1 + f_1 g$ has only real
roots.

Here $p$ interlaces $q$ when $p$ and $q$ are nonzero, $\deg q = \deg p + 1$, and both have only
real roots, whose sorted lists $a_1 \le \dots \le a_n$ and $b_1 \le \dots \le b_{n+1}$ (with
multiplicity) satisfy $b_1 \le a_1 \le b_2 \le \dots \le a_n \le b_{n+1}$. The roots of $p$ and
$q$ alternate when $p$ and $q$ are nonzero of the same degree $n$ and have only real roots, whose
sorted lists satisfy $a_1 \le b_1 \le \dots \le a_n \le b_n$ or
$b_1 \le a_1 \le \dots \le b_n \le a_n$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 2 (quoting Fisk, Lemma 1.26, “Leibnitz rule”).
-/
public theorem_wanted leibniz_rule_interlacing (f f₁ g g₁ : Polynomial ℝ)
    (hflead : 0 < f.leadingCoeff) (hf₁lead : 0 < f₁.leadingCoeff)
    (hglead : 0 < g.leadingCoeff) (hg₁lead : 0 < g₁.leadingCoeff)
    (hfroot : HasOnlyRealRoots f) (hf₁root : HasOnlyRealRoots f₁)
    (hgroot : HasOnlyRealRoots g) (hg₁root : HasOnlyRealRoots g₁)
    (hcoprime : ∀ x : ℝ, ¬(f.IsRoot x ∧ g.IsRoot x))
    (hfint : RealInterlaces f₁ f) (hgint : RealInterlaces g₁ g) :
    RealInterlaces (f₁ * g₁) (f * g₁ + f₁ * g) ∧
      RealInterlaces (f * g₁ + f₁ * g) (f * g) ∧
      RealAlternates (f * g₁ + f₁ * g) (f * g₁) ∧
      RealAlternates (f * g₁ + f₁ * g) (f₁ * g) ∧
      HasOnlyRealRoots (f * g₁ + f₁ * g)

/-- **Coefficientwise limits preserve real interlacing.** Let $(f_n)$ and $(g_n)$ be sequences
of real polynomials with only real roots, and let $f$ and $g$ be nonzero real polynomials such
that, for every $k$, the coefficient of $X^k$ in $f_n$ tends to that in $f$ and the coefficient
of $X^k$ in $g_n$ tends to that in $g$ as $n \to \infty$. Suppose that for all sufficiently
large $n$ the degree of $f_n$ equals the degree of $f$ and the degree of $g_n$ equals the degree
of $g$, and that $f_n$ interlaces $g_n$ for every $n$, in the sense of real interlacing. Then $f$
interlaces $g$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 3 (quoting Fisk, Corollary 1.41).
-/
public theorem_wanted coefficientwise_limit_interlaces
    (fs gs : ℕ → Polynomial ℝ) (f g : Polynomial ℝ)
    (hfs : ∀ n, HasOnlyRealRoots (fs n)) (hgs : ∀ n, HasOnlyRealRoots (gs n))
    (hfconv : ∀ k, Tendsto (fun n => (fs n).coeff k) atTop (nhds (f.coeff k)))
    (hgconv : ∀ k, Tendsto (fun n => (gs n).coeff k) atTop (nhds (g.coeff k)))
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfdeg : ∀ᶠ n in atTop, (fs n).natDegree = f.natDegree)
    (hgdeg : ∀ᶠ n in atTop, (gs n).natDegree = g.natDegree)
    (hint : ∀ n, RealInterlaces (fs n) (gs n)) :
    RealInterlaces f g

/-- **Small sorted CL parameters give an SNN polynomial.** Let $f$ be a complex polynomial of
degree $d$, let $a > 0$ be real, and let $c_0 \le c_1 \le \dots \le c_{m-1}$ be real numbers, each
at least $1/4$, with $m = \lfloor d/2 \rfloor$, such that $f = a \prod_{k=0}^{m-1} (X^2 + X + c_k)$
if $d$ is even and $f = a (2X + 1) \prod_{k=0}^{m-1} (X^2 + X + c_k)$ if $d$ is odd. Suppose that
$c_k \le 2k + 2$ for every $k$ when $d$ is odd, and $c_k \le 2k + 1$ for every $k$ when $d$ is
even. Then $f$ is an SNN polynomial.

The hypothesis $a > 0$ is needed: for $d = 1$, $a = -1$ and no parameters, $f = -(2X + 1)$ is not
SNN, since its zeroth $h^*$-coefficient is $f(0) = -1 < 0$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 5.
-/
public theorem_wanted sorted_cl_parameters_are_snn (f : Polynomial ℂ) (a : ℝ) (cs : List ℝ)
    (d : ℕ) (hdeg : f.natDegree = d) (ha : 0 < a) (hcl : IsCLWithParameters f a cs)
    (hsorted : List.Pairwise (· ≤ ·) cs)
    (hupper : ∀ (k : ℕ) (c : ℝ), cs[k]? = some c →
      if Odd d then c ≤ 2 * (k : ℝ) + 2 else c ≤ 2 * (k : ℝ) + 1) :
    IsSNN f

/-- **Classical bounds on Ehrhart roots.** Let $P \subseteq \mathbb{R}^d$ be a full-dimensional
lattice polytope, the convex hull of a finite set of points of $\mathbb{Z}^d$, and let $E$ be a
complex polynomial with $E(k) = |kP \cap \mathbb{Z}^d|$ for every natural number $k$. Then every
complex root $\alpha$ of $E$ satisfies $|\alpha| \le 1 + (d+1)!$, and every real root $\alpha$
of $E$ satisfies $-d \le \alpha < \lfloor d/2 \rfloor$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 1 (quoting Beck, De Loera, Develin, Pfeifle,
and Stanley, Theorem 1.2).
-/
public theorem_wanted ehrhart_root_classical_bounds {d : ℕ}
    (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ)
    (hfull : IsFullDimensional (latticePolytope vertices))
    (hcount : EhrhartCounts vertices E) :
    (∀ α : ℂ, E.IsRoot α → ‖α‖ ≤ 1 + (d + 1).factorial) ∧
      ∀ α : ℂ, E.IsRoot α → α.im = 0 →
        -(d : ℝ) ≤ α.re ∧ α.re < (d / 2 : ℕ)

/-- **Braun's disc for Ehrhart roots.** Let $P \subseteq \mathbb{R}^d$ be a full-dimensional
lattice polytope, the convex hull of a finite set of points of $\mathbb{Z}^d$, and let $E$ be a
complex polynomial with $E(k) = |kP \cap \mathbb{Z}^d|$ for every natural number $k$. Then every
root $\alpha$ of $E$ lies in the closed disc centered at $-1/2$ with radius $d(d - 1/2)$, that
is, $|\alpha + 1/2| \le d(d - 1/2)$.

By Ehrhart's theorem, $E$ has degree $d$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 2 (quoting Braun, Theorem 1).
-/
public theorem_wanted ehrhart_roots_in_braun_disc {d : ℕ}
    (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ)
    (hfull : IsFullDimensional (latticePolytope vertices))
    (hcount : EhrhartCounts vertices E)
    (α : ℂ) (hroot : E.IsRoot α) :
    ‖α + (1 / 2 : ℝ)‖ ≤ (d : ℝ) * ((d : ℝ) - 1 / 2)

/-- **Asymptotics of the largest root of the model polynomial.** For $d \ge 0$ let
$M_d = \binom{X+d}{d} + \binom{X}{d}$ be the model polynomial. Let $(\beta_d)_{d \ge 0}$ be a
sequence of complex numbers such that for every $d \ge 1$, $\beta_d$ is a root of $M_d$ and
$|\gamma| \le |\beta_d|$ for every root $\gamma$ of $M_d$. Then
$|\beta_d + \tfrac12| - d^2/\pi = O(1)$ as $d \to \infty$.

No condition is placed on $\beta_0$ because $M_0$ is constant; this does not affect the
asymptotic statement.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 3 (quoting Braun and Develin, Theorem 2.3).
-/
public theorem_wanted maximal_model_root_asymptotic :
    ∀ β : ℕ → ℂ,
      (∀ d, 0 < d →
        (modelPolynomial d).IsRoot (β d) ∧
          ∀ γ : ℂ, (modelPolynomial d).IsRoot γ →
            ‖γ‖ ≤ ‖β d‖) →
      (fun d => ‖β d + (1 / 2 : ℝ)‖ - (d : ℝ) ^ 2 / Real.pi)
        =O[atTop] (fun _ : ℕ => (1 : ℝ))

/-- **Hibi's lower bound.** Let $P \subseteq \mathbb{R}^d$ be the lattice polytope spanned by a
finite set of points of $\mathbb{Z}^d$, and suppose that $P$ is full-dimensional. Let $E$ be a
complex polynomial with $E(k) = |kP \cap \mathbb{Z}^d|$ for every natural number $k$, and write
$h^*_i$ for the $h^*$-coefficients of $E$. If $h^*_d \ne 0$, then
$\operatorname{Re} h^*_1 \le \operatorname{Re} h^*_k$ for every $k$ with $1 \le k < d$.

The $h^*$-coefficients are defined as complex numbers, so the inequality compares real parts.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 5 (quoting Hibi's lower bound theorem).
-/
public theorem_wanted hibi_lower_bound {d : ℕ}
    (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ)
    (hfull : IsFullDimensional (latticePolytope vertices))
    (hcount : EhrhartCounts vertices E)
    (htop : hStarCoeff E d ≠ 0) :
    ∀ k, 1 ≤ k → k < d → (hStarCoeff E 1).re ≤ (hStarCoeff E k).re

/-- **The set of attainable canonical-line roots is connected.** For every positive integer $d$,
the set $\Omega_d$ of canonical-line roots of degree-$d$ CL-polynomials satisfying
$(\diamondsuit)$ is a nonempty connected subset of $\mathbb{C}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 6.
-/
public theorem_wanted canonicalLineRootSet_isConnected (d : ℕ) (hd : 0 < d) : IsConnected (canonicalLineRootSet d)

/-- **Parameter bound for SNN CL-polynomials.** Let $f$ be a complex polynomial of degree $d$
that is a CL-polynomial with real scale $a$ and list of real parameters $c_1, \dots, c_m$, and
suppose that $f$ is SNN. Then for each parameter $c_k$ there is a real number $\beta$ such that
$-\tfrac12 + \beta i$ is a root of the symmetric basis polynomial $p^d_0$ and
$c_k \le \tfrac14 + \beta^2$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 7 (restatement of Theorem 4).
-/
public theorem_wanted cl_parameter_bounded_by_pBasis_root (f : Polynomial ℂ) (a : ℝ)
    (cs : List ℝ) (d : ℕ) (hdeg : f.natDegree = d)
    (hcl : IsCLWithParameters f a cs) (hsnn : IsSNN f) :
    ∀ c ∈ cs, ∃ β : ℝ,
      (pBasis d 0).IsRoot (-(1 / 2 : ℝ) + (β : ℂ) * Complex.I) ∧
        c ≤ 1 / 4 + β ^ 2

/-- **CL-span.** The CL-span of a complex polynomial $f$ is the convex hull, in $\mathbb{C}$
viewed as a real vector space, of the set of roots of $f$ lying on the canonical line, the line
of complex numbers with real part $-1/2$. Here the zero polynomial is regarded as having no
roots, so its CL-span is empty.

When nonempty, the CL-span is an interval of the canonical line.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Section 2 (definition of `clspan`).
-/
public def clspan (f : Polynomial ℂ) : Set ℂ :=
  convexHull ℝ {z | z ∈ f.roots ∧ z ∈ canonicalLine}

/-- The zero polynomial has empty CL-span (its root multiset is empty).
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Section 2 (definition of `clspan`).
-/
public theorem clspan_zero : clspan 0 = ∅ := by
  simp [clspan]

/-- **Vertices of the standard reflexive simplex.** For a natural number $d$, this is the finite
set of integer points $\{e_1, \dots, e_d, (-1, \dots, -1)\} \subseteq \mathbb{Z}^d$, where
$e_1, \dots, e_d$ are the standard basis vectors of $\mathbb{Z}^d$, so that
$(-1, \dots, -1) = -(e_1 + \dots + e_d)$. These points are the vertices of the standard
reflexive simplex $\Delta^d_{\mathrm{sr}}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Section 2.2 (definition of `Δᵈ_sr`).
-/
public def standardReflexiveSimplexVertices (d : ℕ) : Finset (Fin d → ℤ) :=
  insert (fun _ => -1) (Finset.univ.image fun i : Fin d => Pi.single i 1)

/-- **The all-minus-one vector is a vertex of the standard reflexive simplex.** For every natural
number $d$, let $e_1, \dots, e_d$ be the standard basis vectors of $\mathbb{Z}^d$. Then the
point $-(e_1 + \dots + e_d) = (-1, \dots, -1)$ belongs to the vertex set
$\{e_1, \dots, e_d, -(e_1 + \dots + e_d)\}$ of the standard reflexive simplex $\Delta^d_{sr}$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Section 2.2 (definition of `Δᵈ_sr`).
-/
public theorem neg_one_mem_standardReflexiveSimplexVertices (d : ℕ) :
    (fun _ => -1) ∈ standardReflexiveSimplexVertices d := by
  simp [standardReflexiveSimplexVertices]

/-- **The symmetric basis polynomials on the canonical line.** Let $d \ge 1$ and $j$ be natural
numbers with $2j \le d$, let $p^d_j$ be the symmetric basis polynomial, and let $i$ be the
imaginary unit. Then:
(a) the real part of $p^d_j(it - \tfrac12) / i^d$ tends to $+\infty$ as the real number $t$
tends to $+\infty$;
(b) if $2j \ne d$, then for every real $t$ we have $p^d_j(it - \tfrac12) = 0$ if and only if
there is a real number $r$ with
$\prod_{k=0}^{d-2j-1} \bigl(it - \tfrac12 + (d - j) - k\bigr) = r \, i^{d-2j+1}$, that is,
the falling factorial $(it - \tfrac12 + d - j)_{d-2j}$ lies in $\mathbb{R} \, i^{d-2j+1}$;
(c) if $j \ge 1$, then the CL-span of $p^d_j$ is contained in the CL-span of $p^d_{j-1}$.

The values in (a) are real by Remark 1 of the paper. The paper also allows $d = 0$, where (a)
fails because $p^0_0 = 1$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 3.
-/
public theorem_wanted pBasis_canonicalLine_properties (d j : ℕ) (hd : 0 < d) (hj : 2 * j ≤ d) :
    Tendsto (fun t : ℝ =>
        ((pBasis d j).eval ((t : ℂ) * Complex.I - 1 / 2) / Complex.I ^ d).re) atTop atTop ∧
    (2 * j ≠ d → ∀ t : ℝ, (pBasis d j).eval ((t : ℂ) * Complex.I - 1 / 2) = 0 ↔
      ∃ r : ℝ, ∏ i ∈ Finset.range (d - 2 * j),
          ((t : ℂ) * Complex.I - 1 / 2 + ((d - j : ℕ) : ℂ) - (i : ℂ)) =
        (r : ℂ) * Complex.I ^ (d - 2 * j + 1)) ∧
    (0 < j → clspan (pBasis d j) ⊆ clspan (pBasis d (j - 1)))

/-- **CL-span bound for SNN CL-polynomials.** Let $f$ be a complex polynomial of degree $d$ that
is both a CL-polynomial and an SNN polynomial. Then the CL-span of $f$ is contained in the
CL-span of the symmetric basis polynomial $p^d_0$.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 4.
-/
public theorem_wanted clspan_subset_clspan_pBasis_zero (f : Polynomial ℂ) (hcl : IsCL f)
    (hsnn : IsSNN f) : clspan f ⊆ clspan (pBasis f.natDegree 0)

/-- **Ehrhart CL-spans of reflexive polytopes in dimension at most 9.** Let $d \le 9$, let
$P \subseteq \mathbb{R}^d$ be the convex hull of a finite set of integer points, and suppose
that $P$ is reflexive. Let $\Delta^d_{sr}$ be the standard reflexive simplex, with vertices
$e_1, \dots, e_d$ and $-(e_1 + \cdots + e_d)$. Let $E$ and $E'$ be complex polynomials such
that, for every natural number $k$, $E(k)$ is the number of integer points of $kP$ and $E'(k)$
is the number of integer points of $k\Delta^d_{sr}$. Then
$\operatorname{clspan} E \subseteq \operatorname{clspan} E'$.

Reflexivity is Hibi's interior-point characterization, up to a lattice translation, which does
not change the Ehrhart polynomial.

Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 4.
-/
public theorem_wanted clspan_ehrhart_subset_standardReflexiveSimplex {d : ℕ} (hd : d ≤ 9)
    (vertices : Finset (Fin d → ℤ)) (hP : IsReflexive (latticePolytope vertices)) (E E' : Polynomial ℂ)
    (hE : EhrhartCounts vertices E) (hE' : EhrhartCounts (standardReflexiveSimplexVertices d) E') :
    clspan E ⊆ clspan E'

end

end MetaMathlibExt
