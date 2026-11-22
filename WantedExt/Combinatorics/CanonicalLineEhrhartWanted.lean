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

/-- The canonical line is the vertical line of complex numbers with real part `-1 / 2`.
This is the paper's `CL`, represented as a set rather than as an affine subspace.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Definition of `CL`.
-/
public def canonicalLine : Set ℂ := {z | z.re = -(1 / 2 : ℝ)}

/-- `hStarCoeff f i` is the coefficient of `t^i` in
`(1 - t)^(d+1) * ∑ k, f(k) t^k`, where `d = f.natDegree`.  It is encoded directly
by the finite alternating sum requested in the task; natural-number arguments of `f` are
cast to `ℂ`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of the `h*`-polynomial.
-/
public def hStarCoeff (f : Polynomial ℂ) (i : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (i + 1),
    (-1 : ℂ) ^ j * (Nat.choose (f.natDegree + 1) j : ℂ) * f.eval (i - j : ℂ)

/-- An SNN polynomial is nonzero and every `h*` coefficient through its degree is real and
nonnegative.  Coefficients beyond the degree, which the generating-series identity makes zero,
are deliberately omitted so the definition does not depend on proving that identity here.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of SNN-polynomial.
-/
public def IsSNN (f : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧ ∀ i ≤ f.natDegree, 0 ≤ (hStarCoeff f i).re ∧ (hStarCoeff f i).im = 0

/-- The monic product of the quadratic canonical-line factors with parameters `cs`.  Real
parameters are mapped to complex constants, and the empty list gives the unit polynomial.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, factored definition of CL-polynomials.
-/
public def clQuadraticProduct (cs : List ℝ) : Polynomial ℂ :=
  (cs.map fun c => X ^ 2 + X + C (c : ℂ)).prod

/-- `IsCLWithParameters f a cs` records the paper's factorization of a CL-polynomial, including
`a ≠ 0`, the bounds `c ≥ 1/4`, the parity-dependent linear factor, and exactly `⌊d/2⌋`
quadratic factors.  A list is used so later statements can refer to individual parameters.
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

/-- A polynomial is a CL-polynomial when it has some real nonzero scale and parameter list
satisfying `IsCLWithParameters`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of CL-polynomial.
-/
public def IsCL (f : Polynomial ℂ) : Prop := ∃ a cs, IsCLWithParameters f a cs

/-- `bBasis d j` is `∏_{i=0}^{d-1} (X + d - j - i)`.  Integer constants are used before
mapping to `ℂ`, avoiding any convention about rising versus falling Pochhammer symbols.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `bᵈⱼ`.
-/
public def bBasis (d j : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range d, (X + C (((d : ℤ) - (j : ℤ) - (i : ℤ) : ℤ) : ℂ))

/-- `pBasis d j` is the symmetric sum `bᵈⱼ + bᵈ_{d-j}`, except that the middle term is
not doubled when `2j = d`.  Statements using it impose `j ≤ d`, so truncated subtraction does
not alter the paper's index.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `pᵈⱼ`.
-/
public def pBasis (d j : ℕ) : Polynomial ℂ :=
  if 2 * j = d then bBasis d j else bBasis d j + bBasis d (d - j)

/-- The first symmetric basis polynomial is `p¹₀ = 2X + 1`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, characteristic case of the `pᵈⱼ` definition.
-/
public theorem pBasis_one_zero : pBasis 1 0 = 2 * X + 1 := by
  simp [pBasis, bBasis]
  ring

/-- The second symmetric basis polynomial is `p²₀ = 2(X² + X + 1)`.
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

/-- `ListInterlaces r as bs` expresses the alternating inequalities
`b₁ r a₁ r b₂ r ⋯ r a_d r b_{d+1}`.  Its shape forces the second list to contain exactly
one more entry than the first.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of interlacing.
-/
public def ListInterlaces {α : Type*} (r : α → α → Prop) : List α → List α → Prop
  | [], [_] => True
  | a :: as, b :: b' :: bs => r b a ∧ r a b' ∧ ListInterlaces r as (b' :: bs)
  | _, _ => False

/-- `ListAlternates r as bs` is one orientation of alternating inequalities for equal-length
lists.  It is used only for the same-degree clauses in Fisk's Leibniz rule, since the paper's
terminology also calls those lists interlacing while its displayed definition reserves
`interlaces` for degrees differing by one.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 2 (quoting Fisk, Lemma 1.26).
-/
public def ListAlternates {α : Type*} (r : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | [a], [b] => r a b
  | a :: a' :: as, b :: bs => r a b ∧ r b a' ∧ ListAlternates r (a' :: as) bs
  | _, _ => False

/-- `RealInterlaces f g` uses ordered lists whose multisets are exactly the roots of `f` and
`g`, hence retain multiplicity.  Nonzeroness, root-cardinality, and degree conditions ensure
that `f` has degree `d`, `g` has degree `d+1`, and both split over `ℝ`; the final clause is the
paper's alternating order.
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

/-- `RealAlternates f g` is the unordered-orientation, equal-degree analogue needed for two
clauses of Fisk's Leibniz rule.  The root lists are complete, sorted, and counted with
multiplicity; either alternating orientation is accepted.
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

/-- `CLInterlaces f g` is real interlacing transported to the canonical line: complete root
lists (with multiplicity) lie on `canonicalLine`, are ordered by imaginary part, and alternate.
Explicit nonzero, degree, and cardinality conditions prevent vacuous zero-polynomial cases.
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

/-- A nonzero real polynomial has only real roots when its root multiset over `ℝ` has cardinality
equal to its degree.  This cardinality formulation includes multiplicity.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 2 (quoting Fisk, Lemma 1.26).
-/
public def HasOnlyRealRoots (f : Polynomial ℝ) : Prop :=
  f ≠ 0 ∧ f.roots.card = f.natDegree

/-- The real point associated to an integer lattice point in `ℤ^d`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of a lattice polytope.
-/
public def latticePointToReal {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ := fun i => x i

/-- The lattice polytope generated by a finite set of integer points is its real convex hull.
Using a `Finset` builds finiteness and integrality into the data.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of a lattice polytope.
-/
public def latticePolytope {d : ℕ} (vertices : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  convexHull ℝ (latticePointToReal '' (vertices : Set (Fin d → ℤ)))

/-- A subset of `ℝ^d` is full-dimensional when it is nonempty and the direction of its affine
span is `⊤`. This is the formal counterpart of dimension `d`; nonemptiness excludes the empty
subset of `ℝ^0`, whose affine-span direction `⊥` equals `⊤`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, full-dimensional lattice-polytope convention.
-/
public def IsFullDimensional {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  P.Nonempty ∧ (affineSpan ℝ P).direction = ⊤

/-- `EhrhartCounts vertices E` says that for every `k`, `E(k)` is the ordinary Ehrhart count
`|kP ∩ ℤ^d|` of the lattice polytope `P`, using the canonical `ordinaryEhrhartCount` on the
rational points of `P` (a lattice point lies in `kP` exactly when it is `k` times a rational
point of `P`).  This is a hypothesis rather than an appeal to an unavailable formal Ehrhart
theorem; that theorem supplies existence and uniqueness on paper.  The counting polynomial is
consistently represented over `ℂ`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of the Ehrhart polynomial.
-/
public def EhrhartCounts {d : ℕ} (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ) : Prop :=
  ∀ k : ℕ, E.eval (k : ℂ) =
    (ordinaryEhrhartCount d
      {x : Fin d → ℚ | (fun i => (x i : ℝ)) ∈ latticePolytope vertices} k : ℂ)

/-- The binomial polynomial `C(X+n,d)` over `ℝ`, defined as a normalized finite product of
linear factors.  This fixes the orientation independently of Mathlib's Pochhammer conventions.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 7.
-/
public def binomialPolynomial (n : ℤ) (d : ℕ) : Polynomial ℝ :=
  ((d.factorial : ℝ)⁻¹) •
    ∏ i ∈ Finset.range d, (X + C ((n - (i : ℤ) : ℤ) : ℝ))

/-- The complex binomial polynomial `C(X+n,d)`, used for the asymptotic root statement.
It is defined separately from the real version to keep all Ehrhart root assertions over `ℂ`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 3 (quoting Braun and Develin, Theorem 2.3).
-/
public def complexBinomialPolynomial (n : ℤ) (d : ℕ) : Polynomial ℂ :=
  ((d.factorial : ℂ)⁻¹) •
    ∏ i ∈ Finset.range d, (X + C ((n - (i : ℤ) : ℤ) : ℂ))

/-- `modelPolynomial d` is `C(X+d,d) + C(X,d)`, without the harmless factor `d!` in
`pBasis d 0`; the paper emphasizes that it need not be an Ehrhart polynomial.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 3 (quoting Braun and Develin, Theorem 2.3).
-/
public def modelPolynomial (d : ℕ) : Polynomial ℂ :=
  complexBinomialPolynomial d d + complexBinomialPolynomial 0 d

/-- Property `(♢)` means that the `h*` coefficients through the degree are real,
nonnegative, and palindromic.  Nonzeroness is explicit; for CL-polynomials the paper notes
that palindromicity is automatic, but it is retained here as part of the named property.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `(♢)`.
-/
public def HasDiamond (f : Polynomial ℂ) : Prop :=
  f ≠ 0 ∧
    (∀ i ≤ f.natDegree, hStarCoeff f i = hStarCoeff f (f.natDegree - i)) ∧
    ∀ i ≤ f.natDegree, 0 ≤ (hStarCoeff f i).re ∧ (hStarCoeff f i).im = 0

/-- `canonicalLineRootSet d` is the set of canonical-line roots attained by degree-`d` CL-polynomials
satisfying `(♢)`.  Root membership is stated with `Polynomial.IsRoot` and is therefore not
set-theoretically vacuous.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, definition of `Ω_d`.
-/
public def canonicalLineRootSet (d : ℕ) : Set ℂ :=
  {z | z ∈ canonicalLine ∧
    ∃ f : Polynomial ℂ, f.natDegree = d ∧ IsCL f ∧ HasDiamond f ∧ f.IsRoot z}

/-- The functional equation `f(X-1) = (-1)^d f(-X)` is equivalent to palindromicity of
the finite `h*` coefficient vector.  Here `d` is `f.natDegree`; `f ≠ 0` is explicit because
the degree of the zero polynomial is not mathematically defined.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 1 (quoting Corollary 2.2 in Kölbl's [11]).
-/
public theorem_wanted functionalEquation_iff_hStar_palindromic (f : Polynomial ℂ) (hf : f ≠ 0) :
    f.comp (X - 1) = C ((-1 : ℂ) ^ f.natDegree) * f.comp (-X) ↔
      ∀ i ≤ f.natDegree, hStarCoeff f i = hStarCoeff f (f.natDegree - i)

/-- A degree-`d` CL-polynomial takes every canonical-line argument into `ℝ · i^d`.
Membership in that one-dimensional real subspace is represented by the witness `r : ℝ`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 2.
-/
public theorem_wanted cl_value_on_canonicalLine (f : Polynomial ℂ) (hf : IsCL f)
    (z : ℂ) (hz : z ∈ canonicalLine) :
    ∃ r : ℝ, f.eval z = (r : ℂ) * Complex.I ^ f.natDegree

/-- For every positive `d`, `pᵈ₀` CL-interlaces `pᵈ⁺¹₀`, with multiplicities and
degree/cardinality conditions supplied by `CLInterlaces`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 4.
-/
public theorem_wanted pBasis_zero_interlaces_succ (d : ℕ) (hd : 0 < d) :
    CLInterlaces (pBasis d 0) (pBasis (d + 1) 0)

/-- For positive `d` and `w`, `pᵈ₀` CL-interlaces
`pᵈ⁺¹₀ + w(2X+1)pᵈ₀`.  This follows the numbered INTEGERS statement's requested direction,
not the differently worded arXiv excerpt.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 5.
-/
public theorem_wanted pBasis_zero_interlaces_perturbation (d : ℕ) (hd : 0 < d)
    (w : ℝ) (hw : 0 < w) :
    CLInterlaces (pBasis d 0)
      (pBasis (d + 1) 0 + C (w : ℂ) * (2 * X + 1) * pBasis d 0)

/-- Multiplication by `2X+1` preserves the SNN property.  The paper's degree `d` is
`f.natDegree`, so no redundant degree parameter is introduced.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Lemma 6.
-/
public theorem_wanted two_mul_X_add_one_preserves_snn (f : Polynomial ℂ) (hf : IsSNN f) :
    IsSNN ((2 * X + 1) * f)

/-- Multiplication of `C(X+d-j,d)` by `X²+X+c` expands into the three displayed
degree-`d+2` binomial polynomials with coefficients `α`, `β`, and `γ`.  The hypotheses
`0 < d` and `j ≤ d` are retained.  The paper's `c ≥ 1/4` is deliberately dropped because
this is a polynomial identity for every real `c`, a strengthening checked exactly in the
requested small cases.
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

/-- Fisk's Leibniz rule for positive-leading, real-rooted `f`, `f₁`, `g`, `g₁` with
no common root of `f` and `g`.  The first two conclusions use strict degree-compatible
`RealInterlaces`; comparisons with `f*g₁` and `f₁*g`, which have the same degree as the
Leibniz sum, use the explicit equal-degree `RealAlternates`.  The final real-rootedness
clause is kept explicit as requested.
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

/-- Coefficientwise limits preserve real interlacing.  Convergence is `Tendsto` of every
coefficient at `atTop`; the limits `f`, `g` are nonzero and degrees are required eventually to
equal the limiting degrees (fixed degrees), and each approximating pair has the strict
orientation `fₙ` interlaces `gₙ`.
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

/-- A sorted degree-`d` CL factorization is SNN when parameter number `k` is at most
`2k+2` for odd `d` and at most `2k+1` for even `d`, in addition to the `1/4` lower bound
already carried by `IsCLWithParameters`, and the scale `a` is positive (for `a < 0` the claim
fails: `d = 1`, `a = -1`, `cs = []`, `f = -(2X + 1)` has `h*_0 = -1`).  Zero-based list
indexing matches `c₀,c₁,…`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 5.
-/
public theorem_wanted sorted_cl_parameters_are_snn (f : Polynomial ℂ) (a : ℝ) (cs : List ℝ)
    (d : ℕ) (hdeg : f.natDegree = d) (ha : 0 < a) (hcl : IsCLWithParameters f a cs)
    (hsorted : List.Pairwise (· ≤ ·) cs)
    (hupper : ∀ (k : ℕ) (c : ℝ), cs[k]? = some c →
      if Odd d then c ≤ 2 * (k : ℝ) + 2 else c ≤ 2 * (k : ℝ) + 1) :
    IsSNN f

/-- Ehrhart roots of a full-dimensional lattice polytope satisfy both classical bounds:
every complex root has norm at most `1 + (d+1)!`, and every real root has real part in
`[-d, ⌊d/2⌋)`.  Realness is `α.im = 0`; the upper endpoint is intentionally strict.
`EhrhartCounts` replaces use of an unavailable formal Ehrhart theorem.
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

/-- Every root of a degree-`d` Ehrhart polynomial lies in the closed disc centered at
`-1/2` with radius `d(d-1/2)`.  The polytope and its point counts use the explicit finite
encoding, and full dimension records its dimension (`E` then has degree `d` by Ehrhart's theorem).
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 2 (quoting Braun, Theorem 1).
-/
public theorem_wanted ehrhart_roots_in_braun_disc {d : ℕ}
    (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ)
    (hfull : IsFullDimensional (latticePolytope vertices))
    (hcount : EhrhartCounts vertices E)
    (α : ℂ) (hroot : E.IsRoot α) :
    ‖α + (1 / 2 : ℝ)‖ ≤ (d : ℝ) * ((d : ℝ) - 1 / 2)

/-- For every choice `β d` of a maximal-norm root of
`M_d = C(X+d,d)+C(X,d)` in positive degree, the difference
`|β_d+1/2| - d²/π` is `O(1)` at infinity.  Positivity is restricted to the root-selection
hypothesis because `M_0` is constant; this does not change an `atTop` asymptotic statement.
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

/-- Hibi's lower bound says `h*₁ ≤ h*ₖ` for `1 ≤ k < d` when the top coefficient
is nonzero.  Since `hStarCoeff` is complex-valued, the order compares real parts; the
Ehrhart counting hypothesis is the formal source of real coefficients.  The strict `k < d`
range is retained rather than broadening the excerpt's wording.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 5 (quoting Hibi's lower bound theorem).
-/
public theorem_wanted hibi_lower_bound {d : ℕ}
    (vertices : Finset (Fin d → ℤ)) (E : Polynomial ℂ)
    (hfull : IsFullDimensional (latticePolytope vertices))
    (hcount : EhrhartCounts vertices E)
    (htop : hStarCoeff E d ≠ 0) :
    ∀ k, 1 ≤ k → k < d → (hStarCoeff E 1).re ≤ (hStarCoeff E k).re

/-- For every positive dimension, the attainable-root set `canonicalLineRootSet d` is connected.
`IsConnected`, rather than only `IsPreconnected`, formalizes the paper's nonempty connected
set and thus also records attainability of at least one root.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 6.
-/
public theorem_wanted canonicalLineRootSet_isConnected (d : ℕ) (hd : 0 < d) : IsConnected (canonicalLineRootSet d)

/-- If a degree-`d` CL-polynomial is SNN, each factor parameter `c` is bounded by
`1/4+β²` for a root `-1/2+βi` of `pᵈ₀`.  This directly quantifies the witnessing extremal
root instead of defining a potentially problematic maximum; it is the task's requested
equivalent reading of `c ≤ mᵈ₀`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 7 (restatement of Theorem 4).
-/
public theorem_wanted cl_parameter_bounded_by_pBasis_root (f : Polynomial ℂ) (a : ℝ)
    (cs : List ℝ) (d : ℕ) (hdeg : f.natDegree = d)
    (hcl : IsCLWithParameters f a cs) (hsnn : IsSNN f) :
    ∀ c ∈ cs, ∃ β : ℝ,
      (pBasis d 0).IsRoot (-(1 / 2 : ℝ) + (β : ℂ) * Complex.I) ∧
        c ≤ 1 / 4 + β ^ 2

/-- The CL-span of a polynomial: the convex hull (in `ℂ` as a real vector space) of its roots
lying on the canonical line; an interval of `CL` when nonempty.
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

/-- Vertices `e₁, …, e_d, -∑ eₖ` of the standard reflexive simplex `Δᵈ_sr`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Section 2.2 (definition of `Δᵈ_sr`).
-/
public def standardReflexiveSimplexVertices (d : ℕ) : Finset (Fin d → ℤ) :=
  insert (fun _ => -1) (Finset.univ.image fun i : Fin d => Pi.single i 1)

/-- `-∑ eₖ = (-1, …, -1)` is a vertex of `Δᵈ_sr`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Section 2.2 (definition of `Δᵈ_sr`).
-/
public theorem neg_one_mem_standardReflexiveSimplexVertices (d : ℕ) :
    (fun _ => -1) ∈ standardReflexiveSimplexVertices d := by
  simp [standardReflexiveSimplexVertices]

/-- Lemma 3 for `d > 0` and `2j ≤ d`: (a) `pᵈⱼ(it - 1/2) i⁻ᵈ → ∞` as `t → ∞` (real part; the
values are real by Remark 1); (b) for `2j ≠ d`, `pᵈⱼ(it - 1/2) = 0` iff
`(it - 1/2 + d - j)_{d-2j} ∈ ℝ i^{d-2j+1}` (falling factorial); (c) for `0 < j`,
`clspan pᵈⱼ ⊆ clspan pᵈⱼ₋₁`. The paper allows `d = 0`, where (a) fails (`p⁰₀ = 1`).
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

/-- For every degree-`d` polynomial `f ∈ 𝔆 ∩ 𝔖` (CL and SNN), `clspan f ⊆ clspan pᵈ₀`.
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Theorem 4.
-/
public theorem_wanted clspan_subset_clspan_pBasis_zero (f : Polynomial ℂ) (hcl : IsCL f)
    (hsnn : IsSNN f) : clspan f ⊆ clspan (pBasis f.natDegree 0)

/-- For every reflexive polytope `P` of dimension `d ≤ 9`, `clspan E_P ⊆ clspan E_{Δᵈ_sr}`.
Reflexivity is the existing `IsReflexive` (Hibi's interior-point characterization, up to a
lattice translation, which does not change the Ehrhart polynomial).
Source: Max Kölbl, *Properties of Ehrhart Polynomials Whose Roots Lie on the Canonical Line*,
INTEGERS 25 (2025), Article A68, Proposition 4.
-/
public theorem_wanted clspan_ehrhart_subset_standardReflexiveSimplex {d : ℕ} (hd : d ≤ 9)
    (vertices : Finset (Fin d → ℤ)) (hP : IsReflexive (latticePolytope vertices)) (E E' : Polynomial ℂ)
    (hE : EhrhartCounts vertices E) (hE' : EhrhartCounts (standardReflexiveSimplexVertices d) E') :
    clspan E ⊆ clspan E'

end

end MetaMathlibExt
