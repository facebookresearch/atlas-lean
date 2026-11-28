/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Regularity of rational functions at a point

This file defines regularity of a fraction-ring element relative to a ring-homomorphism
that evaluates denominators. It also specializes the definition to affine coordinate rings.
-/

@[expose] public section

namespace FractionRing

variable {A K : Type*} [CommRing A] [CommRing K]

/-- **Regularity of a fraction at an evaluation.** Let $A$ and $K$ be commutative rings and
$\mathrm{ev} : A \to K$ a ring homomorphism. An element $r$ of the total ring of fractions of
$A$ (its localization at the non-zero-divisors) is regular at $\mathrm{ev}$ when there is some
$g \in A$ with $\mathrm{ev}(g) \neq 0$ such that $g r$ lies in the image of $A$ in its total ring
of fractions. -/
def IsRegularAt (ev : A →+* K) (r : FractionRing A) : Prop :=
  ∃ g : A, ev g ≠ 0 ∧
    algebraMap A (FractionRing A) g * r ∈
      Set.range (algebraMap A (FractionRing A))

variable [Nontrivial K]

/-- **Elements of the base ring are regular.** Let $A$ be a commutative ring and $K$ a nontrivial
commutative ring. For every ring homomorphism $\mathrm{ev} : A \to K$ and every $a \in A$, the
image of $a$ in the total ring of fractions of $A$ is regular at $\mathrm{ev}$. -/
theorem isRegularAt_algebraMap (ev : A →+* K) (a : A) :
    IsRegularAt ev (algebraMap A (FractionRing A) a) := by
  refine ⟨1, by simp, ?_⟩
  simp

/-- **Zero is regular.** Let $A$ be a commutative ring and $K$ a nontrivial commutative ring.
For every ring homomorphism $\mathrm{ev} : A \to K$, the element $0$ of the total ring of fractions
of $A$ is regular at $\mathrm{ev}$. -/
theorem isRegularAt_zero (ev : A →+* K) : IsRegularAt ev 0 := by
  simpa only [map_zero] using isRegularAt_algebraMap ev 0

/-- **One is regular.** Let $A$ be a commutative ring and $K$ a nontrivial commutative ring.
For every ring homomorphism $\mathrm{ev} : A \to K$, the element $1$ of the total ring of fractions
of $A$ is regular at $\mathrm{ev}$. -/
theorem isRegularAt_one (ev : A →+* K) : IsRegularAt ev 1 := by
  simpa only [map_one] using isRegularAt_algebraMap ev 1

end FractionRing

namespace MvPolynomial

variable {K σ : Type*} [Field K]

/-- **Affine coordinate ring.** Let $K$ be a field, $\sigma$ an index set and
$X \subseteq K^\sigma$ a set of points. The affine coordinate ring of $X$ is the quotient
$K[x_i : i \in \sigma] / I(X)$ of the polynomial ring over $K$ in variables indexed by $\sigma$
by the vanishing ideal $I(X)$, the ideal of all polynomials that vanish at every point of $X$. -/
abbrev AffineCoordinateRing (X : Set (σ → K)) :=
  MvPolynomial σ K ⧸ vanishingIdeal K X

namespace AffineCoordinateRing

/-- **Evaluation at a point of an affine set.** Let $K$ be a field, $\sigma$ an index set and
$X \subseteq K^\sigma$ a set of points. For a point $P \in X$, evaluation at $P$ is the ring
homomorphism from the affine coordinate ring of $X$ to $K$ that sends the residue class of a
polynomial $f$ to $f(P)$; it is well defined because every polynomial in the vanishing ideal of
$X$ vanishes at $P$. -/
noncomputable def evalAt (X : Set (σ → K)) (P : X) : AffineCoordinateRing X →+* K :=
  Ideal.Quotient.lift _ (MvPolynomial.aeval (R := K) P.1)
    (fun _ hp ↦ (MvPolynomial.mem_vanishingIdeal_iff.mp hp) P.1 P.2)

/-- **Evaluating a residue class.** Let $K$ be a field, $\sigma$ an index set,
$X \subseteq K^\sigma$ a set of points and $P \in X$. For every polynomial $f$ over $K$ in
variables indexed by $\sigma$, evaluating the residue class of $f$ in the affine coordinate ring
of $X$ at $P$ gives $f(P)$. -/
@[simp]
theorem evalAt_mk (X : Set (σ → K)) (P : X) (f : MvPolynomial σ K) :
    evalAt X P (Ideal.Quotient.mk _ f) = MvPolynomial.aeval P.1 f :=
  Ideal.Quotient.lift_mk _ _ _

/-- **Regularity of a rational function at a point.** Let $K$ be a field, $\sigma$ an index set
and $X \subseteq K^\sigma$ a set of points whose affine coordinate ring $A$ is an integral domain.
A rational function on $X$ is an element $r$ of the field of fractions of $A$; it is regular at a
point $P \in X$ when there is some $g \in A$ whose value $g(P)$ under evaluation at $P$ is nonzero
such that $g r$ lies in the image of $A$ in its field of fractions. -/
def IsRegularAt (X : Set (σ → K)) [IsDomain (AffineCoordinateRing X)]
    (r : FractionRing (AffineCoordinateRing X)) (P : X) : Prop :=
  FractionRing.IsRegularAt (evalAt X P) r

/-- **Elements of the coordinate ring are regular.** Let $K$ be a field, $\sigma$ an index set and
$X \subseteq K^\sigma$ a set of points whose affine coordinate ring $A$ is an integral domain. For
every $a \in A$ and every point $P \in X$, the image of $a$ in the field of fractions of $A$ is a
rational function on $X$ that is regular at $P$. -/
theorem isRegularAt_algebraMap (X : Set (σ → K)) [IsDomain (AffineCoordinateRing X)]
    (a : AffineCoordinateRing X) (P : X) :
    IsRegularAt X (algebraMap (AffineCoordinateRing X)
      (FractionRing (AffineCoordinateRing X)) a) P :=
  FractionRing.isRegularAt_algebraMap (evalAt X P) a

end AffineCoordinateRing

end MvPolynomial
