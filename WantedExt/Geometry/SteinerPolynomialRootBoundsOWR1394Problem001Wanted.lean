/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Roots of Steiner polynomials and in- and circumradius (Oberwolfach Reports 56/2006)

Oberwolfach workshop Konvexgeometrie (2006), Conjecture 1 (M. A. Hernández Cifre, with M. Henk): for
a convex body `K ⊆ ℝⁿ` with inradius `r` and circumradius `R`, the real parts `a₁ ≤ ⋯ ≤ aₙ` of the
roots of the Steiner polynomial of `K` satisfy `a₁ ≤ -R ≤ -r ≤ aₙ ≤ 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.RingTheory.SimpleRing.Principal
public import MathlibExt.Geometry.Convex.Covering

@[expose] public section

namespace MathlibExt.Geometry.SteinerPolynomialRootBoundsOWR1394Problem001Wanted

/-!
Source: M. A. Hernández Cifre (with M. Henk), in Konvexgeometrie, Oberwolfach Reports 3 (2006), no.
56, p. 3328, Conjecture 1, DOI 10.4171/OWR/2006/56. UnsolvedMath record UM-30000626
(`OWR-1394-001`), dataset ulamai/UnsolvedMath v1.8.0.

A convex body is a compact convex set with nonempty interior (MathlibExt's
`ConvexCovering.IsConvexBody`). The Steiner polynomial is any real polynomial `f` with `f(λ) = vol(K
+ λ Bⁿ)` for `λ ≥ 0` (Steiner's formula; `f` is unique). The chain is read on the multiset of
complex roots: some root has real part `≤ -R`, some root has real part `≥ -r`, and all real parts
are `≤ 0`. `n ≥ 1` (for `n = 0` the polynomial is constant).
-/

open MeasureTheory Pointwise
open ConvexCovering (IsConvexBody)

/-- The inradius of `K`: the supremum of the radii of the closed balls contained in `K`. -/
noncomputable def inradius {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup {r : ℝ | ∃ c, Metric.closedBall c r ⊆ K}

/-- The circumradius of `K`: the infimum of the radii of the closed balls containing `K`. -/
noncomputable def circumradius {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf {R : ℝ | ∃ c, K ⊆ Metric.closedBall c R}

/-- `f` is the Steiner polynomial of `K`: `f(λ) = vol(K + λ Bⁿ)` for every `λ ≥ 0`, where `Bⁿ` is
the closed Euclidean unit ball (Steiner's formula; `f` is unique). -/
def IsSteinerPolynomial {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (f : Polynomial ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    f.eval t = (volume (K + t • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- The conjecture of Teissier type for Steiner polynomials (Oberwolfach Report 56/2006, p. 3328,
Conjecture 1): for every convex body `K ⊆ ℝⁿ` (`n ≥ 1`; compact, convex, nonempty interior, as
MathlibExt's `ConvexCovering.IsConvexBody`) with inradius `r` and circumradius `R`, the real parts
`a₁ ≤ ⋯ ≤ aₙ` of the (complex) roots of its Steiner polynomial satisfy `a₁ ≤ -R ≤ -r ≤ aₙ ≤ 0`:
some root has real part at most `-R`, some root has real part at least `-r`, and every root has
nonpositive real part. -/
def steinerRootBounds : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
    ∀ f : Polynomial ℝ, IsSteinerPolynomial K f →
      (∃ z ∈ (f.map (algebraMap ℝ ℂ)).roots, z.re ≤ -circumradius K) ∧
        (∃ z ∈ (f.map (algebraMap ℝ ℂ)).roots, -inradius K ≤ z.re) ∧
        ∀ z ∈ (f.map (algebraMap ℝ ℂ)).roots, z.re ≤ 0

/--
Resolved false: Henk and Hernández Cifre (Theorem 1.3) constructed a three-dimensional convex body
with nonempty interior (a planar lens plus a small ball) whose Steiner polynomial has all roots with
real part greater than `-R`, violating `a₁ ≤ -R`; their Theorem 1.2 also gives a body in `ℝ^15` with
a root of positive real part. Source: M. A. Hernández Cifre (with M. Henk), in Konvexgeometrie,
Oberwolfach Reports 3 (2006), no. 56, p. 3328, Conjecture 1, DOI 10.4171/OWR/2006/56; resolution: M.
Henk and M. A. Hernández Cifre, Notes on the roots of Steiner polynomials, Rev. Mat. Iberoam. 24
(2008), 631-644, arXiv:math/0703373, Theorem 1.3: there is K ∈ K³ (the body L + νB³, L a planar
lens, ν > 0) such that all real parts of the roots of f(K, B³, s) are greater than -R(K; B³);
Theorem 1.2: a 2-tangential body in ℝ^15 whose Steiner polynomial has a root with positive real
part, https://arxiv.org/abs/math/0703373.
-/
public theorem_wanted steinerRootBounds_refuted : ¬ steinerRootBounds

end MathlibExt.Geometry.SteinerPolynomialRootBoundsOWR1394Problem001Wanted
