/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

@[expose] public section

/-!
# Fogarty smoothness for the Hilbert scheme of surface points

The general Hilbert representative is explicit input. The remaining
surface-specific theorem is smoothness and pure dimension 2n.
No duplicate general Hilbert/Quot representability is requested.

Source: J. Fogarty, Algebraic Families on an Algebraic Surface,
Amer. J. Math. 90 (1968), 511--521, Theorem 2.4.
https://doi.org/10.2307/2373541
-/

namespace WantedExt.AlgebraicGeometry.SurfaceHilbertSmoothness

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

universe u

/-- **Fogarty's smoothness of Hilbert schemes of points on a surface.** Let $k$ be an algebraically
closed field of characteristic zero and $X$ a projective, geometrically irreducible $k$-scheme that
is proper and smooth of relative dimension two over $k$. For every $n$, any proper $k$-scheme $H$
with a universal family of length-$n$ closed subschemes of $X$ (`HilbertPointsModel X n`) is smooth
of relative dimension $2n$ over $k$. -/
public theorem_wanted hilbertPoints_smooth
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsProper X.hom]
    [SmoothOfRelativeDimension 2 X.hom] [GeometricallyIrreducible X.hom]
    (hproj : IsProjective X) (n : ℕ) (M : HilbertPointsModel X n) :
    SmoothOfRelativeDimension (2 * n) M.H.hom

end WantedExt.AlgebraicGeometry.SurfaceHilbertSmoothness
