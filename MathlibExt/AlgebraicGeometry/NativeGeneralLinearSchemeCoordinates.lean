/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Native coordinate scheme of the general linear group

The scheme is literally Spec of the polynomial matrix coordinate ring
with its determinant inverted. Its comparison target is the original
invertible-matrix group on every coefficient algebra, including the zero
algebra. A realization pins multiplication and all point maps on that
actual coordinate scheme; it does not choose another group carrier.

Reference: SGA 3, Expose I, the standard affine general linear group;
Zhu, arXiv:1407.8519v3, Section 1.2.1, p. 9, uses this group scheme.
The normalized native group and point dictionary is requested separately.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeGeneralLinearSchemeCoordinates

open _root_.CategoryTheory _root_.AlgebraicGeometry
open AlgebraicGroupPointRepresentations

variable (B : Type) [CommRing B] (n : ℕ)

/-- Every entry of the universal matrix is its actual polynomial coordinate. -/
def universalMatrix : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) B) :=
  fun i j ↦ MvPolynomial.X (i, j)

/-- The actual determinant-localized coordinate ring. -/
abbrev CoordinateRing := Localization.Away (Matrix.det (universalMatrix B n))

/-- The standard general linear scheme over the original coefficient ring. -/
def scheme : Over (Spec (.of B)) :=
  Over.mk (Spec.algebraMap B (CoordinateRing B n))

/-- Native realization on the fixed coordinate scheme and all algebra tests. The matrix of a point
is its ring map evaluated on the localised universal coordinates `X(i,j)`: a natural group
isomorphism alone would not pin the coordinates, since composing with inversion is natural. -/
structure PointRealization where
  [group : GrpObj (scheme B n)]
  points : groups B (scheme B n) ≅ linearGroups B n
  coordinates : ∀ (A : CommAlgCat.{0} B) (g : (testSchemes B).obj (Opposite.op A) ⟶ scheme B n)
    (i j : Fin n),
    ((show GL (Fin n) A from (points.hom.app A).hom g) : Matrix (Fin n) (Fin n) A) i j =
      (Spec.preimage g.left).hom
        (algebraMap (MvPolynomial (Fin n × Fin n) B) (CoordinateRing B n) (MvPolynomial.X (i, j)))

end MathlibExt.AlgebraicGeometry.NativeGeneralLinearSchemeCoordinates
