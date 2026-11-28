/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeGeneralLinearSchemeCoordinates
public import MathlibExt.AlgebraicGeometry.RelativeWittIndRealizations
public import MathlibExt.AlgebraicGeometry.RelativeWittLoopCorrespondences

/-!
# Original general-linear Witt loops and their lattice orbit comparison

Positive loops and loops evaluate the determinant-localized native
general linear scheme on the original ramified Witt rings. The matrix
of a loop is obtained from the normalized all-algebra point dictionary.
Its lattice is the actual native matrix image of the standard lattice.

The quotient comparison is an isomorphism from the actual fpqc right
action quotient to the actual lattice sheaf. Its square fixes the map on
every original loop before and after sheafification. This forbids an
unrelated orbit-to-lattice assignment or a merely named Grassmannian.

Source: Zhu, arXiv:1407.8519v3, Lemma 1.3 and Section 1.2.1,
pp. 8--9; all original Witt scalar maps are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits

open _root_.CategoryTheory _root_.AlgebraicGeometry
open RelativeWittLoopTests RelativeWittLatticeModels RelativeWittIndRealizations
open NativeGeneralLinearSchemeCoordinates

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
  (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B) (n : ℕ)

/-- Integral coefficient algebras use the exact original right tensor map. -/
def integralAlgebra (R : PerfectAlgebra p k) : CommAlgCat B :=
  letI : Algebra B (Integral p k B R) := (coefficient p k B R).toAlgebra
  CommAlgCat.of B (Integral p k B R)

/-- Rational coefficient algebras use that same map after actual localization. -/
def rationalAlgebra (R : PerfectAlgebra p k) : CommAlgCat B :=
  letI : Algebra B (Rational p k B pi R) :=
    ((algebraMap (Integral p k B R) (Rational p k B pi R)).comp
      (coefficient p k B R)).toAlgebra
  CommAlgCat.of B (Rational p k B pi R)

variable (P : PointRealization B n)

/-- Actual positive-loop points of the fixed native general linear scheme. -/
abbrev PositivePoints (R : PerfectAlgebra p k) :=
  letI := P.group
  (positiveLoops p k B (scheme B n)).obj R

/-- Actual localized-loop points of the same scheme and coefficient tests. -/
abbrev LoopPoints (R : PerfectAlgebra p k) :=
  letI := P.group
  (loops p k B pi (scheme B n)).obj R

/-- A positive loop's matrix is evaluated on its original integral test algebra. -/
def positiveMatrix (R : PerfectAlgebra p k) (g : PositivePoints p k B n P R) :
    GL (Fin n) (Integral p k B R) :=
  (P.points.hom.app (integralAlgebra p k B R)).hom g

/-- A loop's matrix is evaluated on its original localized test algebra. -/
def loopMatrix (R : PerfectAlgebra p k) (g : LoopPoints p k B pi n P R) :
    GL (Fin n) (Rational p k B pi R) :=
  (P.points.hom.app (rationalAlgebra p k B pi R)).hom g

/-- The original loop presheaf, lifted only to the native sheaf universe. -/
abbrev loopPresheaf : PerfectAlgebra p k ⥤ Type 1 :=
  letI := P.group
  RelativeWittLoopCorrespondences.loopSets p k B pi (scheme B n)

/-- The actual presheaf right quotient by the original positive-loop action. -/
abbrev quotientPresheaf : PerfectAlgebra p k ⥤ Type 1 :=
  letI := P.group
  RelativeWittLoopCorrespondences.grassmannianPresheaf p k B pi (scheme B n)

/-- The fixed coequalizer map on every original general-linear loop. -/
def quotientMap : loopPresheaf p k B pi n P ⟶ quotientPresheaf p k B pi n P :=
  letI := P.group
  RelativeWittLoopCorrespondences.quotient p k B pi (scheme B n)

/-- The genuine fpqc loop quotient, independent of any geometric model. -/
abbrev quotientSheaf :=
  letI := P.group
  RelativeWittLoopCorrespondences.grassmannian p k B pi (scheme B n)

variable (D : ScalarExtension p k B pi n) (A : MatrixAction p k B pi n D)

/-- The prescribed loop lattice is the original matrix-translated standard lattice. -/
def loopLattice (R : PerfectAlgebra p k) (g : LoopPoints p k B pi n P R) :
    RelativeWittLatticeModels.Lattice p k B pi R n :=
  A.act R (loopMatrix p k B pi n P R g) (A.standard R)

/-- A natural orbit map is fixed on every loop by its actual standard-lattice image. -/
structure OrbitCoordinates where
  map : loopPresheaf p k B pi n P ⟶ D.functor
  normalized : ∀ (R : PerfectAlgebra p k) (g : (loopPresheaf p k B pi n P).obj R),
    (map.app R g).down = loopLattice p k B pi n P D A R g.down

/-- The quotient comparison retains the exact prequotient orbit square. -/
structure QuotientComparison (C : OrbitCoordinates p k B pi n P D A) where
  comparison : quotientSheaf p k B pi n P ≅ latticeSheaf p k B pi n D
  normalized :
    (sheafification p k).map (quotientMap p k B pi n P) ≫ comparison.hom =
      (sheafification p k).map C.map

end MathlibExt.AlgebraicGeometry.RelativeWittGeneralLinearOrbits
