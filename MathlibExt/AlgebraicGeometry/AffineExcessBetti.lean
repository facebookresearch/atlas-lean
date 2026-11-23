/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.AffineExcessGeometry
public import MathlibExt.AlgebraicGeometry.BettiGysin
public import MathlibExt.AlgebraicGeometry.BettiCycleRealization
public import Mathlib.Algebra.Module.Projective
/-!
# A Betti excess-intersection boundary on concrete affine geometry

The square is the actual quotient base change of A → B and I ⊂ A. Its
conormal comparison, kernel, dual excess normal and symmetric-algebra normal
space are fixed in `AffineExcessGeometry`. The scope explicitly records the
smooth dimensions, finite projectivity and relative rank of that actual
normal bundle, including a nonempty base.

The Euler class is zero-section Gysin followed by pullback, using the same
selected purity family as the other proper cohomological Gysin maps. Thus
no Gysin map, excess bundle or top Chern class is an arbitrary operator field.
`ExcessFormula` is the excess formula on one square for a given purity
family, and `ExcessPurities` is a single family, chosen once, satisfying it on
every square, so that the Gysin maps on a scheme shared by two squares agree.
No existence or global instance is claimed here.

Reference: Fulton, *Intersection Theory*, Theorem 6.3 and §19.1; Stacks Tag
0FV9. The already implemented generic algebraic formula is credited in
`AffineExcessGeometry`; the requested bridge uses these actual Betti carriers.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffineExcessBetti
open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves BettiRealization CompactSupportBetti
open ProperBettiFunctoriality BettiFunctoriality BettiGysin AffineExcessGeometry
attribute [local instance] HasDerivedCategory.standard

section Square

variable (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  [Algebra A B] [IsScalarTower ℂ A B] (I : Ideal A)

/-- The base `B/J` of the excess normal bundle. -/
abbrev base (I : Ideal A) := B ⧸ extendedIdeal A B I

/-- The total space of the excess normal bundle over `Spec (B/J)`. -/
abbrev normalSpace := bundleSpace (base A B I) (excessNormal A B I)

/-- The smoothness, dimension and rank hypotheses on the square
`Spec (B/J) → Spec B`, `Spec (A/I) → Spec A`: the four schemes and the
excess normal space are smooth complex varieties of the displayed pure
dimensions (`A/I` has codimension `c' + e`, `B/J` has codimension `c'`), the
excess normal module is finite projective of rank `e`, the base is nonempty,
and the square is Cartesian. -/
class SmoothExcessSquare (dx dx' c' e : ℕ) : Prop where
  [varietyY : IsComplexVariety (affine A)]
  [varietyX : IsComplexVariety (affine (A ⧸ I))]
  [varietyY' : IsComplexVariety (affine B)]
  [varietyX' : IsComplexVariety (affine (base A B I))]
  [varietyN : IsComplexVariety (normalSpace A B I)]
  [smoothY : SmoothOfRelativeDimension (dx + (c' + e)) (affine A).hom]
  [smoothX : SmoothOfRelativeDimension dx (affine (A ⧸ I)).hom]
  [smoothY' : SmoothOfRelativeDimension (dx' + c') (affine B).hom]
  [smoothX' : SmoothOfRelativeDimension dx' (affine (base A B I)).hom]
  [smoothN : SmoothOfRelativeDimension (dx' + e) (normalSpace A B I).hom]
  [relativeN : SmoothOfRelativeDimension e
    (bundleProjection (base A B I) (excessNormal A B I)).left]
  [finiteNormal : Module.Finite (base A B I) (excessNormal A B I)]
  [projectiveNormal : Module.Projective (base A B I) (excessNormal A B I)]
  [nonemptyBase : Nonempty (affine (base A B I)).left]
  square : IsPullback (quotientBaseMap A B I).left
    (quotientMorphism B (extendedIdeal A B I)).left (quotientMorphism A I).left (affineMap A B).left
attribute [instance] SmoothExcessSquare.varietyY SmoothExcessSquare.varietyX
  SmoothExcessSquare.varietyY' SmoothExcessSquare.varietyX' SmoothExcessSquare.varietyN
  SmoothExcessSquare.smoothY SmoothExcessSquare.smoothX SmoothExcessSquare.smoothY'
  SmoothExcessSquare.smoothX' SmoothExcessSquare.smoothN SmoothExcessSquare.relativeN
  SmoothExcessSquare.finiteNormal SmoothExcessSquare.projectiveNormal
  SmoothExcessSquare.nonemptyBase

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))

variable (dx dx' c' e : ℕ) [SmoothExcessSquare A B I dx dx' c' e]

/-- The Euler class of the excess normal bundle: zero-section Gysin image of `1`,
pulled back by the zero section. -/
def euler (F : PureFamily D) : BettiRealization.Cohomology (space (affine (base A B I))) (2 * e) :=
  BettiCycleRealization.cohomologyCast (by omega)
    (cohomologyPullback (spaceMap (zeroSection (base A B I) (excessNormal A B I))) _
      (cohomologyPushforward (P (zeroSection (base A B I) (excessNormal A B I)))
        (D (affine (base A B I))) (D (normalSpace A B I)) dx' (dx' + e)
        (F.iso _ dx') (F.iso _ (dx' + e)) 0
          (unitClass (space (affine (base A B I))))))

/-- The excess intersection formula `g^* i_! a = j_!(e(E) ∪ g'^* a)` on the
square, for the Gysin maps and Euler class of the purity family `F`. -/
def ExcessFormula (F : PureFamily D) : Prop :=
  ∀ (n : ℤ) (a : BettiRealization.Cohomology (space (affine (A ⧸ I))) n),
    cohomologyPullback (spaceMap (affineMap A B)) _
      (cohomologyPushforward (P (quotientMorphism A I))
        (D (affine (A ⧸ I))) (D (affine A)) dx (dx + (c' + e))
        (F.iso _ dx) (F.iso _ (dx + (c' + e))) n a) =
    BettiCycleRealization.cohomologyCast (by omega)
      (cohomologyPushforward (P (quotientMorphism B (extendedIdeal A B I)))
        (D (affine (base A B I))) (D (affine B)) dx' (dx' + c')
        (F.iso _ dx') (F.iso _ (dx' + c')) (2 * e + n)
        (cup _ (euler A B I D P dx dx' c' e F)
          (cohomologyPullback (spaceMap (quotientBaseMap A B I)) n a)))

end Square

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))

/-- One purity family, chosen once for all smooth complex varieties, for which
the excess intersection formula holds on every smooth affine excess square. -/
structure ExcessPurities where
  /-- The purity family. -/
  family : PureFamily D
  /-- The excess intersection formula on every square. -/
  excess : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra A B] [IsScalarTower ℂ A B] (I : Ideal A) (dx dx' c' e : ℕ)
    [SmoothExcessSquare A B I dx dx' c' e], ExcessFormula A B I D P dx dx' c' e family

end MathlibExt.AlgebraicGeometry.AffineExcessBetti
