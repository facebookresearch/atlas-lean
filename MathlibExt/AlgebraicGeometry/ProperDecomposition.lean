/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import MathlibExt.AlgebraicGeometry.PerverseSheaves

/-!
# Proper images, semismall defect and support data

The normalized image is the actual `Rf_* Q_X[d]`. The amplitude parameter is
geometric: `dim(X ×_Y X) ≤ d + r`. It is not an independently named bound.
Unlike the original projective-source request, the matching Wanted module
allows every smooth complex source and proper algebraic map.

The normalized direct-image construction follows the completed Mathlib-based
construction in ATLAS PR1970, `ProjectiveDirectImage.lean`. The functions below
have complete bodies and import no perverse-provider or decomposition request.

## References

* de Cataldo–Migliorini, https://arxiv.org/abs/0712.0349, Theorem 1.6.1,
  §§3.3.2 and 4.2.
* BBD, *Faisceaux pervers*, Astérisque 100 (1982), Theorem 6.2.5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperDecomposition

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry ComplexAnalytification PerverseSheaves

attribute [local instance] HasDerivedCategory.standard

/-- The actual rational direct image of a constant sheaf in degree `-d`. -/
def normalizedDirectImage (X Y : ComplexScheme) (f : X ⟶ Y) (d : ℕ) :
    RationalDerived (space Y) :=
  DerivedCategory.Plus.ι.obj
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (spaceMap f)).rightDerivedFunctorPlus).obj
      ((DerivedCategory.Plus.singleFunctor (RationalSheaf (space X)) (-(d : ℤ))).obj
        (rationalConstantSheaf (space X))))

/-- Package the image in the actual constructible category once its external
constructibility hypothesis is supplied. -/
def constructibleImage (X Y : ComplexScheme) (f : X ⟶ Y) (d : ℕ)
    (hK : boundedConstructible Y (normalizedDirectImage X Y f d)) :
    (boundedConstructible Y).FullSubcategory :=
  ⟨normalizedDirectImage X Y f d, hK⟩

/-- Geometric defect bound: the self-fiber-product has dimension at most `d+r`. -/
def DefectLE {X Y : ComplexScheme} (f : X ⟶ Y) (d r : ℕ) : Prop :=
  topologicalKrullDim (pullback f.left f.left : Scheme.{0}) ≤
    ((d + r : ℕ∞) : WithBot ℕ∞)

/-- The actual fiber over a complex point, as a scheme pullback. -/
def pointFiber {X Y : ComplexScheme} (f : X ⟶ Y) (p : space Y) : Scheme.{0} :=
  pullback f.left p.hom

/-- The underlying derived object of a perverse object. -/
def perverseAmbient (Y : ComplexScheme) [IsComplexVariety Y] [PerverseSheafTheory Y] :
    PerverseSheaf Y ⥤ RationalDerived (space Y) :=
  (perverseTStructure Y).heart.ι ⋙ (boundedConstructible Y).ι

end MathlibExt.AlgebraicGeometry.ProperDecomposition
