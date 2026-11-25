/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeDerivedCotangentPullbacks

/-!
# Actual affine polynomial-resolution maps of scheme squares

The base and coefficient maps come from the original commuting scheme
square and its actual affine opens. Every resolution map preserves those
coefficients, its original augmentation and every simplicial operator.
The induced cotangent map is fixed on every pure differential in every
negative degree. This is the local normalization for the derived
cotangent differential; it does not replace it by a freely named map.

Completed source maps: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Cotangent/SheavesOfRings/SquareFunctoriality.lean,
squareCotangentComplexMap_derivation. Scheme adaptation is separate.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CotangentSquareResolutionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.Simplicial
open GlobalObstructionMorphisms GlobalPerfectObstructionTheory GeometricCotangentComplex

variable {X Y X' Y' : Scheme.{0}} (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- The original full scheme square is retained before taking cotangent objects. -/
structure SchemeSquare where
  top : X' ⟶ X
  bottom : Y' ⟶ Y
  commutes : top ≫ f = f' ≫ bottom

variable {f f'} (S : SchemeSquare f f')

/-- Both local ring maps are the actual restrictions of this same scheme square. -/
structure AffineSquare where
  original : AffineChart f
  changed : AffineChart f'
  source : changed.source ≤ S.top ⁻¹ᵁ original.source
  base : changed.target ≤ S.bottom ⁻¹ᵁ original.target

def sourceRingMap (a : AffineSquare S) : a.original.ring →+* a.changed.ring :=
  (S.top.appLE a.original.source a.changed.source a.source).hom

def baseRingMap (a : AffineSquare S) : a.original.base →+* a.changed.base :=
  (S.bottom.appLE a.original.target a.changed.target a.base).hom

/-- The coefficient ring square is an equality of the original scheme-induced maps. -/
def CoefficientSquare (a : AffineSquare S) : Prop :=
  (sourceRingMap S a).comp (algebraMap a.original.base a.original.ring) =
    (algebraMap a.changed.base a.changed.ring).comp (baseRingMap S a)

/-- The all-degree map has actual resolution and generator normalization. -/
structure ResolutionSquare (a : AffineSquare S)
    (R : PolynomialResolution a.original.base a.original.ring)
    (T : PolynomialResolution a.changed.base a.changed.ring) where
  coefficient : CoefficientSquare S a
  polynomialMap : ∀ n : SimplexCategoryᵒᵖ, R.algebra.obj n →+* T.algebra.obj n
  scalar : ∀ (n : SimplexCategoryᵒᵖ) (r : a.original.base),
    polynomialMap n (algebraMap a.original.base (R.algebra.obj n) r) =
      algebraMap a.changed.base (T.algebra.obj n) (baseRingMap S a r)
  augmentation : ∀ (n : SimplexCategoryᵒᵖ) (r : R.algebra.obj n),
    T.augmentation.app n (polynomialMap n r) = sourceRingMap S a (R.augmentation.app n r)
  simplicial : ∀ {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) (r : R.algebra.obj n),
    polynomialMap m (R.algebra.map g r) = T.algebra.map g (polynomialMap n r)
  map : affineComplex R ⟶
    ((ModuleCat.restrictScalars (sourceRingMap S a)).mapHomologicalComplex (.up ℤ)).obj
      (affineComplex T)
  pure : ∀ (n : ℕ) (r : R.algebra.obj (op ⦋n⦌)),
    (affineDegreeIso T n).hom ((map.f (-(n : ℤ))).hom
      ((affineDegreeIso R n).inv
        (CommAlgCat.resolutionCotangentTermDifferential a.original.base
          (CommAlgCat.of a.original.base a.original.ring) R.algebra R.augmentation (op ⦋n⦌) r))) =
    CommAlgCat.resolutionCotangentTermDifferential a.changed.base
      (CommAlgCat.of a.changed.base a.changed.ring) T.algebra T.augmentation (op ⦋n⦌)
        (polynomialMap (op ⦋n⦌) r)

end MathlibExt.AlgebraicGeometry.CotangentSquareResolutionMaps
