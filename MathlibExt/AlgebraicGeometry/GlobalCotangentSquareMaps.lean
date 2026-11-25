/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CotangentSquareResolutionMaps

/-!
# Scheme-square cotangent differentials on the original modules

The section map uses the native scheme-module pullback adjunction unit
and the actual source-open restriction. Every coefficient and polynomial
resolution map is the original scheme-square map. The global cochain map
is tested on all pure differentials in all degrees through those sections.
Its derived map is the native derived counit followed by its native Q-map.

The canonical flat cotangent diagram is source integration from the
completed Stacks SquareFunctoriality, PullbackCotangentComplex and
BaseChangedCotangentDerived constructions. Existence for arbitrary chosen
noncanonical complexes is not asserted here.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalCotangentSquareMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.Simplicial
open GlobalObstructionMorphisms GlobalPerfectObstructionTheory GeometricCotangentComplex
open CotangentSquareResolutionMaps SchemeDerivedCotangentPullbacks
attribute [local instance] HasDerivedCategory.standard

variable {X Y X' Y' : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  (S : SchemeSquare f f') (C : CotangentNormalization f) (C' : CotangentNormalization f')

def pulledComplex : Complex X' :=
  ((Scheme.Modules.pullback S.top).mapHomologicalComplex (.up ℤ)).obj C.complex

/-- Pull an actual source section using the same module adjunction unit and restriction. -/
def pullSection (a : AffineSquare S) (M : X.Modules) (s : (moduleSections a.original.source).obj M)
  :
    (moduleSections a.changed.source).obj ((Scheme.Modules.pullback S.top).obj M) :=
  (((Scheme.Modules.pullback S.top).obj M).val.map (homOfLE a.source).op).hom
    (((((Scheme.Modules.pullbackPushforwardAdjunction S.top).unit.app M).val.app
      (op a.original.source)).hom) s)

/-- The full source map is fixed by every original affine polynomial differential. -/
structure SquareMap where
  resolution : ∀ a : AffineSquare S, ResolutionSquare S a
    (C.resolution a.original) (C'.resolution a.changed)
  cochain : pulledComplex S C ⟶ C'.complex
  normalized : ∀ (a : AffineSquare S) (n : ℕ)
    (r : (C.resolution a.original).algebra.obj (op ⦋n⦌)),
    ((cochain.f (-(n : ℤ))).val.app (op a.changed.source)).hom
      (pullSection S a (C.complex.X (-(n : ℤ)))
        (((C.comparison a.original).f (-(n : ℤ))).hom
          ((affineDegreeIso (C.resolution a.original) n).inv
            (CommAlgCat.resolutionCotangentTermDifferential a.original.base
              (CommAlgCat.of a.original.base a.original.ring)
              (C.resolution a.original).algebra (C.resolution a.original).augmentation
              (op ⦋n⦌) r)))) =
    (((C'.comparison a.changed).f (-(n : ℤ))).hom
      ((affineDegreeIso (C'.resolution a.changed) n).inv
        (CommAlgCat.resolutionCotangentTermDifferential a.changed.base
          (CommAlgCat.of a.changed.base a.changed.ring)
          (C'.resolution a.changed).algebra (C'.resolution a.changed).augmentation
          (op ⦋n⦌) ((resolution a).polynomialMap (op ⦋n⦌) r))))

/-- The actual derived differential is formed from these same native maps. -/
def SquareMap.derived {S : SchemeSquare f f'} {C : CotangentNormalization f}
    {C' : CotangentNormalization f'} (M : SquareMap S C C') (P : DerivedPullbackSource S.top) :
    (derivedPullback S.top P).obj (DerivedCategory.Q.obj C.complex) ⟶
      DerivedCategory.Q.obj C'.complex :=
  (derivedPullbackCounit S.top P).app C.complex ≫ DerivedCategory.Q.map M.cochain

/-- A flat canonical source makes the native counit invertible on its actual cotangent. -/
def CotangentAcyclic (P : DerivedPullbackSource S.top) : Prop :=
  IsIso ((derivedPullbackCounit S.top P).app C.complex)

end MathlibExt.AlgebraicGeometry.GlobalCotangentSquareMaps
