/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalCotangentSquareMaps

/-!
# The original derived equivariant obstruction morphism

The cotangent action is computed from the action square relative to Gm
and the inverse of the actual product-base-change comparison. The source
comparison is the native derived inverse-image counit on the globally
two-term bundle complex. Its cochain action is fixed in both nonzero
degrees by the original term linearizations. Equivariance is an equality
for the original derived phi through these particular operators.

Source: Graber--Pandharipande alg-geom/9708001v2, Section1, equation(4).
The source simplifying global cochain phi is not assumed here.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EquivariantDerivedObstructionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open GlobalObstructionMorphisms GlobalPerfectObstructionTheory GlobalPOTVirtualClass
open AlgebraicWeightBundleModels DerivedTwoTermObstructionModels
open SchemeDerivedCotangentPullbacks CotangentSquareResolutionMaps GlobalCotangentSquareMaps
attribute [local instance] HasDerivedCategory.standard
open scoped _root_.CategoryTheory.MonObj

variable (X : Over base) [ModObj Gm X]

def actionMap : (Gm ⊗ X).left ⟶ X.left := γ[Gm,X].left

def projectionMap : (Gm ⊗ X).left ⟶ X.left := (snd Gm X).left

def torusProjection : (Gm ⊗ X).left ⟶ Gm.left := (fst Gm X).left

/-- The action is read as a square over the actual torus base. -/
def actionSquare : SchemeSquare X.hom (torusProjection X) where
  top := actionMap X
  bottom := Gm.hom
  commutes := by
    change γ[Gm,X].left ≫ X.hom = (fst Gm X).left ≫ Gm.hom
    exact (Over.w γ[Gm,X]).trans (Over.w (fst Gm X)).symm

/-- The product-base-change square uses the actual projection. -/
def projectionSquare : SchemeSquare X.hom (torusProjection X) where
  top := projectionMap X
  bottom := Gm.hom
  commutes := by
    exact (Over.w (snd Gm X)).trans (Over.w (fst Gm X)).symm

/-- Every relative cotangent comparison is normalized on the actual source squares. -/
structure CotangentActionData (C : CotangentNormalization X.hom) where
  relative : CotangentNormalization (torusProjection X)
  actionPullback : DerivedPullbackSource (actionMap X)
  projectionPullback : DerivedPullbackSource (projectionMap X)
  action : SquareMap (actionSquare X) C relative
  projection : SquareMap (projectionSquare X) C relative
  projectionIso : IsIso (projection.derived projectionPullback)

/-- The cotangent linearization is this exact relative differential and inverse base change. -/
def CotangentActionData.linearization {C : CotangentNormalization X.hom}
    (D : CotangentActionData X C) :
    (derivedPullback (actionMap X) D.actionPullback).obj (DerivedCategory.Q.obj C.complex) ⟶
      (derivedPullback (projectionMap X) D.projectionPullback).obj (DerivedCategory.Q.obj C.complex)
        :=
  D.action.derived D.actionPullback ≫
    (@asIso _ _ _ _ (D.projection.derived D.projectionPullback) D.projectionIso).inv

variable {X}

/-- The degree-zero injection is the native cone injection after the native single-complex term
  isomorphism. -/
def sourceZeroInclusion (E : TwoTermModel X.left) : E.degreeZero ⟶ (sourceComplex E).X 0 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 E.degreeZero).inv ≫
    (CochainComplex.mappingCone.inr ((CochainComplex.singleFunctor X.left.Modules 0).map
      E.differential)).f 0

/-- The negative degree uses the original cone's degree-minus-one injection. -/
def sourceNegativeInclusion (E : TwoTermModel X.left) : E.negative ⟶ (sourceComplex E).X (-1) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 E.negative).inv ≫
    (CochainComplex.mappingCone.inl ((CochainComplex.singleFunctor X.left.Modules 0).map
      E.differential)).v
      0 (-1) (by omega)

/-- The source action is the original linearization in both actual nonzero terms. -/
structure SourceActionData (E : EquivariantObstructionTerms X)
    (C : CotangentActionData X E.obstruction.cotangent) where
  actionAcyclic : SourceAcyclic (actionMap X) C.actionPullback E.obstruction.model
  projectionAcyclic : SourceAcyclic (projectionMap X) C.projectionPullback E.obstruction.model
  map : ((Scheme.Modules.pullback (actionMap X)).mapHomologicalComplex (.up ℤ)).obj
      (sourceComplex E.obstruction.model) ⟶
    ((Scheme.Modules.pullback (projectionMap X)).mapHomologicalComplex (.up ℤ)).obj
      (sourceComplex E.obstruction.model)
  zero : (Scheme.Modules.pullback (actionMap X)).map (sourceZeroInclusion E.obstruction.model) ≫
    map.f 0 = E.degreeZero.comparison.hom ≫
      (Scheme.Modules.pullback (projectionMap X)).map (sourceZeroInclusion E.obstruction.model)
  negative : (Scheme.Modules.pullback (actionMap X)).map (sourceNegativeInclusion
    E.obstruction.model) ≫
    map.f (-1) = E.negative.comparison.hom ≫
      (Scheme.Modules.pullback (projectionMap X)).map (sourceNegativeInclusion E.obstruction.model)

/-- The source derived action is computed from its normalized cochain and the actual native
counits. -/
def SourceActionData.linearization {E : EquivariantObstructionTerms X}
    {C : CotangentActionData X E.obstruction.cotangent} (S : SourceActionData E C) :=
  (sourceComparison (actionMap X) C.actionPullback E.obstruction.model S.actionAcyclic).hom ≫
    DerivedCategory.Q.map S.map ≫
    (sourceComparison (projectionMap X) C.projectionPullback E.obstruction.model
      S.projectionAcyclic).inv

/-- Full equivariance is imposed on the original derived obstruction map. -/
def IsEquivariantObstruction (E : EquivariantObstructionTerms X)
    (C : CotangentActionData X E.obstruction.cotangent) (S : SourceActionData E C) : Prop :=
  (derivedPullback (actionMap X) C.actionPullback).map E.obstruction.map ≫ C.linearization =
    S.linearization ≫ (derivedPullback (projectionMap X) C.projectionPullback).map E.obstruction.map

end MathlibExt.AlgebraicGeometry.EquivariantDerivedObstructionModels
