/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EnhancedStableCoefficientModels
public import MathlibExt.AlgebraicGeometry.OrdinaryIndDerivedModels
public import MathlibExt.AlgebraicGeometry.BoundedIndOperationSources
public import MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels
public import MathlibExt.AlgebraicGeometry.EnhancedSheafHomModels

/-!
# The computed ordinary enhancement e

The functor is the actual bounded ordinary iota, the original base
inverse image, coefficient tensor with the fixed stable half-line Ind
colimit in degree zero, and Q. It is covariant, with those actual maps.
There is no additional shift and no separately supplied enhancement.

Source: DK1311.2374v2 Proposition9.1.3, printed94, and Proposition9.5.4;
Mathlib56a005 native iota, tensor, inverse image and localization, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinaryEnhancedEmbeddingModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels OrdinaryIndDerivedModels
open EnhancedStableCoefficientModels EnhancedIndQuotientModels BoundedIndOperationSources
open BorderedIndDerivedModels EnhancedConvolutionModels
open BorderedRealTimeModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

variable (X : TopCat.{0})
  [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X]
  [CompactSheafSource ℂ (enhancedSpace X).ambient]
  [CompactSheafSource ℂ (boundarySpace (enhancedSpace X))]

local instance ordinaryPreadditive : Preadditive (OrdinarySheaf ℂ X) := Abelian.toPreadditive
local instance indPreadditive (Z : TopCat.{0}) [CompactSheafSource ℂ Z] : Preadditive (IndSheaf ℂ Z) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (Iota : OrdinaryIndSource ℂ X) [(ordinaryToInd ℂ X Iota).Additive]
  (Exact : ExactImageSource (ordinaryToInd ℂ X Iota))
  (Bounded : BoundedIotaSource ℂ X Iota Exact)
  (Boundary : ProperSource ℂ (boundaryInclusion (enhancedSpace X)))
  (Projection : InverseSource ℂ (baseProjection X))
  (Tensor : TensorSource ℂ (enhancedSpace X).ambient)
  (Closed : ClosedHalfLineDiagramSource X)
  (StableIota : OrdinaryIndSource ℂ (enhancedSpace X).ambient)
  (Colimit : StableColimitSource X Closed StableIota)
  (StableBounded : IsBounded ℂ (enhancedSpace X).ambient
    ((DerivedCategory.singleFunctor (IndSheaf ℂ (enhancedSpace X).ambient) 0).obj
      (stableIndCoefficient X Closed StableIota Colimit)))

def stableCoefficient : BoundedIndDerived ℂ (enhancedSpace X).ambient :=
  ⟨(DerivedCategory.singleFunctor (IndSheaf ℂ (enhancedSpace X).ambient) 0).obj
    (stableIndCoefficient X Closed StableIota Colimit), StableBounded⟩

/-- e(F) = C_X^E tensor pi^-1(iota F), by actual coefficient tensor and Q. -/
def ordinaryEnhancedEmbedding : BoundedOrdinary ℂ X ⥤
    EnhancedCategory ℂ X Boundary Projection :=
  boundedIota ℂ X Iota Exact Bounded ⋙ inverseFunctor ℂ (baseProjection X) Projection ⋙
    (tensorFunctor ℂ (enhancedSpace X).ambient Tensor).obj
      (stableCoefficient X Closed StableIota Colimit StableBounded) ⋙
    enhancedSourceProjection ℂ X Boundary Projection

end MathlibExt.AlgebraicGeometry.OrdinaryEnhancedEmbeddingModels
