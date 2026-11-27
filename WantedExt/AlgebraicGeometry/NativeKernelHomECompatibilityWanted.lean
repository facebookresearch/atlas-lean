/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeKernelHomETargetModels

/-!
# Native ringed reconstruction target and literal enhanced Hom

The kernel is an object of the actual source enhanced D-module quotient.
Its coefficient image is computed by native localization of the full
coefficient forgetful functor, with every map fixed by factorization.
The compared target is the original beta-pi/module-tensor-Hom target;
Hom^E is literally alpha Rpi_* RIhom(LE,RE). This is a compatibility
request for that ringed target, without a general scalar-tensor Hom^E
adjunction. Applied to the computed O^E it compares the two targets of
Proposition9.5.1 objectwise, for each M: the isomorphism is neither natural
in M nor required to carry the constructed map to the morphism of
Proposition9.5.1, so it does not identify (9.5.1) itself. The holonomic
IsIso request concerns the separate ringed-mate reconstruction map.

The three adjoint-existence hypotheses (the left adjoint of the enhanced
quotient, the internal Hom of the coefficient tensor and the right adjoint
of the β-pullback) are the instance requests
`coefficient_enhanced_quotient_left_adjoint`, `bounded_coefficient_tensor_closed`
and `ordinary_beta_pull_right_adjoint` of NativeEnhancedRiemannHilbertWanted;
no unit of the quotient adjunctions is assumed invertible.

Source: DK1311.2374v2 Definition4.5.13, Proposition9.5.1, Theorem9.5.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeKernelHomECompatibilityWanted

open MathlibExt.AlgebraicGeometry NativeKernelReconstructionModels NativeKernelHomETargetModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeIndModuleInverseModels
open NativeEnhancedModuleGeometry NativeBetaModuleDerivedModels NativeEnhancedKernelFunctorModels
open ProjectiveExponentialSectionModels ProductDifferentialOperatorModels
open BorderedIndDerivedModels EnhancedIndQuotientModels EnhancedConvolutionModels
open BoundedIndOperationSources
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeRingedReconstructionMaps
open scoped Manifold ContDiff

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) X]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ X]
  [ProjectiveComplexSource]
  [HasSheafify (Opens.grothendieckTopology X) RingCat.{0}]
  [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [CompactSheafSource ℂ (TopCat.of X)] [IndSpaceSource (TopCat.of X)]
  [DifferentialBetaSource X (analyticCoefficients n X)]
  [OppositeDifferentialBetaSource X (analyticCoefficients n X)]
  [CompactSheafSource ℂ (ProductSpace X)] [IndSpaceSource (ProductSpace X)]
  [CompactSheafSource ℂ (enhancedSpace (TopCat.of X)).ambient]
  [IndSpaceSource (enhancedSpace (TopCat.of X)).ambient]
  [CompactSheafSource ℂ (boundarySpace (enhancedSpace (TopCat.of X)))]
  [IndSpaceSource (boundarySpace (enhancedSpace (TopCat.of X)))]
  (Real : RealProjectiveMapSource) (First : InverseMonoidalSource (xProjection X))
  (Graph : InverseMonoidalSource (realGraphInclusion (TopCat.of X) Real))
  (Geometry : EnhancedModuleGeometrySource n X Real First Graph)

local instance reconstructionIndPreadditive (Z : TopCat.{0}) [CompactSheafSource ℂ Z] :
    Preadditive (IndSheaf ℂ Z) := Abelian.toPreadditive
local instance reconstructionModulePreadditive (Z : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ Z] [IndSpaceSource Z] (R S : Mon (IndSheaf ℂ Z)) :
    Preadditive (Bimod R S) := Abelian.toPreadditive
local instance reconstructionOrdinaryPreadditive :
    Preadditive (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
      (analyticDifferentialRing n X)) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (N : OrdinaryBetaModuleSource (TopCat.of X) (analyticDifferentialRing n X))
  (Normalize : BetaUnitNormalizationSource (TopCat.of X) (analyticDifferentialRing n X))
  [(betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize).Additive]
  (BetaExact : ExactImageSource (betaUnitModules (TopCat.of X) (analyticDifferentialRing n X) N Normalize))
  (Representatives : ModuleRepresentativeSource (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry))
  (Kernel : NativeEnhancedDModules n X Real First Graph Geometry)
  [LeftTensorDerivationSource (RY n X Real First Graph) (KY X) (KY X)]
  [LeftTensorHomSource (RY n X Real First Graph) (KY X) (KY X)]
  [(Bimod.forget (B := KY X) (KY X)).Additive]
  (CoefficientExact : ExactCoefficientSource (KY X) (KY X))
  (CoefficientBounded : BoundedCoefficientSource (KY X) (KY X) CoefficientExact)
  (Boundary : ProperSource ℂ (boundaryInclusion (enhancedSpace (TopCat.of X))))
  (Projection : InverseSource ℂ (baseProjection (TopCat.of X)))


variable
  [(coefficientEnhancedQ X CoefficientExact CoefficientBounded Boundary Projection).IsRightAdjoint]


variable [∀ H : BoundedModules (KY X) (KY X),
    ((boundedCoefficientTensor n X Real First Graph).obj H).IsLeftAdjoint]
  [(originalOrdinaryBetaPull n X Real First Graph Geometry N Normalize BetaExact).IsLeftAdjoint]
  (M : DerivedCategory (RingedComplexCoefficientModels.OrdinaryModule (TopCat.of X)
    (analyticDifferentialRing n X)))
  (BoundedSolution : IsBoundedDerived (Bimod (KY X) (KY X))
    ((solutionsWithKernel n X Real First Graph Geometry N Normalize BetaExact
      Representatives Kernel).obj (Opposite.op M)))



open EnhancedSheafHomModels IndSheafDerivedAlphaModels

local instance wantedKernelOrdinarySheafPreadditive :
    Preadditive (OrdinarySheaf ℂ (TopCat.of X)) := Abelian.toPreadditive

variable [N.forget.functor.Additive]
  (ForgetExact : ExactImageSource N.forget.functor)
  [(Bimod.forget (B := KY X) (RY n X Real First Graph)).Additive]
  (ModuleExact : ExactCoefficientSource (RY n X Real First Graph) (KY X))
  (ModuleBounded : BoundedCoefficientSource (RY n X Real First Graph) (KY X) ModuleExact)

/-- The coefficient functor descends to the enhanced $\mathcal{D}$-module quotient. Let $X$ be a
Hausdorff complex manifold of dimension $n$, with the given interface data, among them the enhanced
module geometry `Geometry`, the boundary proper image `Boundary`, the base inverse image
`Projection`, and the exactness `ModuleExact` and boundedness `ModuleBounded` of forgetting the
module structure. Then the functor `moduleCoefficientQuotientInput`, from bounded objects of the
derived category of modules over `RY` (bimodules over `RY` and the trivial monoid `KY`) in
ind-sheaves on the ambient space of the enhanced space of $X$ to the enhanced category of
ind-sheaves, which forgets the module structure and then applies the enhanced quotient, inverts
every morphism whose cone lies in the smallest triangulated subcategory closed under isomorphisms
that contains the boundary proper images `nativeBoundaryImage` and the inverse images from the base
`nativeBaseInverse`. -/
theorem_wanted native_module_coefficients_descend :
  ModuleCoefficientQuotientSource (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
    (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection ModuleExact ModuleBounded)

variable (Factor : ModuleCoefficientQuotientSource (RY n X Real First Graph) (KY X)
    (nativeBoundaryImage n X Real First Graph Geometry) (nativeBaseInverse n X Real First Graph Geometry)
    (moduleCoefficientQuotientInput n X Real First Graph Boundary Projection ModuleExact ModuleBounded))
  (AmbientTensor : TensorSource ℂ (enhancedSpace (TopCat.of X)).ambient)
  (HomRepresentatives : EnhancedRepresentativeSource ℂ (TopCat.of X) Boundary Projection)
  (HomClosed : AmbientIhomSource ℂ (TopCat.of X) AmbientTensor)
  (Pi : ProperSource ℂ (baseProjection (TopCat.of X)))
  [(IndSheafAlphaBetaModels.alpha ℂ (TopCat.of X)
    (IndSpaceSource.alpha (X := TopCat.of X))).Additive]
  (AlphaExact : ExactAlphaSource ℂ (TopCat.of X) (IndSpaceSource.alpha (X := TopCat.of X)))

/-- For a given $M$, an isomorphism between the ringed reconstruction target and the enhanced Hom
target of a kernel $\mathcal{K}$. Let $X$ be a Hausdorff complex manifold of dimension $n$ with the
given interface data, $M$ an object of the derived category of modules over the ring of analytic
differential operators on $X$, and $\mathcal{K}$ (`Kernel`) an object of the enhanced
$\mathcal{D}$-module quotient such that the solution complex of $M$ with kernel $\mathcal{K}$ is
bounded (`BoundedSolution`); let $S$ be its class in the enhanced category. Assume that the
coefficient functor descends to the enhanced quotient (`Factor`, the statement of
`native_module_coefficients_descend`), that the enhanced quotient of coefficients has a left
adjoint, that tensoring with each bounded coefficient complex has a right adjoint, and that the
pulled-back $\beta$-functor has a right adjoint. This constructs an isomorphism, in the derived
category of sheaves of complex vector spaces on $X$, from `reconstructionCoefficientsTarget`, the
underlying complex of the ringed reconstruction target of $M$ (the right adjoint of the pulled-back
$\beta$-functor applied to the internal Hom from the left representative of $S$ to the right
representative of $\mathcal{K}$), to `scalarHomETarget`, the enhanced Hom
$\alpha\,R\pi_*\,R\mathcal{I}hom(L^E S, R^E K)$ from $S$ to the coefficient image $K$ of
$\mathcal{K}$. The isomorphism is not required to be natural in $M$ or compatible with the
reconstruction morphism `originalReconstructionMap` (D'Agnolo–Kashiwara, Proposition 9.5.1). -/
def_wanted native_reconstruction_target_HomE_iso :
  reconstructionCoefficientsTarget n X Real First Graph Geometry N Normalize BetaExact Representatives
    Kernel CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution ForgetExact ≅
  scalarHomETarget n X Real First Graph Geometry N Normalize BetaExact Representatives
    Kernel CoefficientExact CoefficientBounded Boundary Projection M BoundedSolution
      ModuleExact ModuleBounded Factor AmbientTensor HomRepresentatives HomClosed Pi AlphaExact


end WantedExt.AlgebraicGeometry.NativeKernelHomECompatibilityWanted
