/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The computed global cotangent exterior/de Rham comparison

The source is RΓ of the actual native cotangent exterior square. First
enter the full injective coefficient diagram using the actual all-degree
global-section map. In the localization of whole diagrams, invert the
actual raw coefficient augmentation and projective source resolution,
apply the full DG exterior(df), and apply the original polynomial and
derived scalar-extension span. A cone into the actual injective weight
target represents that entire class. Its native coherent limit is taken.
The target index is the actual affine mapping prestack. Its augmentation
to F is native evaluation at Q(A) to A. Restriction on de Rham weights
is the actual full reindexed cochain pullback; its sourced inverse merely
changes that equivalent index. Thus the direction is
RΓ(exterior-square L_F) to DR(F)(2)[-2].

A cochain representative is required to represent this computed derived
morphism. Its quasi-isomorphism is a separate Wanted theorem. No equality
f*L_F=L_A for an arbitrary affine map, and no supplied eta endpoint, is
used in the definition.

Source: PTVV arXiv:1111.3209v4, Proposition 1.14 and Lemma 1.15;
HAG II arXiv:math/0404373v7, Sections 1.3.7 and 1.4.1. Source notices of
the native DG, diagram-localization and derived-category imports remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
open MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u
variable {k : Type u} [CommRing k] {Q : AlgebraReplacementFunctor k}
    {D : AffineDRSystem Q} {NC : NegativeCyclicDiagram D.functor (2 : ℤ)}
attribute [local instance] HasDerivedCategory.standard

/-- The actual whole weight pullback lift, with its original reindexed augmentation. -/
def weightPullbackLift {X Y : Prestack k} (f : X ⟶ Y)
    (FY : GlobalNCModel D 2 NC Y) (FX : GlobalNCModel D 2 NC X) :
    reindex f ⋙ FY.ordinary.diagram ⟶ FX.ordinary.diagram :=
  Classical.choose (FX.ordinary.fibrant _ _ (Functor.whiskerLeft (reindex f) FY.ordinary.map)
    (fun j => ⟨FY.ordinary.mono ((reindex f).obj j), FY.ordinary.weak ((reindex f).obj j)⟩)
    FX.ordinary.map)

/-- Its square fixes the complete actual raw de Rham weight diagram. -/
theorem weightPullbackLift_square {X Y : Prestack k} (f : X ⟶ Y)
    (FY : GlobalNCModel D 2 NC Y) (FX : GlobalNCModel D 2 NC X) :
    Functor.whiskerLeft (reindex f) FY.ordinary.map ≫ weightPullbackLift f FY FX =
      FX.ordinary.map :=
  Classical.choose_spec (FX.ordinary.fibrant _ _ (Functor.whiskerLeft (reindex f) FY.ordinary.map)
    (fun j => ⟨FY.ordinary.mono ((reindex f).obj j), FY.ordinary.weak ((reindex f).obj j)⟩)
    FX.ordinary.map)

/-- The global ordinary weight restriction retains every affine, parameter and gauge projection. -/
def weightPullback {X Y : Prestack k} (f : X ⟶ Y)
    (FY : GlobalNCModel D 2 NC Y) (FX : GlobalNCModel D 2 NC X) :
    weightComplex FY ⟶ weightComplex FX :=
  limit.lift FX.ordinary.diagram
    ⟨weightComplex FY,
      Functor.whiskerLeft (reindex f) (limit.cone FY.ordinary.diagram).π ≫
        weightPullbackLift f FY FX⟩

/-- Restriction keeps the original source exterior/weight shift minus two. -/
def coefficientWeightPullback {X Y : Prestack k} (f : X ⟶ Y)
    (FY : GlobalNCModel D 2 NC Y) (FX : GlobalNCModel D 2 NC X) :=
  (coefficientWeightFunctor k).map (weightPullback f FY FX)

variable [Algebra ℚ k] {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {R : RawModuleRealization M}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}

/-- Eta is the computed injective coefficient/weight limit followed by inverse native index restriction. -/
def globalExteriorClass (C : CoherentExteriorCone B)
    (FF : GlobalNCModel D 2 NC F) (FP : GlobalNCModel D 2 NC (affineParameterPrestack Q F))
    [PreservesLimit FP.ordinary.diagram (coefficientWeightFunctor k)]
    [QuasiIso (coefficientWeightPullback (affineParameterPoint Q F) FF FP)] :
    DerivedCategory.Q.obj (globalHom G E.object) ⟶
      DerivedCategory.Q.obj (((globalToCoefficients k).obj (weightComplex FF))⟦-2⟧) :=
  DerivedCategory.Q.map (parameterExteriorComparison C FP) ≫
    inv (DerivedCategory.Q.map (coefficientWeightPullback (affineParameterPoint Q F) FF FP))

/-- A representative is fixed by that same computed derived map, never by an arbitrary eta hypothesis. -/
structure GlobalExteriorRepresentative (C : CoherentExteriorCone B)
    (FF : GlobalNCModel D 2 NC F) (FP : GlobalNCModel D 2 NC (affineParameterPrestack Q F))
    [PreservesLimit FP.ordinary.diagram (coefficientWeightFunctor k)]
    [QuasiIso (coefficientWeightPullback (affineParameterPoint Q F) FF FP)] where
  map : globalHom G E.object ⟶ ((globalToCoefficients k).obj (weightComplex FF))⟦-2⟧
  normalized : DerivedCategory.Q.map map = globalExteriorClass C FF FP

end MathlibExt.AlgebraicGeometry.DerivedNormalizedGlobalExteriorComparison
