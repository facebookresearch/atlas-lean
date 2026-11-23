/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
public import Batteries.Util.ProofWanted

/-!
# Actual integration realization and source naturality requests

The integration representative realizes the computed global κ/NC/trace
composite in the actual global complexes. Naturality retains the full
mixed pullback squares and both source factors. The ordinary-form square
uses the actual first closing coefficient, not a separately named map.
Reference: PTVV arXiv:1111.3209v4, Definition 2.3 and Theorem 2.5.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.Algebra.Homology.WeightedClosedFormSpaces
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.Algebra.Homology.ShiftedTensorUnits
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
open MathlibExt.AlgebraicGeometry.DerivedRelativeAffineDiagrams
open MathlibExt.AlgebraicGeometry.DerivedGlobalRelativeDeRham
open MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u
attribute [local instance] HasDerivedCategory.standard

def_wanted actualGlobalIntegrationRepresentative (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (RM : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (R : ProductReplacementSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (SL : StrongCochainLift L) (V : NerveLiftModel L)
    (F X : DerivedStack Q) (B : SourcedScalarFamily M U RM Q L V X.functor)
    (G : GlobalMixedModel D T F.functor) (GP : GlobalMixedModel D T (F.functor ⊗ X.functor))
    (P : PureTensorModel G.mixed (gammaCoefficients B.family.model B.absolute B.scalar))
    (A : GlobalRelativeModel B.family.model B.absolute B.scalar B.gamma R SL G GP P)
    (projectionWeak : ∀ w : ℤ, QuasiIso (A.projection.map.map w))
    (p : ℕ) (NC : NegativeCyclicDiagram D.functor (p : ℤ))
    (W : NCCategoryModel (LargeScalar k) (p : ℤ))
    (K : Comparison P (p : ℤ) (W.diagram.toModel G.mixed) (W.diagram.toModel P.mixed))
    [IsIso (DerivedCategory.Q.map K.map)] (d : ℤ)
    (η : TraceSystem B.family.model B.absolute B.scalar d)
    (shift : UnitTensorModel (W.diagram.complex.obj G.mixed) (-d))
    (FP : GlobalNCModel D p NC (F.functor ⊗ X.functor)) (FF : GlobalNCModel D p NC F.functor)
    (NP : GlobalNCData GP FP) (NF : GlobalNCData G FF)
    [IsIso (DerivedCategory.Q.map
      ((shiftFunctor (Cochains (LargeScalar k)) (-d)).map (NF.comparison W)))] :
    NCIntegrationRepresentative FP FF d
      (globalIntegrationClass B.family.model B.absolute B.scalar B.gamma A projectionWeak W K η shift NP NF)

theorem_wanted actualGlobalKappaNaturality (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (RM : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q) (R : ProductReplacementSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (SL : StrongCochainLift L) (V : NerveLiftModel L)
    (F F' X : DerivedStack Q) (f : F'.functor ⟶ F.functor)
    (B : SourcedScalarFamily M U RM Q L V X.functor)
    (G : GlobalMixedModel D T F.functor) (G' : GlobalMixedModel D T F'.functor)
    (GP : GlobalMixedModel D T (F.functor ⊗ X.functor))
    (GP' : GlobalMixedModel D T (F'.functor ⊗ X.functor))
    (P : PureTensorModel G.mixed (gammaCoefficients B.family.model B.absolute B.scalar))
    (P' : PureTensorModel G'.mixed (gammaCoefficients B.family.model B.absolute B.scalar))
    (A : GlobalRelativeModel B.family.model B.absolute B.scalar B.gamma R SL G GP P)
    (A' : GlobalRelativeModel B.family.model B.absolute B.scalar B.gamma R SL G' GP' P')
    (weak : ∀ w : ℤ, QuasiIso (A.projection.map.map w))
    (weak' : ∀ w : ℤ, QuasiIso (A'.projection.map.map w))
    (pullback : MixedPullbackModel f G G')
    (productPullback : MixedPullbackModel (f ⊗ₘ 𝟙 X.functor) GP GP')
    (tensorPullback : PureTensorMap pullback.map (𝟙 _) P P') :
    (mixedQ (LargeScalar k)).map productPullback.map ≫
      globalKappa B.family.model B.absolute B.scalar B.gamma A' weak' =
    globalKappa B.family.model B.absolute B.scalar B.gamma A weak ≫
      (mixedQ (LargeScalar k)).map tensorPullback.map

theorem_wanted actualIntegrationUnderlyingSquare (R : Type u) [CommRing R]
    (p : ℤ) (N : NCCategoryModel R p) (E F : GradedMixed R) (C : Cochains R)
    (P : PureTensorModel F C) (κ : (mixedQ R).obj E ⟶ (mixedQ R).obj P.mixed)
    (B : Comparison P p (N.diagram.toModel F) (N.diagram.toModel P.mixed))
    [IsIso (DerivedCategory.Q.map B.map)] (d : ℤ)
    (trace : C ⟶ (𝟙_ (Cochains R))⟦-d⟧)
    (U : UnitTensorModel (N.diagram.complex.obj F) (-d)) (V : UnitTensorModel (F.weight p) (-d)) :
    integrateClass N P κ B trace U ≫
      DerivedCategory.Q.map ((shiftFunctor (Cochains R) (-d)).map
        (weightProjection (N.diagram.toModel F))) =
    DerivedCategory.Q.map (weightProjection (N.diagram.toModel E)) ≫
      integrateWeightClass p P κ trace V

end MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration
