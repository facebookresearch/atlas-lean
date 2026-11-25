/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProperOrdinaryCoefficientTransport

/-!
# Source requests for native ordinary geometric moduli realization

The construction outputs are full native module/cochain/source diagrams
with actual units and derived counit normalizations. Ordinary
equivalence concerns the computed fundamental-groupoid comparison on
the exact relative-perfect/no-negative-fibre-Ext locus, and explicitly
requires actual smooth proper source maps.

Proper-flat gives perfect to pseudo-perfect over the COEFFICIENT ring.
The converse requires smoothness. Neither an unrestricted M_T(A)
groupoid equality nor a supplied geometric/RHom comparison is assumed.

Source: Toën--Vaquié arXiv:math/0503269v5 Section 3.5 pp.59--61,
Remark 3.30(2); Stacks 03G8/06YY/0DLD/0DLE. Genuine proofs remain
direct Batteries ProofWanted; provider theory completion is not a gate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProperOrdinaryRealizationWanted

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
open MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DGFrameAllSimplexUnits
open MathlibExt.AlgebraicGeometry.ProperOrdinaryModuleRealization
open MathlibExt.AlgebraicGeometry.ProperOrdinaryGlueableRealization
open MathlibExt.AlgebraicGeometry.ProperOrdinaryCoefficientTransport
open MathlibExt.AlgebraicGeometry.SpaceCoefficientPullbackCoherence
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
attribute [local instance] HasDerivedCategory.standard

/-- Construct all original simplex/envelope/common-degeneracy units and canonical coefficient restrictions together. -/
def_wanted native_moduli_simplex_module_sources (k : Type u) [CommRing k]
    (T : DGCat k) (F : DGFrame k (oppositeCategory T))
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) (P : StrictPerfectSystem N S)
    (A : CommAlgCat.{u} k) : ModuliSimplexModuleSources F P A

/-- Construct the prescribed all-chart/cochain/total-left-derived source coherence, with no output comparison input. -/
def_wanted native_space_pullback_coherence [SourceTheory.{u}] (P : PullbackSystem.{u}) :
    SpacePullbackCoherence P

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (C : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)
    (SB : ScalarLinearitySource B.ring (affineProperProjection D B)) (UL : CochainLiftModel B.ring)
    (T : SmallPerfectTestModel O L J C SB UL) (F : DGFrame B.ring (oppositeCategory T.category))
    {N : ShuffleAlgebraFunctor B.ring} {S : AffineScalarSystem N} (P : StrictPerfectSystem N S)
    (Q : PullbackSystem.{u}) (FB : NativeFramePerfectTests O L J C D B SB UL T F)

/-- Realize all actual full enveloping modules by a native DG quasi-functor roof and complete Yoneda comparison. -/
def_wanted native_ordinary_module_realization (A : CommAlgCat.{u} B.ring) :
    Σ G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A,
      OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G

/-- The triangle proof concerns the computed same-unit span images and native two-simplex, not arbitrary edge maps. -/
def_wanted native_ordinary_realization_triangles (A : CommAlgCat.{u} B.ring)
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (M : ModuliSimplexModuleSources F P A) :
    OrdinaryRealizationTriangles O L J C D B SB UL T F P Q FB A G R M

/-- Full geometric RHom is compared on the already computed native all-module DG roof, not supplied as an endpoint. -/
theorem_wanted native_ordinary_geometric_realization_rHom_quasiIso (A : CommAlgCat.{u} B.ring)
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (x y : R.roof.source.category) :
    QuasiIso (geometricRealizationRHomLeg O L J C D B SB UL T F Q FB A R x y)

/-- The exact ordinary comparison is an equivalence on the actual locus under smooth and proper source hypotheses. -/
theorem_wanted native_smooth_proper_ordinary_glueable_equivalence
    (smooth : IsSmoothProperSource D) (A : CommAlgCat.{u} B.ring)
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (M : ModuliSimplexModuleSources F P A)
    (H : OrdinaryRealizationTriangles O L J C D B SB UL T F P Q FB A G R M) :
    (complexesGroupoidComparison O L J C D B SB UL T F P Q FB A G R M H).IsEquivalence

/-- The coefficient source is the actual scalar extension plus full native geometric pullback/counit roof. -/
def_wanted native_ordinary_coefficient_transport {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A')
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (G' : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A')
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (R' : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A' G') :
    OrdinaryCoefficientTransport O L J C D B SB UL T F Q FB f G G' R R'

/-- Relative perfection and universal negative field Ext are preserved by the actual native X_f derived inverse image. -/
theorem_wanted native_complexes_coefficient_pullback {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A') :
    MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations.ComplexesPullbackSource Q L J C (coefficientArrow D B f)

/-- The complete native coefficient diagram transports the actual locus of the SAME realized source objects. -/
theorem_wanted native_glueable_coefficient_preservation {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A')
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (G' : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A')
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (R' : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A' G')
    (H : OrdinaryCoefficientTransport O L J C D B SB UL T F Q FB f G G' R R')
    (M : ModuliSimplexModuleSources F P A) (M' : ModuliSimplexModuleSources F P A') :
    ∀ e : ((underivedModuliFunctor F P).obj A) _⦋0⦌,
      IsGlueableVertex O L J C D B SB UL T F P Q FB A G R M e →
      IsGlueableVertex O L J C D B SB UL T F P Q FB A' G' R' M'
        (((underivedModuliFunctor F P).map f).app (op ⦋0⦌) e)

/-- Naturality compares the computed full module-unit groupoid map and actual source X_f pullback.
The native module extension and both geometric counit diagrams are supplied as source data, not the result. -/
def_wanted native_ordinary_groupoid_coefficient_comparison {A A' : CommAlgCat.{u} B.ring} (f : A ⟶ A')
    (G : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A)
    (G' : OrdinaryCoefficientGeometry O L J C D B SB UL T F (N := N) Q FB A')
    (R : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A G)
    (R' : OrdinaryModuleRealization O L J C D B SB UL T F Q FB A' G')
    (H : OrdinaryCoefficientTransport O L J C D B SB UL T F Q FB f G G' R R')
    (M : ModuliSimplexModuleSources F P A) (M' : ModuliSimplexModuleSources F P A')
    (J0 : OrdinaryRealizationTriangles O L J C D B SB UL T F P Q FB A G R M)
    (J1 : OrdinaryRealizationTriangles O L J C D B SB UL T F P Q FB A' G' R' M')
    (L0 : MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations.ComplexesPullbackSource Q L J C (coefficientArrow D B f))
    (preserves : ∀ e : ((underivedModuliFunctor F P).obj A) _⦋0⦌,
      IsGlueableVertex O L J C D B SB UL T F P Q FB A G R M e →
      IsGlueableVertex O L J C D B SB UL T F P Q FB A' G' R' M'
        (((underivedModuliFunctor F P).map f).app (op ⦋0⦌) e)) :
    complexesGroupoidComparison O L J C D B SB UL T F P Q FB A G R M J0 ⋙
      MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations.complexesPullback L0 ≅
    glueableCoefficientGroupoidMap O L J C D B SB UL T F Q FB f G G' R R' M M' preserves ⋙
      complexesGroupoidComparison O L J C D B SB UL T F P Q FB A' G' R' M' J1

/-- The actual X_A source stays proper and flat; coefficient pseudo-perfection is measured over A. -/
theorem_wanted native_proper_flat_perfect_to_pseudoPerfect (A : CommAlgCat.{u} B.ring)
    (SA : ScalarLinearitySource (ordinaryRing A) (coefficientProjection D B A))
    (E : qcohDGCategory O L J C SA)
    (perfect : IsSourcePerfect O L J C (DerivedCategory.Q.obj
      (show CochainComplex (Modules (coefficientSpace D B A)) ℤ from E.obj))) :
    IsSourcePseudoPerfect O L J C SA E

/-- Smoothness supplies the opposite direction for the same all-perfect-test A-linear criterion. -/
theorem_wanted native_smooth_pseudoPerfect_to_perfect (smooth : IsSmoothProperSource D)
    (A : CommAlgCat.{u} B.ring) (SA : ScalarLinearitySource (ordinaryRing A) (coefficientProjection D B A))
    (E : qcohDGCategory O L J C SA) (pseudo : IsSourcePseudoPerfect O L J C SA E) :
    IsSourcePerfect O L J C (DerivedCategory.Q.obj
      (show CochainComplex (Modules (coefficientSpace D B A)) ℤ from E.obj))

end WantedExt.AlgebraicGeometry.ProperOrdinaryRealizationWanted
