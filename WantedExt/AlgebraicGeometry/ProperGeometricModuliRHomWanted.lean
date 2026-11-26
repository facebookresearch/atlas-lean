/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
public import MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomNativeLargeModuleEndomorphismIsomorphism

/-!
# Source construction and RHom requests for the actual proper DG-moduli point

The original DG-moduli point, its complete uncurried T/coefficient action
and its projective enveloping-module replacement are fixed inputs. The
geometric functor is normalized against every actual native perfect
test, every homogeneous source/target map and every coefficient action
on the original etale-chart sections. Point construction requests a weak
map between those actual projective modules. The geometric RHom
comparison uses only the computed span of those maps.

References: Toen--Vaquie math/0503269v5, Sections3.1/3.3/3.5 and the
restricted-Yoneda/derived tensor background cited there. Native
proper-flat-finitely-presented algebraic-space source adaptation is
explicit work, at Stacks03G8/06YY/0DLD/0DLE and AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b. No unrestricted equivalence
with absolute perfect complexes on a singular proper source is stated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProperGeometricModuliRHomWanted

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels
open MathlibExt.AlgebraicGeometry.ProperGeometricCoefficientFamilies
open MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
open MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomModels
open scoped Simplicial

universe u

/-- The native coefficient lift preserves every original full projective-module value and action. -/
def_wanted native_large_projective_module_lift (k : Type u) [CommRing k]
    (UL : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)
    (h : IsCofibrantModule M) : LargeProjectiveModuleLift UL T M

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
  (L : EtalePullbackSystem O)
  (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
  (C : ChartRestrictionSystem O)
  (D : ProperSpaceSituation.{u}) (B : AffineProperFamily D)
  (SB : ScalarLinearitySource B.ring (affineProperProjection D B))
  (UL : CochainLiftModel B.ring)
  (T : SmallPerfectTestModel O L J C SB UL)
  (F : DGFrame B.ring (oppositeCategory T.category))

/-- Construct the original actual zero-frame perfect-test functor, fixing all objects and all homogeneous cochains. -/
def_wanted native_augmented_perfect_frame_tests : NativeFramePerfectTests O L J C D B SB UL T F

variable {N : ShuffleAlgebraFunctor B.ring} {S : AffineScalarSystem N}
  (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} B.ring)
  (Q : PullbackSystem.{u}) (FB : NativeFramePerfectTests O L J C D B SB UL T F)
  (SA : ScalarLinearitySource B.ring (baseCoefficientProjection D B A))
  (R : RawPullbackDGSource Q (coefficientSourceMap D B A) B.ring
    (affineProperProjection D B) (baseCoefficientProjection D B A) SB SA)

/-- Resolve the same entire native perfect-test DG diagram before applying the actual X_A inverse image. -/
def_wanted native_coefficient_perfect_test_pullback
    (h : IsCofibrant (frameTestCategory UL F)) :
  TestPullbackDGSource R (frameTestCategory UL F) FB.functor

variable (V : TestPullbackDGSource R (frameTestCategory UL F) FB.functor)

/-- Construct the geometric enveloping module with literal test Hom values, coefficient actions and all target Hom maps. -/
def_wanted native_geometric_enveloping_yoneda :
  GeometricEnvelopingYoneda O L J C D B SB UL T F (N := N) A Q FB SA R V

variable (Y : GeometricEnvelopingYoneda O L J C D B SB UL T F (N := N) A Q FB SA R V)
  (I : CofibrantReplacement (qcohDGCategory O L J C SA))

/-- Construct one full projective diagram augmented to that same native geometric enveloping functor. -/
def_wanted native_geometric_projective_module_diagram :
  EnrichedModuleReplacementDiagram (qcohDGCategory O L J C SA)
    (largeOrdinaryEnvelope UL F N A) Y.functor I

variable (Z : EnrichedModuleReplacementDiagram (qcohDGCategory O L J C SA)
    (largeOrdinaryEnvelope UL F N A) Y.functor I)
  {E : ((underivedModuliFunctor F P).obj A) _⦋0⦌}
  (M : ModulePointModel F P (ordinaryAlgebras.obj A) E)
  (ML : LargeProjectiveModuleLift UL (ordinaryEnvelope F N A) M.replacement.module)

/-- Construct the geometric point from the actual full uncurried/projective DG-moduli module, with its native weak comparison. -/
def_wanted native_proper_geometric_moduli_point :
  GeometricModuliPoint O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z

variable (G : GeometricModuliPoint O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z)

/-- The actual weak point comparison induces the fixed target-Hom quasi-isomorphism from a projective source. -/
theorem_wanted native_point_module_post_hom_quasi_isomorphism :
  QuasiIso (pointModulePostHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)

/-- Its actual source-Hom comparison is a quasi-isomorphism between the same projective modules. -/
theorem_wanted native_point_module_pre_hom_quasi_isomorphism :
  QuasiIso (pointModulePreHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)

/-- The actual all-perfect-test enveloping Yoneda replacement identifies this same geometric Hom complex. -/
theorem_wanted native_point_geometric_module_hom_quasi_isomorphism :
  QuasiIso (pointGeometryModuleHomLeg O L J C D B SB UL T F P A Q FB SA R V M ML Y I Z G)

end WantedExt.AlgebraicGeometry.ProperGeometricModuliRHomWanted
