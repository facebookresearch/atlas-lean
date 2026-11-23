/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels

/-!
# Source constructions for the native all-perfect-test geometric Yoneda

The source is a fixed affine test of an actual proper, flat,
finitely-presented algebraic-space situation. Its native structure ring,
every chart restriction, every homogeneous module map and the full
coefficient Hom complexes are already prescribed by the public models.

The projective diagram is augmented to the literal all-perfect-test
Yoneda module. Its comparison to geometric RHom is a proof result,
rather than a field of an independent input. Absolute perfection,
pseudo-perfection and relative perfection remain separate predicates.

References: Toen--Vaquie math/0503269v5, Section3.5 pp59--61 and
Remark3.30(2), the cited compact-generation/restricted-Yoneda background;
Stacks 03G8/06YY and the actual proper small-etale source at
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b. Extension to
the stated native algebraic-space source is explicit adaptation work.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeometricPerfectTestsWanted

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels
open MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels

universe u

attribute [local instance] HasDerivedCategory.standard

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
  (L : EtalePullbackSystem O)
  (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
  (R : ChartRestrictionSystem O)
  (D : ProperSpaceSituation.{u}) (T : AffineProperFamily D)
  (S : ScalarLinearitySource T.ring (affineProperProjection D T))

/-- Construct a small model of all actual native perfect tests, with the complete lifted Hom comparison. -/
def_wanted native_small_perfect_test_model (C : CochainLiftModel T.ring) :
  SmallPerfectTestModel O L J R S C

/-- Native enriched restriction fixes every original module value and every homogeneous component. -/
def_wanted native_all_perfect_tests_restriction :
  RestrictionModel (perfectIntoQCoh O L J R S)

variable (U : RestrictionModel (perfectIntoQCoh O L J R S))
  (Q : CofibrantReplacement (qcohDGCategory O L J R S))

/-- Construct one augmented projective diagram over the entire actual perfect-test DG action. -/
def_wanted native_all_perfect_tests_yoneda_replacement :
  YonedaReplacementDiagram O L J R S U Q

variable (P : YonedaReplacementDiagram O L J R S U Q)

/-- Every original geometric Hom is compared through the fixed native projective-module RHom leg. -/
theorem_wanted native_all_perfect_tests_rhom_comparison (x y : Q.category) :
  QuasiIso (allPerfectTestRHomLeg O L J R S U Q P x y)

/-- Essential surjectivity of the derived Yoneda functor onto the modules with `u`-small
cohomology; with `native_all_perfect_tests_rhom_comparison` (full faithfulness) this is the
all-perfect-test derived Yoneda equivalence onto those modules. The whole module category over
`LargeScalar A` is not reached: it contains `u+1`-large modules (`HasSmallCohomology`). -/
theorem_wanted native_all_perfect_tests_yoneda_small_essential_image
    (M : DGDerivedModules (LargeScalar T.ring) (perfectDGCategory O L J R S))
    (_hM : HasSmallCohomology O L J R S M) :
  ∃ x : Q.category, Nonempty (DGHomotopyCategory.of (LargeScalar T.ring) (P.functor.obj x) ≅
    DGHomotopyCategory.of (LargeScalar T.ring) M)

/-- Proper flat source geometry makes every absolute perfect complex pseudo-perfect on every actual test. -/
theorem_wanted native_proper_perfect_is_pseudo_perfect
    (E : perfectDGCategory O L J R S) :
  IsSourcePseudoPerfect O L J R S ((perfectIntoQCoh O L J R S).obj E)

/-- Smooth source geometry supplies the opposite implication; it is not asserted for singular proper sources. -/
theorem_wanted native_smooth_pseudo_perfect_is_perfect
    (smooth : ∀ C : EtaleChart (familySpace D T.test),
      Smooth (chartStructuralMap (affineProperProjection D T) C))
    (E : qcohDGCategory O L J R S) (h : IsSourcePseudoPerfect O L J R S E) :
  IsSourcePerfect O L J R (DerivedCategory.Q.obj E.obj)

end WantedExt.AlgebraicGeometry.GeometricPerfectTestsWanted
