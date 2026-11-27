/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels

/-!
# Native all-perfect-test Yoneda replacements and the actual RHom span

The restricted Yoneda functor is computed from the native DG Yoneda and
the restriction along the literal full perfect-test inclusion. Its
restriction source fixes every module value and every homogeneous module
component. A replacement diagram is augmented to that same whole functor,
and its modules are projectively cofibrant over the entire perfect-test
DG category. This retains the full action, rather than merely replacing
each coefficient value.

The two RHom legs come from the actual source DG augmentation and actual
replacement DG functor. Neither a desired geometric RHom isomorphism nor
a tangent formula is a field of the replacement input. The native source
and all-perfect-test projective-module Hom complexes are thus endpoints
of a fixed source-normalized span; comparison proofs remain Wanted.

References: Toen--Vaquie math/0503269v5, Section3.5 pp59--61; native
K-injective source cochains and the actual enriched DG/module primitives
at the revisions and licenses retained in the imported modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels

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
open MathlibExt.AlgebraicGeometry.GeometricPerfectTestModels

universe u

variable (O : ∀ Z : Scheme.{u}, EtaleStructureSource Z) [SourceTheory.{u}]
  (L : EtalePullbackSystem O)
  (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
  (R : ChartRestrictionSystem O)
  {X : SourceSpace.{u}} {A : CommRingCat.{u}}
  {π : X.sheaf ⟶ represented.obj (Spec A)} (S : ScalarLinearitySource A π)

/-- The actual full inclusion of native cofibrant modules retains their original module Hom complexes. -/
def cofibrantModulesToRaw (C : DGCat (LargeScalar A)) :
    EnrichedFunctor (Cochains (LargeScalar A))
      (DGDerivedModules (LargeScalar A) C) (RightModule (LargeScalar A) C) where
  obj M := M.obj
  map _ _ := 𝟙 _

variable (U : RestrictionModel (perfectIntoQCoh O L J R S))

/-- Native Yoneda followed by the prescribed homogeneous restriction to all actual perfect tests. -/
def restrictedYonedaFunctor :
    EnrichedFunctor (Cochains (LargeScalar A)) (qcohDGCategory O L J R S)
      (RightModule (LargeScalar A) (perfectDGCategory O L J R S)) :=
  (dgYoneda (LargeScalar A)).comp (Cochains (LargeScalar A)) U.functor

/-- Its original module object is the literal all-perfect-test geometric Yoneda module. -/
theorem restrictedYonedaFunctor_obj (E : qcohDGCategory O L J R S) :
    (restrictedYonedaFunctor O L J R S U).obj E = allPerfectTestsYoneda O L J R S E :=
  U.object_eq ((dgYoneda (LargeScalar A)).obj E)

/-- A derived module whose cohomology at every perfect test is `u`-small. Geometric Yoneda modules
have this property (their values are computed by `u`-small affine presentations), while the module
category over `LargeScalar A` also contains `u+1`-large modules, e.g. a direct sum of
representables indexed by `Cardinal.{u}`; these are not in the essential image. -/
def HasSmallCohomology (M : DGDerivedModules (LargeScalar A) (perfectDGCategory O L J R S)) :
    Prop :=
  ∀ (E : perfectDGCategory O L J R S) (n : ℤ),
    Small.{u} ((M.obj.toEnrichedFunctor.obj (op E)).homology n)

variable (Q : CofibrantReplacement (qcohDGCategory O L J R S))

/-- The actual indexed source functor, using the given native DG augmentation. -/
def augmentedRestrictedYoneda :
    EnrichedFunctor (Cochains (LargeScalar A)) Q.category
      (RightModule (LargeScalar A) (perfectDGCategory O L J R S)) :=
  Q.augmentation.comp (Cochains (LargeScalar A)) (restrictedYonedaFunctor O L J R S U)

/-- One augmented DG diagram of full perfect-test modules; no RHom comparison occurs in its inputs. -/
structure YonedaReplacementDiagram where
  functor : EnrichedFunctor (Cochains (LargeScalar A)) Q.category
    (DGDerivedModules (LargeScalar A) (perfectDGCategory O L J R S))
  augmentation : DGNatTrans
    (functor.comp (Cochains (LargeScalar A)) (cofibrantModulesToRaw (perfectDGCategory O L J R S)))
    (augmentedRestrictedYoneda O L J R S U Q)
  trivial : ∀ x : Q.category,
    IsModuleTrivialFibration
      ((DGFunctor.homEquivDGCycles (LargeScalar A) (functor.obj x).obj
        ((augmentedRestrictedYoneda O L J R S U Q).obj x)).symm
          ⟨augmentation.dgApp x, augmentation.dgApp_mem_dgCycles x⟩)

variable (D : YonedaReplacementDiagram O L J R S U Q)

/-- The actual projective module point retains the complete source augmentation on every perfect test. -/
def yonedaModuleReplacement (x : Q.category) :
    ModuleReplacement ((augmentedRestrictedYoneda O L J R S U Q).obj x) where
  module := (D.functor.obj x).obj
  augmentation :=
    (DGFunctor.homEquivDGCycles (LargeScalar A) (D.functor.obj x).obj
      ((augmentedRestrictedYoneda O L J R S U Q).obj x)).symm
        ⟨D.augmentation.dgApp x, D.augmentation.dgApp_mem_dgCycles x⟩
  cofibrant := (D.functor.obj x).property
  trivialFibration := D.trivial x

/-- The geometric leg is exactly the native DG augmentation on the complete source Hom complex. -/
def geometricRHomLeg (x y : Q.category) :
    dgHomComplex (LargeScalar A) x y ⟶
      dgHomComplex (LargeScalar A) (Q.augmentation.obj x).obj (Q.augmentation.obj y).obj :=
  Q.augmentation.map x y

/-- The actual geometric leg is a quasi-isomorphism by the source DG augmentation, in every degree. -/
theorem geometricRHomLeg_quasiIso (x y : Q.category) :
    QuasiIso (geometricRHomLeg O L J R S Q x y) := by
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_isIso_homologyMap (geometricRHomLeg O L J R S Q x y) n).mpr
    (EnrichedFunctor.IsQuasiFullyFaithful.isIso_homologyMap
      (EnrichedFunctor.IsQuasiEquivalence.isQuasiFullyFaithful Q.trivialFibration.2) x y n)

/-- The module leg is the actual replacement DG functor on the complete projective-module Hom complex. -/
def allPerfectTestRHomLeg (x y : Q.category) :
    dgHomComplex (LargeScalar A) x y ⟶
      dgHomComplex (LargeScalar A) (yonedaModuleReplacement O L J R S U Q D x).module
        (yonedaModuleReplacement O L J R S U Q D y).module :=
  D.functor.map x y

/-- This native derived endomorphism carrier is computed over the whole actual perfect-test module action. -/
def allPerfectTestDerivedEndomorphisms (x : Q.category) : Cochains (LargeScalar A) :=
  dgHomComplex (LargeScalar A) (yonedaModuleReplacement O L J R S U Q D x).module
    (yonedaModuleReplacement O L J R S U Q D x).module

end MathlibExt.AlgebraicGeometry.GeometricPerfectDGYonedaModels
