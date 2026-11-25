/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources

/-!
# Wanted adapters for the actual proper algebraic-space complex source

These requests adapt the positively implemented native small étale,
relative-perfect and derived-pullback source to the existing actual
étale-quotient presentations. They do not classify general T-actions
by unrestricted ordinary complexes. Geometric Yoneda/moduli comparison
and its equivalence remain separate source bindings and proof goals.

Every ring, chart, tensor test, inverse-image unit and graded Hom map
is fixed by its public native/source-normalized contract.
References: Stacks 03G8, 06YY, 0DKN, 0DKR, 0DLD and 0DLE;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.ProperComplexFamilySources
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
open MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
open MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations
open MathlibExt.AlgebraicGeometry.SpaceGeometricDGHomSources

universe u

/-- Supply native sheafification/Γ-ring sheaf proofs on the actual space chart site. -/
def_wanted native_algebraic_space_site_source (X : SourceSpace.{u}) : SiteSource X

/-- Adapt the native small étale source for all actual quotient spaces. -/
def_wanted native_algebraic_space_source_theory : SourceTheory.{u}

/-- Construct the inverse image representing all actual chart-square semilinear maps. -/
def_wanted native_algebraic_space_module_pullback (X Y : SourceSpace.{u})
    [SiteSource X] [SiteSource Y] (f : X ⟶ Y) : ModulePullbackSource f

/-- The prescribed source module inverse image has its native total left derivation. -/
theorem_wanted native_algebraic_space_pullback_derivation (X Y : SourceSpace.{u})
    [SiteSource X] [SiteSource Y] (f : X ⟶ Y) (P : ModulePullbackSource f) :
  DerivedPullbackSource P

/-- Assemble actual module/derived source inverse images on every space morphism. -/
def_wanted native_algebraic_space_pullback_system [SourceTheory.{u}] : PullbackSystem.{u}

/-- Adapt the completed native fibre-product source to a presentation of this exact pullback sheaf. -/
def_wanted native_space_fibre_presentation (X Y : SourceSpace.{u}) (f : X ⟶ Y)
    (T : Scheme.{u}) (g : represented.obj T ⟶ Y.sheaf) : SpaceModel (pullback (sheafMap f) g)

/-- Construct the actual source chart inclusion and exact Γ-module restriction. -/
def_wanted native_space_chart_restriction (O : ∀ S : Scheme.{u}, EtaleStructureSource S)
    (X : SourceSpace.{u}) [SiteSource X] (U : EtaleChart X) : ChartRestrictionSource O U

/-- Assemble the same source restriction on every actual chart and every scheme test. -/
def_wanted native_space_chart_restriction_system
    (O : ∀ S : Scheme.{u}, EtaleStructureSource S) [SourceTheory.{u}] : ChartRestrictionSystem O

/-- Source pseudo-coherence yields an actual bounded-above finite-projective affine resolution. -/
def_wanted native_pseudo_coherent_affine_resolution (B : CommRingCat.{u})
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (h : IsPseudoCoherentComplex B K) :
  PseudoCoherentResolution B K

/-- Adapt the native pseudo-coherent/finite-Tor criterion to the exact bounded-flat affine presentation. -/
theorem_wanted native_relative_perfect_affine_criterion (A B : CommRingCat.{u}) (α : A ⟶ B)
    (hflat : RingHom.Flat α.hom) (K : CochainComplex (ModuleCat.{u} B) ℤ) :
  IsCanonicalRelativePerfect α hflat K ↔ HasRelativePerfectPresentation α K

/-- Both space criteria use the same native X_T object, actual chart restrictions and native A-Tor complexes. -/
theorem_wanted native_space_relative_perfect_criterion
    (O : ∀ S : Scheme.{u}, EtaleStructureSource S) [SourceTheory.{u}]
    (L : EtalePullbackSystem O) (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (R : ChartRestrictionSystem O) (D : ProperSpaceSituation.{u})
    (T : MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies.FamilyTest D) (E : Derived (familySpace D T)) :
  MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations.IsCanonicalRelativelyPerfect L J R D T E ↔
    MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations.IsRelativelyPerfect L J R D T E

/-- Both native conditions are preserved by actual derived inverse image under the same X_h. -/
theorem_wanted native_space_complexes_pullback_preserves
    (O : ∀ S : Scheme.{u}, EtaleStructureSource S) [SourceTheory.{u}]
    (P : PullbackSystem.{u}) (L : EtalePullbackSystem O)
    (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A) (R : ChartRestrictionSystem O)
    (D : ProperSpaceSituation.{u}) (T T' : MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies.FamilyTest D) (h : T ⟶ T') :
  MathlibExt.AlgebraicGeometry.SpaceComplexAffinePresentations.ComplexesPullbackSource P L J R h

/-- The general scheme source is preserved without an absolute-perfect restriction. -/
theorem_wanted native_scheme_complexes_pullback_preserves
    (O : ∀ S : Scheme.{u}, EtaleStructureSource S) (L : EtalePullbackSystem O)
    (J : ∀ A : CommRingCat.{u}, AffineEtaleModuleSource O A)
    (D : ProperComplexesSituation.{u}) (T T' : MathlibExt.AlgebraicGeometry.ProperComplexFamilySources.FamilyTest D) (h : T ⟶ T') :
  MathlibExt.AlgebraicGeometry.ProperComplexFamilySources.ComplexesPullbackSource L J h

/-- Source linearity is fixed by every actual Γ chart action, including its coefficient-ring unit. -/
def_wanted native_space_scalar_linearity (X : SourceSpace.{u}) [SiteSource X]
    (A : CommRingCat.{u}) (π : X.sheaf ⟶ represented.obj (Spec A)) : ScalarLinearitySource A π

/-- Resolve this same actual geometric derived object in the native small étale module category. -/
def_wanted native_space_kinjective_model (X : SourceSpace.{u}) [SiteSource X] (E : Derived X) :
  KInjectiveSource E

/-- The raw DG functor preserves every native homogeneous cochain of the actual module inverse image. -/
def_wanted native_space_raw_dg_pullback [SourceTheory.{u}] (P : PullbackSystem.{u})
    (X Y : SourceSpace.{u}) (f : X ⟶ Y) (A : CommRingCat.{u})
    (πY : Y.sheaf ⟶ represented.obj (Spec A)) (πX : X.sheaf ⟶ represented.obj (Spec A))
    (SY : ScalarLinearitySource A πY) (SX : ScalarLinearitySource A πX)
    (h : sheafMap f ≫ πY = πX) : RawPullbackDGSource P f A πY πX SY SX

/-- A cofibrant whole test diagram has augmented native source and K-injective target pullback models. -/
def_wanted native_space_test_dg_pullback [SourceTheory.{u}] (P : PullbackSystem.{u})
    (X Y : SourceSpace.{u}) (f : X ⟶ Y) (A : CommRingCat.{u})
    (πY : Y.sheaf ⟶ represented.obj (Spec A)) (πX : X.sheaf ⟶ represented.obj (Spec A))
    (SY : ScalarLinearitySource A πY) (SX : ScalarLinearitySource A πX)
    (F : RawPullbackDGSource P f A πY πX SY SX)
    (D : DGCat (LargeScalar A)) (hcof : IsCofibrant D)
    (G : EnrichedFunctor (Cochains (LargeScalar A)) D (geometricDG SY)) : TestPullbackDGSource F D G
