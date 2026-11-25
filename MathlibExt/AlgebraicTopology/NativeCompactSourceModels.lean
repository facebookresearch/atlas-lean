/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeKParametrizedSource
public import MathlibExt.AlgebraicTopology.StableInfinityFilteredColimits
public import MathlibExt.AlgebraicTopology.BGTContravariantPresheaves

/-!
# Actual compact spectra and compact stable-category source skeletons

Compactness is the existing native full coherent filtered-colimit test:
all cofinal cardinal-filtered index models, actual universal cocones,
and the canonical left-slice pullback comparison. Spomega is the full
subcategory of the actual spectrum infinity source satisfying this
test at aleph0. Its distinguished object is the native sphere module.

The perfect-category source is the coherent nerve of the original full
exact-functor-core enrichment, restricted by actual idempotent
completeness. Skeleton Homs are those same entire exact-functor cores.
Cardinality and compactness remain explicit, including the uncountable
regular cardinal used by the localizing construction.

Sources: BGT1001.2282v4 Sections2/5/7.2/8/9.1; HTT Section5.3;
HSS finite spectra. Native source pins and licenses remain in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeCompactSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityCategoryModels StableInfinityFilteredColimits
open StableSpectraInfinitySource NativeKParametrizedSource StableInfinitySParametrizedAction
open BGTContravariantPresheaves
open BGTVerdierQuotients
open StableInfinitySFunctorMaps
open scoped Simplicial Cardinal

/-- Actual compact spectra are tested inside the fixed native stable spectrum source. -/
def compactSpectra (S : SpectrumInfinitySource) : SSet.{1} :=
  (S.category.toSSet.fullEnhancedSubcategory (IsKappaCompactVertex ℵ₀ S.category.toSSet)).toSSet

/-- The actual entire compact-spectrum category has a genuine small perfect presentation. -/
structure CompactSpectraSource (S : SpectrumInfinitySource) where
  small : PerfectInfinityCategory.{0}
  comparison : (SSet.uliftFunctor : SSet.{0} ⥤ SSet.{1}).obj small.toStableInfinityCategory.toSSet ⟶ compactSpectra S
  weak : CategoricalWeakEquivalence comparison
  sphere : small.toStableInfinityCategory.toSSet _⦋0⦌
  sphere_normalization :
    (comparison ≫ (S.category.toSSet.fullEnhancedSubcategory
      (IsKappaCompactVertex ℵ₀ S.category.toSSet)).ι).app (op ⦋0⦌) (ULift.up sphere) = sphereVertex S

variable (A : StableCategoryEnrichment)

/-- The source is the complete original exact-functor-core coherent nerve. -/
def stableCategories : SSet.{1} :=
  letI := A.enrichment
  SimplicialNerve (ForgetEnrichment SSet.{0} StableInfinityCategory.{0})

def stableCategoryOfVertex (x : (stableCategories A) _⦋0⦌) : StableInfinityCategory.{0} :=
  letI := A.enrichment
  ForgetEnrichment.to SSet.{0}
    (SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{0} StableInfinityCategory.{0}) x)

def IsPerfectCategoryVertex (x : (stableCategories A) _⦋0⦌) : Prop := IsIdempotentComplete (stableCategoryOfVertex A x)

/-- All small perfect stable categories retain their actual full mapping spaces. -/
def perfectCategories : SSet.{1} := ((stableCategories A).fullEnhancedSubcategory (IsPerfectCategoryVertex A)).toSSet

def stableCategoryVertex (C : StableInfinityCategory.{0}) : (stableCategories A) _⦋0⦌ :=
  letI := A.enrichment
  (SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{0} StableInfinityCategory.{0})).symm
    (ForgetEnrichment.of SSet.{0} C)

def perfectCategoryVertex (C : PerfectInfinityCategory.{0}) : (perfectCategories A) _⦋0⦌ := by
  let x := stableCategoryVertex A C.toStableInfinityCategory
  refine ⟨x, (SSet.mem_fullEnhancedSubcategory_obj_zero_iff _ x).mpr ?_⟩
  change IsIdempotentComplete (stableCategoryOfVertex A x)
  have h : stableCategoryOfVertex A x = C.toStableInfinityCategory := by
    letI := A.enrichment
    simp only [x, stableCategoryVertex, stableCategoryOfVertex, Equiv.apply_symm_apply,
      ForgetEnrichment.to_of]
  rw [h]
  exact C.idempotentComplete

/-- The exact cardinal-compactness predicate is native, not a placeholder certificate. -/
def IsCompactPerfectCategory (k : Cardinal.{0}) (C : PerfectInfinityCategory.{0}) : Prop :=
  IsKappaCompactVertex k (perfectCategories A) (perfectCategoryVertex A C)

/-- A small source skeleton has the actual complete exact-functor Homs and all compact objects. -/
structure CompactStableSkeleton (k : Cardinal.{0}) where
  carrier : Type
  enrichment : EnrichedCategory SSet.{0} carrier
  representation : letI := A.enrichment; letI := enrichment
    EnrichedFunctor SSet.{0} carrier StableInfinityCategory.{0}
  perfect : letI := A.enrichment; letI := enrichment
    ∀ c : carrier, IsIdempotentComplete (representation.obj c)
  hom_normalization : letI := A.enrichment; letI := enrichment
    ∀ c d : carrier, (c ⟶[SSet.{0}] d) = ExactFunctorCore (representation.obj c) (representation.obj d)
  map_normalization : letI := A.enrichment; letI := enrichment
    ∀ c d : carrier, representation.map c d ≫
      eqToHom (A.hom_normalization (representation.obj c) (representation.obj d)) = eqToHom (hom_normalization c d)
  compact : letI := A.enrichment; letI := enrichment
    ∀ c : carrier, IsCompactPerfectCategory A k ⟨representation.obj c, perfect c⟩
  coverage : letI := A.enrichment; letI := enrichment
    ∀ C : PerfectInfinityCategory.{0}, IsCompactPerfectCategory A k C →
    ∃ c : carrier, EquivalentVertices (perfectCategories A) (perfectCategoryVertex A C)
      (perfectCategoryVertex A ⟨representation.obj c, perfect c⟩)

/-- BGT's K target is the entire full exact-functor infinity category, including noninvertible natural transformations. -/
structure FullExactFunctorInput (C : StableInfinityCategory.{0}) (D : PerfectInfinityCategory.{0}) where
  category : PerfectInfinityCategory.{0}
  normalized : category.toStableInfinityCategory.toSSet = exactFunctorCategory C D.toStableInfinityCategory

end MathlibExt.AlgebraicTopology.NativeCompactSourceModels
