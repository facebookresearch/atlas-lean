/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.StableSpectraInfinitySource
public import MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction
public import MathlibExt.AlgebraicGeometry.EnhancedPerfKModels

/-!
# Native stable-category, coherent S and spectrum source requests

These support and construction requests concern the prescribed native
mapping fibres, cone categories, whole S-diagrams, symmetric spectrum
localization and enriched perfect nerve. The K carrier, Ind/Sigma cone,
vanishing and universal motive comparisons are separate constructions
and theorem targets. No K or motive conclusion is assumed here.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Sections 2/4/7;
Lurie, Higher Topos Theory, Sections 1.2 and 2.2;
Hovey--Shipley--Smith, Symmetric spectra, Section 3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicTopology.StableInfinitySourcesWanted

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.StableInfinityMappingSpaces
open MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams
open MathlibExt.AlgebraicTopology.StableInfinityCategoryModels
open MathlibExt.AlgebraicTopology.StableInfinitySConstruction
open MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction
open MathlibExt.AlgebraicTopology.StableSpectraInfinitySource
open MathlibExt.AlgebraicGeometry.EnhancedPerfKModels
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open scoped Simplicial

universe u

/-- The native arrow-core fibre is the actual Kan mapping space. -/
theorem_wanted native_mapping_space_kan (C : SSet.{u}) [SSet.Quasicategory C]
    (x y : C _⦋0⦌) : SSet.KanComplex (mappingSpace C x y)

/-- Full native functor objects into a quasicategory remain quasicategories. -/
theorem_wanted native_functor_category_quasi (X Y : SSet.{u}) [SSet.Quasicategory Y] :
  SSet.Quasicategory (mapping X Y)

/-- The full actual coherent cone fibres are quasicategories. -/
theorem_wanted native_coherent_left_cones (I : Type) [Category.{0} I]
    (C : SSet.{u}) [SSet.Quasicategory C] (d : indexNerve I ⟶ C) :
  SSet.Quasicategory (leftCones C d)

/-- The full actual coherent cocone fibres are quasicategories. -/
theorem_wanted native_coherent_right_cones (I : Type) [Category.{0} I]
    (C : SSet.{u}) [SSet.Quasicategory C] (d : indexNerve I ⟶ C) :
  SSet.Quasicategory (rightCones C d)

/-- The stable source is formed from the native sphere-module category and actual generating maps. -/
def_wanted native_stable_spectra_infinity_source : SpectrumInfinitySource

/-- The whole specified perfect DG nerve is stable and idempotent complete. -/
def_wanted native_enhanced_perfect_input (k : Type u) [CommRing k]
    (A : DGCat k) (P : SmallPerfectModel A) : EnhancedPerfectInput P

/-- Native enriched perfect functors give the actual exact coherent-nerve maps. -/
theorem_wanted native_enhanced_perfect_functor_exact (k : Type u) [CommRing k]
    (A B : DGCat k) (P : SmallPerfectModel A) (Q : SmallPerfectModel B)
    (C : EnhancedPerfectInput P) (D : EnhancedPerfectInput Q)
    (F : EnrichedFunctor (Cochains k) P.category Q.category) : IsExactPerfectMap C D F

/-- The full actual S-level has its source stable structure, with fixed underlying diagrams. -/
def_wanted native_gap_stable_input (C : StableInfinityCategory.{u}) (n : ℕ) :
  {D : StableInfinityCategory.{u} // D.toSSet = gapCategory C n}

/-- Every coordinate in the full iterated S-level has the same source stable structure. -/
def_wanted native_multi_gap_stable_input (C : StableInfinityCategory.{u})
    (q : ℕ) (n : Fin q → ℕ) :
  {D : StableInfinityCategory.{u} // D.toSSet = multiGapCategory C q n}

/-- Source Lemma7.3 is a conclusion on the actual native spine map. -/
theorem_wanted native_gap_spine_equivalence (C : StableInfinityCategory.{u}) (n : ℕ) :
  CategoricalWeakEquivalence (gapSpineRestriction C n)

end WantedExt.AlgebraicTopology.StableInfinitySourcesWanted
