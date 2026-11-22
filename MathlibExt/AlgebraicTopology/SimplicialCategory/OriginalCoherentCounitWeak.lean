/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingRealizationWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentCounitComparisonCompositeWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveQuasicategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses

/-!
# The SAME original coherent counit is genuinely Dwyer--Kan weak

For an original enrichment with all original Hom objects Kan, its
actual coherent nerve is a quasicategory. The SAME original raw right-Q
comparison and actual counit composite are weak, so every original
counit Hom map is weak. Its original object map is the full original
vertex equivalence. No locally Kan raw realization is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

open SimplicialEnrichment

/-- The SAME original coherent counit is weak on its entire original Hom at both original enriched objects. -/
theorem counit_originalHom_weak (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) (x y : C) :
    SSet.realizationWeakEquivalences ((counit C).map
      (SSet.yonedaEquiv (HomSimplexEndpoints.vertex x))
      (SSet.yonedaEquiv (HomSimplexEndpoints.vertex y))) := by
  let _ : SSet.Quasicategory (coherentNerveFunctor.obj C) := coherentNerve_quasicategory C hKan
  let _ : SSet.KanComplex (x ⟶[SSet.{u}] y) := hKan x y
  exact SSet.realizationWeakEquivalences.of_precomp _ _
    (OriginalRawRightMapping.realizationComparison_weak (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y))
    (OriginalRawRightMapping.realizationComparison_counit_weak x y)

/-- The SAME original counit object map is the actual original vertex/object bijection. -/
theorem counit_objects_bijective (C : Carrier.{u}) : Function.Bijective (counit C).obj :=
  (verticesEquiv C).bijective

/-- EVERY complete original raw counit Hom map is weak, retaining every original coherent vertex. -/
theorem counit_localWeak (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) : EnrichedDwyerKan.localWeak (counit C) := by
  intro a b
  have ha : SSet.yonedaEquiv (HomSimplexEndpoints.vertex (vertexOf C a)) = a :=
    (Equiv.apply_symm_apply (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C))
      (constantSimplex C ⦋0⦌ (vertexOf C a))).trans (constant_vertexOf C a)
  have hb : SSet.yonedaEquiv (HomSimplexEndpoints.vertex (vertexOf C b)) = b :=
    (Equiv.apply_symm_apply (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C))
      (constantSimplex C ⦋0⦌ (vertexOf C b))).trans (constant_vertexOf C b)
  exact ha ▸ hb ▸ counit_originalHom_weak C hKan (vertexOf C a) (vertexOf C b)

/-- The SAME actual original coherent evaluation counit is genuinely Dwyer--Kan weak for every original locally Kan
enrichment. -/
theorem counit_DKweak (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    EnrichedDwyerKan.weakEquivalences (counit C) :=
  ⟨counit_localWeak C hKan, Functor.essSurj_of_surj (counit_objects_bijective C).surjective⟩

end CategoryTheory.CoherentRealization
