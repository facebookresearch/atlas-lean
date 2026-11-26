/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentIntervalFaceCover
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomObjects

/-!
# Actual composition of coherent whole-interval face comparisons

Composed embeddings cover the original endpoint interval when each of
its two actual embeddings covers its corresponding interval. The whole
Hom maps and their genuine isomorphisms compose by the original coherent
simplex direct-image operator, with all original scalar simplices kept.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.WholeFaceComposition
open OrderEmbeddingFace IntervalFaceCover SimplicialEnrichment
variable {J K L : Type u} [LinearOrder J] [LinearOrder K] [LinearOrder L]
  (d : J ↪o K) (e : K ↪o L) (a b : J)

/-- The original whole coherent Hom direct-image maps compose by the same actual order embedding. -/
theorem imageMap_comp :
    imageMap d a b ≫ imageMap e (d a) (d b) = imageMap (d.comp e) a b := by
  have h := enriched_map_of_eq
    (C := of (SimplicialThickening J)) (D := of (SimplicialThickening L))
    (SimplicialThickening.functor_comp d.toOrderHom e.toOrderHom) (.mk a) (.mk b)
  change imageMap (d.comp e) a b ≫ 𝟙 _ = imageMap d a b ≫ imageMap e (d a) (d b) at h
  exact h.symm.trans (Category.comp_id _)

variable
  (hd : ∀ x : K, d a ≤ x → x ≤ d b → x ∈ Set.range d)
  (he : ∀ x : L, e (d a) ≤ x → x ≤ e (d b) → x ∈ Set.range e)

include hd he in
/-- Two actual interval coverages imply coverage by the original composite embedding. -/
theorem composite_coverage (x : L) (ha : (d.comp e) a ≤ x) (hb : x ≤ (d.comp e) b) :
    x ∈ Set.range (d.comp e) := by
  obtain ⟨y, rfl⟩ := he x ha hb
  obtain ⟨z, rfl⟩ := hd y (e.le_iff_le.mp ha) (e.le_iff_le.mp hb)
  exact ⟨z, rfl⟩

/-- The original whole Hom isomorphisms compose to the genuine isomorphism of the same composed interval face. -/
theorem wholeHomIso_comp :
    (wholeHomIso d a b hd).hom ≫ (wholeHomIso e (d a) (d b) he).hom =
      (wholeHomIso (d.comp e) a b (composite_coverage d e a b hd he)).hom := by
  rw [wholeHomIso_hom, wholeHomIso_hom, wholeHomIso_hom]
  exact imageMap_comp d e a b

end CategoryTheory.CoherentRealization.WholeFaceComposition
