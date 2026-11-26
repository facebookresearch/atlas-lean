/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOrdinalFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace

/-!
# Coherent zero and composition faces under embeddings

Order embeddings act on the path subsets by direct image. The
positive and negative face maps retain their supplied middle or omitted
vertex. The positive-face product comparison commutes with the 
enriched composition and its two Hom maps. These are 
scalar equations, not compatibility certificates.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FacesNaturality
open CompositionFace OrderEmbeddingFace
variable {J K : Type u} [LinearOrder J] [LinearOrder K] (e : J ↪o K) (i j k : J)

/-- Direct image of the same coherent positive-face path chain. -/
def positiveMap : (positive i j k : SSet.{u}) ⟶ positive (e i) (e j) (e k) where
  app q := ↾fun p => ⟨(imageMap e i k).app q p.val, fun t => ⟨j, p.property t, rfl⟩⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congr($((imageMap e i k).naturality f) p.val)

/-- The positive-face embedding followed by inclusion is the Hom
direct-image map. -/
theorem positiveMap_ι : positiveMap e i j k ≫ (positive (e i) (e j) (e k)).ι =
    (positive i j k).ι ≫ imageMap e i k := rfl

/-- The coherent Hom direct images preserve the union-composition map. -/
theorem imageMap_composition :
    CompositionFace.composition i j k ≫ imageMap e i k =
      (imageMap e i j ⊗ₘ imageMap e j k) ≫ CompositionFace.composition (e i) (e j) (e k) :=
  (SimplicialThickening.functor e.toOrderHom).map_comp (.mk i) (.mk j) (.mk k)

/-- Both positive-face comparisons are natural for the same embedding and
Hom legs. -/
theorem positiveIso_naturality :
    (positiveIso i j k).hom ≫ positiveMap e i j k =
      (imageMap e i j ⊗ₘ imageMap e j k) ≫ (positiveIso (e i) (e j) (e k)).hom := by
  apply (cancel_mono (positive (e i) (e j) (e k)).ι).mp
  rw [Category.assoc, positiveMap_ι, ← Category.assoc, positiveIso_composition,
    Category.assoc, positiveIso_composition]
  exact imageMap_composition e i j k

/-- Direct image of the omitted-vertex path chain, with the same omitted
vertex image. -/
def negativeMap : (HomBoxDecomposition.negative i j k : SSet.{u}) ⟶
    HomBoxDecomposition.negative (e i) (e j) (e k) where
  app q := ↾fun p => ⟨(imageMap e i k).app q p.val, fun t h => by
    obtain ⟨x, hx, he⟩ := h
    have hxy : x = j := e.injective he
    subst x
    exact p.property t hx⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact congr($((imageMap e i k).naturality f) p.val)

/-- The negative-face embedding followed by inclusion reads back the same 
Hom direct image. -/
theorem negativeMap_ι : negativeMap e i j k ≫ (HomBoxDecomposition.negative (e i) (e j) (e k)).ι =
    (HomBoxDecomposition.negative i j k).ι ≫ imageMap e i k := rfl

end CategoryTheory.CoherentRealization.FacesNaturality
