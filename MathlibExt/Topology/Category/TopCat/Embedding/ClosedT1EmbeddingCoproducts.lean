/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits

/-!
# Disjoint unions of closed T1-embeddings

A closed T1-embedding is a closed embedding such that every codomain point outside its image has
a closed singleton. A disjoint union of maps with this property retains it: the map sends (i,x)
to (i,fᵢ(x)), and the outside-image singleton condition holds component by component.

The component-space universe u and index universe v are independent. Their disjoint unions have
carrier universe max(u,v).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Topology

namespace Topology

variable {ι : Type v} {α β : ι → Type u} [∀ i, TopologicalSpace (α i)]
  [∀ i, TopologicalSpace (β i)] {f : ∀ i, α i → β i}

/-- For families of topological spaces αᵢ,βᵢ in universe u indexed in universe v, assume each
fᵢ:αᵢ→βᵢ is a closed embedding and all codomain singletons outside its image are closed. Then
(i,x)↦(i,fᵢ(x)) is a closed T1-embedding of the disjoint unions. -/
theorem IsClosedT1Embedding.sigmaMap (hf : ∀ i, IsClosedT1Embedding (f i)) :
    IsClosedT1Embedding (Sigma.map (fun i : ι => i) f) := by
  refine ⟨IsClosedEmbedding.sigmaMap (fun i => (hf i).toIsClosedEmbedding), ?_⟩
  intro p hp
  rcases p with ⟨i, y⟩
  have h_notMem : y ∉ Set.range (f i) := by
    intro hy_mem
    obtain ⟨x, hx⟩ := hy_mem
    have h_mem : (⟨i, y⟩ : Σ i, β i) ∈ Set.range (Sigma.map (fun i : ι => i) f) := by
      exact ⟨⟨i, x⟩, by simp [Sigma.map_mk, hx]⟩
    exact hp h_mem
  have h_closed_y : IsClosed ({y} : Set (β i)) :=
    (hf i).isClosed_singleton_of_notMem_range y h_notMem
  have h_eq : (Sigma.mk (β := β) i '' {y} : Set (Σ i, β i)) = {⟨i, y⟩} := by
    ext q
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, hq⟩
      have hx_eq : x = y := (Set.mem_singleton_iff.mp hx)
      subst hx_eq
      exact hq.symm
    · intro hq
      subst hq
      exact ⟨y, rfl, rfl⟩
  have h_closed_image : IsClosed (Sigma.mk i '' {y} : Set (Σ i, β i)) :=
    isClosedMap_sigmaMk _ h_closed_y
  rw [h_eq] at h_closed_image
  exact h_closed_image

end Topology

namespace TopCat

variable {J : Type v} {X Y : J → TopCat.{u}} {f : ∀ j, X j ⟶ Y j}

private lemma sigmaMap_closedT1Embedding_of_forall (hf : ∀ j, TopCat.closedT1Embeddings (f j)) :
    Topology.IsClosedT1Embedding (Sigma.map (fun j : J => j) (fun j => (f j).hom)) :=
  Topology.IsClosedT1Embedding.sigmaMap (fun j => hf j)

/-- For maps fⱼ:Xⱼ→Yⱼ in TopCat.{u} indexed by J:Type v, if every fⱼ is a closed embedding with
closed codomain singletons outside its image, the continuous disjoint-union map (j,x)↦(j,fⱼ(x))
is also one. The resulting spaces have carrier universe max(u,v). -/
theorem closedT1Embeddings_sigmaMapTop (hf : ∀ j, TopCat.closedT1Embeddings (f j)) :
    TopCat.closedT1Embeddings
      (TopCat.ofHom ⟨Sigma.map (fun j : J => j) (fun j => (f j).hom),
        Continuous.sigma_map (fun j => (hf j).continuous)⟩) :=
  sigmaMap_closedT1Embedding_of_forall hf

instance : TopCat.closedT1Embeddings.{max v u}.IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape J := by
    apply MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
    intro X₁ X₂ _ _ g hg
    have h_top :
        Topology.IsClosedT1Embedding (Sigma.map (fun j : J => j) (fun j => (g j).hom)) :=
      Topology.IsClosedT1Embedding.sigmaMap (f := fun j => (g j).hom)
        (fun j => (TopCat.closedT1Embeddings_iff (g j)).mp (hg j))
    have h_cont : Continuous (Sigma.map (fun j : J => j) (fun j => (g j).hom)) :=
      Continuous.sigma_map (fun j => (hg j).continuous)
    let sigmaMapTop : TopCat.of (Σ j, X₁ j) ⟶ TopCat.of (Σ j, X₂ j) :=
      TopCat.ofHom ⟨Sigma.map (fun j : J => j) (fun j => (g j).hom), h_cont⟩
    have h_closed_top : TopCat.closedT1Embeddings sigmaMapTop := h_top
    let e₁ : (∐ X₁) ≅ TopCat.of (Σ j, X₁ j) := TopCat.sigmaIsoSigma X₁
    let e₂ : (∐ X₂) ≅ TopCat.of (Σ j, X₂ j) := TopCat.sigmaIsoSigma X₂
    have h3 : ∀ j, TopCat.sigmaι X₁ j ≫ sigmaMapTop =
        g j ≫ TopCat.sigmaι X₂ j := by
      intro j
      apply TopCat.ext
      intro x
      simp [TopCat.sigmaι, sigmaMapTop, Sigma.map_mk]
    have h_comm : e₁.hom ≫ sigmaMapTop = Limits.Sigma.map g ≫ e₂.hom :=
      TopCat.sigmaIsoSigma_hom_naturality h3
    have h_iso : Arrow.mk (Limits.Sigma.map g) ≅ Arrow.mk sigmaMapTop :=
      Arrow.isoMk e₁ e₂ h_comm
    have h_iff : TopCat.closedT1Embeddings (Limits.Sigma.map g) ↔
        TopCat.closedT1Embeddings sigmaMapTop :=
      TopCat.closedT1Embeddings.arrow_mk_iso_iff h_iso
    exact h_iff.mpr h_closed_top

end TopCat
