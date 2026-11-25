/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedT1Embedding
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits

/-!
# Closed T1-embedding coproducts — arbitrary coproduct stability

Coproduct stability for `TopCat.closedT1Embeddings` via the concrete
`Sigma` topology. The core is `Topology.IsClosedT1Embedding.sigmaMap`:
a coproduct (disjoint union) of closed T1-embeddings is a closed
T1-embedding. The categorical coproduct `∐ X` in `TopCat` is
`TopCat.of (Σ X)` via `TopCat.sigmaIsoSigma`; transfer via
`MorphismProperty.RespectsIso` yields
`TopCat.closedT1Embeddings.IsStableUnderCoproducts`.

The relative-T1 part reduces a point `⟨i, y⟩` outside the `Sigma.map`
range to `y ∉ Set.range (f i)` and proves the singleton `{⟨i, y⟩}`
closed in the sigma codomain using `isClosedMap_sigmaMk`
(`isClosed_sigma_iff`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Topology

namespace Topology

variable {ι : Type v} {α β : ι → Type u} [∀ i, TopologicalSpace (α i)]
  [∀ i, TopologicalSpace (β i)] {f : ∀ i, α i → β i}

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
