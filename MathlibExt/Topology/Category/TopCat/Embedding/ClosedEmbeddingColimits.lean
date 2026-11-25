/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Constructions
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding

/-!
# Closed-embedding colimits — coproducts

Coproduct stability for `TopCat.closedEmbeddings` via the concrete
`Sigma` topology. The core is `Topology.IsClosedEmbedding.sigmaMap`:
a coproduct (disjoint union) of closed embeddings is a closed embedding.
The categorical coproduct `∐ X` in `TopCat` is `TopCat.of (Σ X)` via
`TopCat.sigmaIsoSigma`; transfer via `MorphismProperty.RespectsIso` yields
`TopCat.closedEmbeddings.IsStableUnderCoproducts`.

This module proves only coproduct stability. The other stability results live
in their named modules: pushout / cobase-change stability in
`ClosedEmbedding.lean` (`IsStableUnderCobaseChange`), and transfinite-composition
stability in `ClosedEmbeddingTransfinite.lean`
(`IsStableUnderTransfiniteComposition`).

No cofibration, model-structure, boundary/horn, or Riou legacy framework is
duplicated.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Topology

namespace Topology

variable {ι : Type v} {α β : ι → Type u} [∀ i, TopologicalSpace (α i)]
  [∀ i, TopologicalSpace (β i)] {f : ∀ i, α i → β i}

theorem IsClosedEmbedding.sigmaMap (hf : ∀ i, IsClosedEmbedding (f i)) :
    IsClosedEmbedding (Sigma.map (fun i : ι => i) f) := by
  refine ⟨?_, ?_⟩
  · exact (Topology.isEmbedding_sigmaMap (f₂ := f) Function.injective_id).2
      (fun i => (hf i).isEmbedding)
  · rw [isClosed_sigma_iff]
    intro j
    have h_eq :
        (Sigma.mk j ⁻¹' Set.range (Sigma.map (fun i : ι => i) f)) =
          Set.range (f j) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_range]
      constructor
      · rintro ⟨⟨i, x⟩, h_eq⟩
        have h_map : Sigma.map (fun i : ι => i) f ⟨i, x⟩ = ⟨j, y⟩ := h_eq
        simp only [Sigma.map_mk] at h_map
        have h_fst : i = j := congrArg Sigma.fst h_map
        subst h_fst
        cases h_map
        exact ⟨x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨⟨j, x⟩, rfl⟩
    rw [h_eq]
    exact (hf j).isClosed_range

end Topology

namespace TopCat

variable {J : Type v} {X Y : J → TopCat.{u}} {f : ∀ j, X j ⟶ Y j}

protected theorem sigmaIsoSigma_hom_naturality
    {J : Type v} {X Y : J → TopCat.{max v u}} {f : ∀ j, X j ⟶ Y j}
    {sigmaMapTop : TopCat.of (Σ j, X j) ⟶ TopCat.of (Σ j, Y j)}
    (h : ∀ j, TopCat.sigmaι X j ≫ sigmaMapTop = f j ≫ TopCat.sigmaι Y j) :
    (TopCat.sigmaIsoSigma X).hom ≫ sigmaMapTop =
      Limits.Sigma.map f ≫ (TopCat.sigmaIsoSigma Y).hom := by
  apply Limits.Sigma.hom_ext
  intro j
  have h1 : Limits.Sigma.ι X j ≫ (TopCat.sigmaIsoSigma X).hom = TopCat.sigmaι X j :=
    TopCat.sigmaIsoSigma_hom_ι X j
  have h2 : Limits.Sigma.ι X j ≫ Limits.Sigma.map f = f j ≫ Limits.Sigma.ι Y j := by
    simp
  calc Limits.Sigma.ι X j ≫ (TopCat.sigmaIsoSigma X).hom ≫ sigmaMapTop
      = TopCat.sigmaι X j ≫ sigmaMapTop := congrArg (· ≫ sigmaMapTop) h1
    _ = f j ≫ TopCat.sigmaι Y j := h j
    _ = f j ≫ Limits.Sigma.ι Y j ≫ (TopCat.sigmaIsoSigma Y).hom :=
        congrArg (f j ≫ ·) (TopCat.sigmaIsoSigma_hom_ι Y j).symm
    _ = Limits.Sigma.ι X j ≫ Limits.Sigma.map f ≫ (TopCat.sigmaIsoSigma Y).hom :=
        congrArg (· ≫ (TopCat.sigmaIsoSigma Y).hom) h2.symm

instance : TopCat.closedEmbeddings.{max v u}.IsStableUnderCoproducts.{v} where
  isStableUnderCoproductsOfShape J := by
    apply MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
    intro X₁ X₂ _ _ g hg
    have h_top :
        IsClosedEmbedding (Sigma.map (fun j : J => j) (fun j => (g j).hom)) :=
      Topology.IsClosedEmbedding.sigmaMap (f := fun j => (g j).hom)
        (fun j => (TopCat.closedEmbeddings_iff (g j)).mp (hg j))
    have h_cont : Continuous (Sigma.map (fun j : J => j) (fun j => (g j).hom)) :=
      Continuous.sigma_map (fun j => (hg j).continuous)
    let sigmaMapTop : TopCat.of (Σ j, X₁ j) ⟶ TopCat.of (Σ j, X₂ j) :=
      TopCat.ofHom ⟨Sigma.map (fun j : J => j) (fun j => (g j).hom), h_cont⟩
    have h_closed_top : TopCat.closedEmbeddings sigmaMapTop := h_top
    let e₁ : (∐ X₁) ≅ TopCat.of (Σ j, X₁ j) := TopCat.sigmaIsoSigma X₁
    let e₂ : (∐ X₂) ≅ TopCat.of (Σ j, X₂ j) := TopCat.sigmaIsoSigma X₂
    have h_comm : e₁.hom ≫ sigmaMapTop = Limits.Sigma.map g ≫ e₂.hom := by
      apply TopCat.sigmaIsoSigma_hom_naturality
      intro j
      apply TopCat.ext
      intro x
      simp [TopCat.sigmaι, sigmaMapTop, Sigma.map_mk]
    have h_iso : Arrow.mk (Limits.Sigma.map g) ≅ Arrow.mk sigmaMapTop :=
      Arrow.isoMk e₁ e₂ h_comm
    have h_iff : TopCat.closedEmbeddings (Limits.Sigma.map g) ↔
        TopCat.closedEmbeddings sigmaMapTop :=
      TopCat.closedEmbeddings.arrow_mk_iso_iff h_iso
    exact h_iff.mpr h_closed_top

end TopCat
