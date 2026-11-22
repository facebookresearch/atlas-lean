/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Closed embeddings are stable under retracts in `TopCat`

A retract (in the arrow category) of a closed embedding is a closed embedding.
From `RetractArrow f g` with `g` a closed embedding, the section legs are
embeddings (a section of a continuous retraction is an embedding), hence `f`
is an embedding by left cancellation against the target inclusion; the range
of `f` is the preimage of the closed range of `g` along that inclusion, hence
closed.

This reuses `TopCat.closedEmbeddings` and the pinned `RetractArrow` /
`MorphismProperty.IsStableUnderRetracts` API. No model structure is proved.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace TopCat

instance : closedEmbeddings.IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg := by
    have hgCE : IsClosedEmbedding g.hom := hg
    have hgEmb : IsEmbedding g.hom := hgCE.isEmbedding
    have hgClosed : IsClosed (Set.range g.hom) := hgCE.isClosed_range
    have hixCont : Continuous (h.i.left).hom := (h.i.left).hom.continuous
    have hrxCont : Continuous (h.r.left).hom := (h.r.left).hom.continuous
    have hiyCont : Continuous (h.i.right).hom := (h.i.right).hom.continuous
    have hryCont : Continuous (h.r.right).hom := (h.r.right).hom.continuous
    have hiw : ∀ (x : X),
        g.hom ((h.i.left).hom x) = (h.i.right).hom (f.hom x) :=
      fun x => ConcreteCategory.congr_hom ((forget TopCat).congr_map h.i_w) x
    have hrw : ∀ (z : Z),
        f.hom ((h.r.left).hom z) = (h.r.right).hom (g.hom z) :=
      fun z => ConcreteCategory.congr_hom ((forget TopCat).congr_map h.r_w) z
    have hretL : ∀ (x : X), (h.r.left).hom ((h.i.left).hom x) = x :=
      fun x =>
        ConcreteCategory.congr_hom ((forget TopCat).congr_map h.retract_left) x
    have hretR : ∀ (y : Y), (h.r.right).hom ((h.i.right).hom y) = y :=
      fun y =>
        ConcreteCategory.congr_hom ((forget TopCat).congr_map h.retract_right) y
    have hix : IsEmbedding (h.i.left).hom :=
      IsEmbedding.of_leftInverse (fun x => hretL x) hrxCont hixCont
    have hiy : IsEmbedding (h.i.right).hom :=
      IsEmbedding.of_leftInverse (fun y => hretR y) hryCont hiyCont
    have hgix : IsEmbedding (g.hom ∘ (h.i.left).hom) := hgEmb.comp hix
    have hcomp_eq : (h.i.right).hom ∘ f.hom = g.hom ∘ (h.i.left).hom :=
      funext fun x => (hiw x).symm
    have hiyf : IsEmbedding ((h.i.right).hom ∘ f.hom) := by
      rw [hcomp_eq]
      exact hgix
    have hfEmb : IsEmbedding f.hom := hiy.of_comp_iff.mp hiyf
    have hrange_eq :
        Set.range f.hom = (h.i.right).hom ⁻¹' (Set.range g.hom) := by
      ext y
      simp only [Set.mem_range, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(h.i.left).hom x, hiw x⟩
      · rintro ⟨z, hz⟩
        refine ⟨(h.r.left).hom z, ?_⟩
        calc f.hom ((h.r.left).hom z)
            = (h.r.right).hom (g.hom z) := hrw z
          _ = (h.r.right).hom ((h.i.right).hom y) := by rw [hz]
          _ = y := hretR y
    have hfClosed : IsClosed (Set.range f.hom) := by
      rw [hrange_eq]
      exact hgClosed.preimage hiyCont
    have hfCE : IsClosedEmbedding f.hom := ⟨hfEmb, hfClosed⟩
    exact (TopCat.closedEmbeddings_iff f).mpr hfCE

end TopCat
