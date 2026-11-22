/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
public import MathlibExt.Topology.Category.CGWH.Colimits
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingColimits
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Coproducts of CGWH model generators

Arbitrary same-universe coproducts of the native boundary and positive-horn
generators are created by the immediate inclusion into compactly generated
spaces, and their coproduct maps are closed embeddings after inclusion into
topological spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open Topology

universe u v

namespace CGWH

/-- The immediate inclusion identifies the ambient compactly generated
coproduct with the included native coproduct. -/
noncomputable def coproductComparisonToCompactlyGeneratedIso
    {I : Type v} (X : I → CGWH.{u, v}) :
    (∐ fun i ↦ cgwhToCompactlyGenerated.obj (X i)) ≅
      cgwhToCompactlyGenerated.obj (∐ X) := by
  let F := Discrete.functor X
  let d := F ⋙ cgwhToTop
  let sourceIso : Limits.colimit d ≅
      (∐ fun i ↦ cgwhToTop.obj (X i)) :=
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := d))
  have homeo_preserves
      {B C : Type v} [TopologicalSpace B] [TopologicalSpace C]
      (h : B ≃ₜ C) (hB : UWeakHausdorffSpace.{u} B) :
      UWeakHausdorffSpace.{u} C := by
    refine ⟨fun K f ↦ ?_⟩
    let f' : C(K, B) :=
      ⟨fun k ↦ h.symm (f k), h.symm.continuous.comp f.continuous⟩
    have hc : IsClosed (Set.range f') := hB.isClosed_range K f'
    have hrange : Set.range f = h '' Set.range f' := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨f' k, ⟨k, rfl⟩, h.apply_symm_apply (f k)⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (h.apply_symm_apply (f k)).symm⟩
    rw [hrange]
    exact h.isClosedMap _ hc
  have hTarget : UWeakHausdorffSpace.{u}
      (((∐ X) : CGWH.{u, v}) : Type v) :=
    CGWH.is_weakHausdorff ((∐ X) : CGWH.{u, v})
  have hRaw : UWeakHausdorffSpace.{u}
      (((∐ fun i ↦ cgwhToTop.obj (X i)) : TopCat.{v}) : Type v) :=
    homeo_preserves
      (TopCat.homeoOfIso (coproductComparisonIso X).symm) hTarget
  have hColim : UWeakHausdorffSpace.{u}
      ((Limits.colimit d : TopCat.{v}) : Type v) :=
    homeo_preserves (TopCat.homeoOfIso sourceIso.symm) hRaw
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2
      ((colimitComparisonFromTop_isHomeomorph_iff F).2 hColim)
  exact CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.preimageIso
    ((PreservesCoproduct.iso
      CompactlyGenerated.compactlyGeneratedToTop
      (fun i ↦ cgwhToCompactlyGenerated.obj (X i))) ≪≫
        sourceIso.symm ≪≫ asIso (colimitComparisonFromTop F))

/-- The ambient compactly generated coproduct of CGWH spaces is weak
Hausdorff. -/
theorem compactlyGeneratedCoproduct_isWeakHausdorff
    {I : Type v} (X : I → CGWH.{u, v}) :
    UWeakHausdorffSpace.{u}
      (((∐ fun i ↦ cgwhToCompactlyGenerated.obj (X i)) :
        CompactlyGenerated.{u, v}) : Type v) := by
  let e := CompactlyGenerated.homeoOfIso
    (coproductComparisonToCompactlyGeneratedIso X)
  let hTarget : UWeakHausdorffSpace.{u}
      (((∐ X) : CGWH.{u, v}) : Type v) :=
    inferInstance
  refine ⟨fun K g ↦ ?_⟩
  let g' : C(K,
      cgwhToCompactlyGenerated.obj ((∐ X) : CGWH.{u, v})) :=
    ⟨fun k ↦ e (g k), e.continuous.comp g.continuous⟩
  have hc : IsClosed (Set.range g') := hTarget.isClosed_range K g'
  have hrange : Set.range g = e.symm '' Set.range g' := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨g' k, ⟨k, rfl⟩, e.symm_apply_apply (g k)⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (e.symm_apply_apply (g k)).symm⟩
  rw [hrange]
  exact e.symm.isClosedMap _ hc

/-- The immediate comparison carries each ambient coproduct injection to
the included native injection. -/
@[reassoc]
theorem coproductComparisonToCompactlyGeneratedIso_hom_ι
    {I : Type v} (X : I → CGWH.{u, v}) (i : I) :
    Sigma.ι (fun j ↦ cgwhToCompactlyGenerated.obj (X j)) i ≫
        (coproductComparisonToCompactlyGeneratedIso X).hom =
      cgwhToCompactlyGenerated.map (Sigma.ι X i) := by
  apply CompactlyGenerated.compactlyGeneratedToTop.map_injective
  change CompactlyGenerated.compactlyGeneratedToTop.map (Sigma.ι _ i) ≫
      CompactlyGenerated.compactlyGeneratedToTop.map
        (coproductComparisonToCompactlyGeneratedIso X).hom = _
  simp only [coproductComparisonToCompactlyGeneratedIso,
    Functor.FullyFaithful.preimageIso_hom,
    CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop.map_preimage]
  simp only [Iso.trans_hom]
  rw [← Category.assoc]
  rw [show CompactlyGenerated.compactlyGeneratedToTop.map (Sigma.ι _ i) ≫
      (PreservesCoproduct.iso
        CompactlyGenerated.compactlyGeneratedToTop _).hom =
      Sigma.ι (fun j ↦ CompactlyGenerated.compactlyGeneratedToTop.obj
        (cgwhToCompactlyGenerated.obj (X j))) i by
    rw [← cancel_mono (PreservesCoproduct.iso
      CompactlyGenerated.compactlyGeneratedToTop
      (fun j ↦ cgwhToCompactlyGenerated.obj (X j))).inv]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]]
  simp only [asIso_hom]
  change (Limits.colimit.ι (Discrete.functor fun j ↦
      CompactlyGenerated.compactlyGeneratedToTop.obj
        (cgwhToCompactlyGenerated.obj (X j))) (Discrete.mk i) ≫
      (HasColimit.isoOfNatIso
        (Discrete.natIsoFunctor
          (F := Discrete.functor X ⋙ cgwhToTop))).inv) ≫
      colimitComparisonFromTop (Discrete.functor X) = _
  rw [HasColimit.ι_isoOfNatIso_inv]
  simp only [Discrete.natIsoFunctor_inv_app]
  simpa using
    (colimitComparisonFromTop_ι (Discrete.functor X) (Discrete.mk i))

/-- Arbitrary same-universe coproducts of native closed embeddings remain
closed embeddings under the actual underlying functor. -/
instance closedEmbeddings_isStableUnderCoproducts :
    (TopCat.closedEmbeddings.inverseImage cgwhToTop.{u, v}).IsStableUnderCoproducts.{v} := by
  constructor
  intro J
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
  intro A B _ _ f hf
  let eA : (∐ fun j ↦ cgwhToTop.obj (A j)) ≅
      cgwhToTop.obj (∐ A) :=
    (PreservesCoproduct.iso
      CompactlyGenerated.compactlyGeneratedToTop
      (fun j ↦ cgwhToCompactlyGenerated.obj (A j))).symm ≪≫
      CompactlyGenerated.compactlyGeneratedToTop.mapIso
        (coproductComparisonToCompactlyGeneratedIso A)
  let eB : (∐ fun j ↦ cgwhToTop.obj (B j)) ≅
      cgwhToTop.obj (∐ B) :=
    (PreservesCoproduct.iso
      CompactlyGenerated.compactlyGeneratedToTop
      (fun j ↦ cgwhToCompactlyGenerated.obj (B j))).symm ≪≫
      CompactlyGenerated.compactlyGeneratedToTop.mapIso
        (coproductComparisonToCompactlyGeneratedIso B)
  have heA (j : J) :
      Sigma.ι (fun j ↦ cgwhToTop.obj (A j)) j ≫ eA.hom =
        cgwhToTop.map (Sigma.ι A j) := by
    change (Sigma.ι (fun j ↦ cgwhToTop.obj (A j)) j ≫
        (PreservesCoproduct.iso
          CompactlyGenerated.compactlyGeneratedToTop
          (fun j ↦ cgwhToCompactlyGenerated.obj (A j))).inv) ≫
        CompactlyGenerated.compactlyGeneratedToTop.map
          (coproductComparisonToCompactlyGeneratedIso A).hom = _
    rw [PreservesCoproduct.inv_hom]
    change (Sigma.ι (fun j ↦
        CompactlyGenerated.compactlyGeneratedToTop.obj
          (cgwhToCompactlyGenerated.obj (A j))) j ≫
        sigmaComparison CompactlyGenerated.compactlyGeneratedToTop
          (fun j ↦ cgwhToCompactlyGenerated.obj (A j))) ≫
      CompactlyGenerated.compactlyGeneratedToTop.map
        (coproductComparisonToCompactlyGeneratedIso A).hom = _
    rw [ι_comp_sigmaComparison]
    rw [← CompactlyGenerated.compactlyGeneratedToTop.map_comp,
      coproductComparisonToCompactlyGeneratedIso_hom_ι]
    rfl
  have heB (j : J) :
      Sigma.ι (fun j ↦ cgwhToTop.obj (B j)) j ≫ eB.hom =
        cgwhToTop.map (Sigma.ι B j) := by
    change (Sigma.ι (fun j ↦ cgwhToTop.obj (B j)) j ≫
        (PreservesCoproduct.iso
          CompactlyGenerated.compactlyGeneratedToTop
          (fun j ↦ cgwhToCompactlyGenerated.obj (B j))).inv) ≫
        CompactlyGenerated.compactlyGeneratedToTop.map
          (coproductComparisonToCompactlyGeneratedIso B).hom = _
    rw [PreservesCoproduct.inv_hom]
    change (Sigma.ι (fun j ↦
        CompactlyGenerated.compactlyGeneratedToTop.obj
          (cgwhToCompactlyGenerated.obj (B j))) j ≫
        sigmaComparison CompactlyGenerated.compactlyGeneratedToTop
          (fun j ↦ cgwhToCompactlyGenerated.obj (B j))) ≫
      CompactlyGenerated.compactlyGeneratedToTop.map
        (coproductComparisonToCompactlyGeneratedIso B).hom = _
    rw [ι_comp_sigmaComparison]
    rw [← CompactlyGenerated.compactlyGeneratedToTop.map_comp,
      coproductComparisonToCompactlyGeneratedIso_hom_ι]
    rfl
  have hRaw : TopCat.closedEmbeddings
      (Limits.Sigma.map (fun j ↦ cgwhToTop.map (f j))) := by
    apply MorphismProperty.colimMap
    rintro ⟨j⟩
    exact hf j
  have hComm : eA.hom ≫ cgwhToTop.map (Limits.Sigma.map f) =
      Limits.Sigma.map (fun j ↦ cgwhToTop.map (f j)) ≫ eB.hom := by
    apply Limits.Sigma.hom_ext
    intro j
    rw [← Category.assoc, heA, ← cgwhToTop.map_comp,
      Sigma.ι_map]
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, heB]
    rfl
  have hArrow :
      Arrow.mk (Limits.Sigma.map (fun j ↦ cgwhToTop.map (f j))) ≅
        Arrow.mk (cgwhToTop.map (Limits.Sigma.map f)) :=
    Arrow.isoMk eA eB hComm
  exact (TopCat.closedEmbeddings.arrow_mk_iso_iff hArrow).mp hRaw

/-- Coproducts of native boundary and horn generators are closed embeddings
after inclusion into topological spaces. -/
theorem coproducts_realizedGenerators_le_closedEmbeddings :
    MorphismProperty.coproducts.{v}
        (realizedBoundaryInclusions.{u, v} ⊔
          realizedHornInclusions.{u, v}) ≤
      TopCat.closedEmbeddings.inverseImage cgwhToTop.{u, v} := by
  rw [MorphismProperty.coproducts_le_iff]
  apply sup_le
  · intro A B f hf
    obtain ⟨n⟩ := hf
    have hTop := TopCat.closedT1Embeddings_le_closedEmbeddings _
      (TopCat.realizedBoundaryInclusions_le_closedT1Embeddings _
        (TopCat.boundary_mem_realizedBoundaryInclusions n))
    have hCompact : TopCat.closedEmbeddings
        (CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
          (CompactlyGenerated.realizedBoundaryInclusion.{v, u} n)) :=
      (CompactlyGenerated.compactlyGeneratedToTop_map_realizedBoundaryInclusion
        n).symm ▸
        hTop
    change TopCat.closedEmbeddings
      (CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
        (cgwhToCompactlyGenerated.{u, v}.map
          (realizedBoundaryInclusion.{v, u} n)))
    exact (congrArg (fun q ↦
      CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map q)
        (cgwhToCompactlyGenerated_map_realizedBoundaryInclusion
          n)).symm ▸
          hCompact
  · intro A B f hf
    unfold realizedHornInclusions at hf
    rw [MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    have hTop := TopCat.closedT1Embeddings_le_closedEmbeddings _
      (TopCat.realizedHornInclusions_le_closedT1Embeddings _
        (TopCat.horn_mem_realizedHornInclusions (n + 1) i))
    have hCompact : TopCat.closedEmbeddings
        (CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
          (CompactlyGenerated.realizedHornInclusion.{v, u} n i)) :=
      (CompactlyGenerated.compactlyGeneratedToTop_map_realizedHornInclusion
        n i).symm ▸
        hTop
    change TopCat.closedEmbeddings
      (CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map
        (cgwhToCompactlyGenerated.{u, v}.map
          (realizedHornInclusion.{v, u} n i)))
    exact (congrArg (fun q ↦
      CompactlyGenerated.compactlyGeneratedToTop.{u, v}.map q)
        (cgwhToCompactlyGenerated_map_realizedHornInclusion
          n i)).symm ▸
          hCompact

end CGWH
