/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Reflection
public import MathlibExt.Topology.Category.CompactlyGenerated.Colimits
public import MathlibExt.Topology.Category.CompactlyGenerated.ClosedEmbeddingProduct
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Colimits in compactly generated weak-Hausdorff spaces

Colimits are obtained by weak-Hausdorff reflection of compactly generated
colimits.  This file also compares their underlying topological spaces with
ordinary topological colimits and identifies coproducts and pushouts along a
closed embedding.
-/

public section

set_option autoImplicit false

noncomputable section

universe u v w r

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace CGWH

/-- CGWH spaces have all same-carrier-universe colimits. -/
noncomputable instance instHasColimitsOfSize :
    HasColimitsOfSize.{v, v} CGWH.{u, v} :=
  CategoryTheory.hasColimits_of_reflective
    cgwhToCompactlyGenerated

private noncomputable def reflectedColimitCocone
    {J : Type w} [Category.{r} J] (F : J ⥤ CGWH.{u, v})
    [HasColimit (F ⋙ cgwhToCompactlyGenerated)] : Cocone F := by
  let c := weakHausdorffification.mapCocone
    (colimit.cocone (F ⋙ cgwhToCompactlyGenerated))
  let e :
      (F ⋙ cgwhToCompactlyGenerated) ⋙ weakHausdorffification ≅ F :=
    Functor.isoWhiskerLeft F
        (asIso weakHausdorffificationAdjunction.counit) ≪≫
      F.rightUnitor
  exact (Cocone.precompose e.inv).obj c

private noncomputable def reflectedColimitIsColimit
    {J : Type w} [Category.{r} J] (F : J ⥤ CGWH.{u, v})
    [HasColimit (F ⋙ cgwhToCompactlyGenerated)] :
    IsColimit (reflectedColimitCocone F) := by
  let c := weakHausdorffification.mapCocone
    (colimit.cocone (F ⋙ cgwhToCompactlyGenerated))
  let e :
      (F ⋙ cgwhToCompactlyGenerated) ⋙ weakHausdorffification ≅ F :=
    Functor.isoWhiskerLeft F
        (asIso weakHausdorffificationAdjunction.counit) ≪≫
      F.rightUnitor
  let _ : weakHausdorffification.IsLeftAdjoint :=
    weakHausdorffificationAdjunction.isLeftAdjoint
  let t : IsColimit c :=
    isColimitOfPreserves weakHausdorffification
      (colimit.isColimit (F ⋙ cgwhToCompactlyGenerated))
  exact (IsColimit.precomposeInvEquiv e c).symm t

private theorem reflectedColimitCocone_ι_map
    {J : Type w} [Category.{r} J] (F : J ⥤ CGWH.{u, v})
    [HasColimit (F ⋙ cgwhToCompactlyGenerated)] (j : J) :
    cgwhToCompactlyGenerated.map
        ((reflectedColimitCocone F).ι.app j) =
      Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) j ≫
        reflectionUnit.app
          (Limits.colimit (F ⋙ cgwhToCompactlyGenerated)) := by
  let D := F ⋙ cgwhToCompactlyGenerated
  dsimp [reflectedColimitCocone]
  simp only [Category.id_comp]
  change cgwhToCompactlyGenerated.map
      ((inv weakHausdorffificationAdjunction.counit).app (F.obj j) ≫
        weakHausdorffification.map (Limits.colimit.ι D j)) = _
  rw [Functor.map_comp, NatIso.isIso_inv_app, Functor.map_inv]
  rw [weakHausdorffificationAdjunction.inv_counit_map]
  exact weakHausdorffificationAdjunction.unit.naturality
    (Limits.colimit.ι D j) |>.symm

/-- Every point of a CGWH colimit is in the image of one of its colimit legs.

This applies to arbitrary diagram and morphism universes whenever both the
underlying compactly generated colimit and the CGWH colimit exist. -/
theorem colimit_exists_rep
    {J : Type w} [Category.{r} J] (F : J ⥤ CGWH.{u, v})
    [HasColimit (F ⋙ cgwhToCompactlyGenerated)] [HasColimit F]
    (z : ↥(Limits.colimit F)) :
    ∃ (j : J) (x : ↥(F.obj j)), Limits.colimit.ι F j x = z := by
  let D := F ⋙ cgwhToCompactlyGenerated
  let L := Limits.colimit D
  let c := reflectedColimitCocone F
  let hc := reflectedColimitIsColimit F
  let e := hc.coconePointUniqueUpToIso (Limits.colimit.isColimit F)
  let q := reflectionUnit.app L
  obtain ⟨y, hy⟩ := reflectionUnit_surjective L (e.inv z)
  have hTop : IsColimit
      (CompactlyGenerated.compactlyGeneratedToTop.mapCocone
        (Limits.colimit.cocone D)) :=
    isColimitOfPreserves
      CompactlyGenerated.compactlyGeneratedToTop
      (Limits.colimit.isColimit D)
  have hType : IsColimit
      ((forget TopCat).mapCocone
        (CompactlyGenerated.compactlyGeneratedToTop.mapCocone
          (Limits.colimit.cocone D))) :=
    isColimitOfPreserves (forget TopCat) hTop
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hType y
  change Limits.colimit.ι D j x = y at hx
  refine ⟨j, x, ?_⟩
  have hcleg := ConcreteCategory.congr_hom
    (reflectedColimitCocone_ι_map F j) x
  have hcx : c.ι.app j x = e.inv z := by
    rw [← hy, ← hx]
    change c.ι.app j x = q (Limits.colimit.ι D j x)
    exact hcleg
  have heleg := IsColimit.comp_coconePointUniqueUpToIso_hom
    hc (Limits.colimit.isColimit F) j
  calc
    Limits.colimit.ι F j x = e.hom (c.ι.app j x) :=
      (ConcreteCategory.congr_hom heleg x).symm
    _ = e.hom (e.inv z) := congrArg e.hom hcx
    _ = z := e.inv_hom_id_apply z

variable {J : Type v} [Category.{v} J]

/-- The chosen CGWH colimit is canonically the weak-Hausdorff reflection of
the compactly generated colimit. -/
noncomputable def colimit (F : J ⥤ CGWH.{u, v}) :
    weakHausdorffification.obj
        (Limits.colimit (F ⋙ cgwhToCompactlyGenerated)) ≅
      Limits.colimit F := by
  change (reflectedColimitCocone F).pt ≅ Limits.colimit F
  exact (reflectedColimitIsColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)

/-- Comparison from the ordinary topological colimit to the underlying space
of the native CGWH colimit. -/
noncomputable def colimitComparisonFromTop (F : J ⥤ CGWH.{u, v}) :
    Limits.colimit (F ⋙ cgwhToTop) ⟶
      cgwhToTop.obj (Limits.colimit F) :=
  (preservesColimitIso
      CompactlyGenerated.compactlyGeneratedToTop
      (F ⋙ cgwhToCompactlyGenerated)).inv ≫
    CompactlyGenerated.compactlyGeneratedToTop.map
      (reflectionUnit.app
        (Limits.colimit (F ⋙ cgwhToCompactlyGenerated))) ≫
    CompactlyGenerated.compactlyGeneratedToTop.map
      (cgwhToCompactlyGenerated.map (colimit F).hom)

/-- Each raw colimit injection followed by the comparison is the included
native colimit injection. -/
@[reassoc]
theorem colimitComparisonFromTop_ι
    (F : J ⥤ CGWH.{u, v}) (k : J) :
    Limits.colimit.ι (F ⋙ cgwhToTop) k ≫
        colimitComparisonFromTop F =
      cgwhToTop.map (Limits.colimit.ι F k) := by
  unfold colimitComparisonFromTop
  change Limits.colimit.ι
        ((F ⋙ cgwhToCompactlyGenerated) ⋙
          CompactlyGenerated.compactlyGeneratedToTop) k ≫
      (preservesColimitIso
        CompactlyGenerated.compactlyGeneratedToTop
        (F ⋙ cgwhToCompactlyGenerated)).inv ≫
      CompactlyGenerated.compactlyGeneratedToTop.map
        (reflectionUnit.app
          (Limits.colimit (F ⋙ cgwhToCompactlyGenerated))) ≫
      CompactlyGenerated.compactlyGeneratedToTop.map
        (cgwhToCompactlyGenerated.map (colimit F).hom) =
    CompactlyGenerated.compactlyGeneratedToTop.map
      (cgwhToCompactlyGenerated.map (Limits.colimit.ι F k))
  rw [ι_preservesColimitIso_inv_assoc]
  rw [← CompactlyGenerated.compactlyGeneratedToTop.map_comp,
    ← CompactlyGenerated.compactlyGeneratedToTop.map_comp]
  apply congrArg CompactlyGenerated.compactlyGeneratedToTop.map
  change Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) k ≫
      weakHausdorffificationAdjunction.unit.app
        (Limits.colimit (F ⋙ cgwhToCompactlyGenerated)) ≫
      cgwhToCompactlyGenerated.map (colimit F).hom = _
  rw [show Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) k ≫
        weakHausdorffificationAdjunction.unit.app
          (Limits.colimit (F ⋙ cgwhToCompactlyGenerated)) ≫
        cgwhToCompactlyGenerated.map (colimit F).hom =
      weakHausdorffificationAdjunction.unit.app
          (cgwhToCompactlyGenerated.obj (F.obj k)) ≫
        (weakHausdorffification ⋙ cgwhToCompactlyGenerated).map
          (Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) k) ≫
        cgwhToCompactlyGenerated.map (colimit F).hom by
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
      weakHausdorffificationAdjunction.unit.naturality_assoc
        (Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) k)
        (cgwhToCompactlyGenerated.map (colimit F).hom)]
  change weakHausdorffificationAdjunction.unit.app
        (cgwhToCompactlyGenerated.obj (F.obj k)) ≫
      cgwhToCompactlyGenerated.map
        (weakHausdorffification.map
          (Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) k)) ≫
      cgwhToCompactlyGenerated.map (colimit F).hom = _
  rw [← cgwhToCompactlyGenerated.map_comp]
  have hleg := IsColimit.comp_coconePointUniqueUpToIso_hom
    (reflectedColimitIsColimit F) (Limits.colimit.isColimit F) k
  have hleg' : (asIso
        (weakHausdorffificationAdjunction.counit.app (F.obj k))).inv ≫
        weakHausdorffification.map
          (Limits.colimit.ι (F ⋙ cgwhToCompactlyGenerated) k) ≫
        (colimit F).hom = Limits.colimit.ι F k := by
    simpa [reflectedColimitCocone, colimit] using hleg
  rw [← hleg']
  simp

/-- Naturality of the raw-to-native colimit comparison. -/
theorem colimitComparisonFromTop_naturality
    {F G : J ⥤ CGWH.{u, v}} (f : F ⟶ G) :
    Limits.colimMap (Functor.whiskerRight f cgwhToTop) ≫
        colimitComparisonFromTop G =
      colimitComparisonFromTop F ≫
        cgwhToTop.map (Limits.colimMap f) := by
  apply Limits.colimit.hom_ext
  intro k
  simp only [Limits.ι_colimMap_assoc,
    colimitComparisonFromTop_ι, Functor.whiskerRight_app,
    ← Functor.map_comp]
  rw [← Category.assoc, colimitComparisonFromTop_ι]
  rw [← cgwhToTop.map_comp, Limits.ι_colimMap]

/-- The raw-to-native colimit comparison is a homeomorphism exactly when
the ordinary topological colimit is weak Hausdorff. -/
theorem colimitComparisonFromTop_isHomeomorph_iff
    (F : J ⥤ CGWH.{u, v}) :
    IsHomeomorph (colimitComparisonFromTop F) ↔
      UWeakHausdorffSpace.{u}
        ↥(Limits.colimit (F ⋙ cgwhToTop)) := by
  let L := Limits.colimit (F ⋙ cgwhToCompactlyGenerated)
  let p := preservesColimitIso
    CompactlyGenerated.compactlyGeneratedToTop
    (F ⋙ cgwhToCompactlyGenerated)
  let m := CompactlyGenerated.compactlyGeneratedToTop.map
    (reflectionUnit.app L)
  let r := CompactlyGenerated.compactlyGeneratedToTop.map
    (cgwhToCompactlyGenerated.map (colimit F).hom)
  have hcomp : IsHomeomorph (p.inv ≫ m ≫ r) ↔
      IsHomeomorph m := by
    constructor
    · intro h
      let _ : IsIso (p.inv ≫ m ≫ r) :=
        (TopCat.isIso_iff_isHomeomorph _).2 h
      let _ : IsIso (m ≫ r) :=
        IsIso.of_isIso_comp_left p.inv (m ≫ r)
      let _ : IsIso m := IsIso.of_isIso_comp_right m r
      exact (TopCat.isIso_iff_isHomeomorph m).1 inferInstance
    · intro h
      let _ : IsIso m := (TopCat.isIso_iff_isHomeomorph m).2 h
      exact (TopCat.isIso_iff_isHomeomorph _).1 inferInstance
  have hm : IsHomeomorph m ↔ UWeakHausdorffSpace.{u} L := by
    change IsHomeomorph (reflectionUnit.app L) ↔ _
    exact reflectionUnit_isHomeomorph_iff L
  let e : (↥(CompactlyGenerated.compactlyGeneratedToTop.obj L)) ≃ₜ
      ↥(Limits.colimit (F ⋙ cgwhToTop)) :=
    TopCat.homeoOfIso p
  have homeo_preserves
      {A B : Type v} [TopologicalSpace A] [TopologicalSpace B]
      (e' : A ≃ₜ B) (hA : UWeakHausdorffSpace.{u} A) :
      UWeakHausdorffSpace.{u} B := by
    refine ⟨fun K f => ?_⟩
    let f' : C(K, A) :=
      ⟨fun k => e'.symm (f k), e'.symm.continuous.comp f.continuous⟩
    have hc : IsClosed (Set.range f') := hA.isClosed_range K f'
    have hrange : Set.range f = e' '' Set.range f' := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨f' k, ⟨k, rfl⟩, e'.apply_symm_apply (f k)⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (e'.apply_symm_apply (f k)).symm⟩
    rw [hrange]
    exact e'.isClosedMap _ hc
  have hwh : UWeakHausdorffSpace.{u} L ↔
      UWeakHausdorffSpace.{u}
        ↥(Limits.colimit (F ⋙ cgwhToTop)) := by
    exact ⟨homeo_preserves e, homeo_preserves e.symm⟩
  change IsHomeomorph (p.inv ≫ m ≫ r) ↔ _
  exact hcomp.trans (hm.trans hwh)

private theorem rawCoproduct_isWeakHausdorff
    {I : Type v} (X : I → CGWH.{u, v}) :
    UWeakHausdorffSpace.{u}
      ↥(Limits.colimit
        (Discrete.functor X ⋙ cgwhToTop)) := by
  let A : I → TopCat.{v} := fun i => cgwhToTop.obj (X i)
  let d := Discrete.functor X ⋙ cgwhToTop
  let e : ↥(Limits.colimit d) ≃ₜ (Σ i, ↥(A i)) :=
    TopCat.homeoOfIso
      (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := d)) ≪≫
        TopCat.sigmaIsoSigma A)
  have hsigma : UWeakHausdorffSpace.{u} (Σ i, ↥(A i)) := by
    refine ⟨fun K f => ?_⟩
    apply isClosed_sigma_iff.mpr
    intro i
    let ι : ↥(A i) → (Σ j, ↥(A j)) :=
      @Sigma.mk I (fun j => ↥(A j)) i
    have hιclosed : IsClosed (Set.range ι) :=
      isClosed_range_sigmaMk
    have hKclosed : IsClosed (f ⁻¹' Set.range ι) :=
      hιclosed.preimage f.continuous
    let Ki := {k : K // f k ∈ Set.range ι}
    let _ : CompactSpace Ki :=
      isCompact_iff_compactSpace.mp hKclosed.isCompact
    let hι : IsEmbedding ι := by
      simpa only [ι] using
        (Topology.IsEmbedding.sigmaMk
          (i := i) (σ := fun j => ↥(A j)))
    let ei : ↥(A i) ≃ₜ Set.range ι := hι.toHomeomorph
    have hfsub : Continuous (fun k : Ki =>
        (⟨f k.1, k.2⟩ : Set.range ι)) :=
      (f.continuous.comp continuous_subtype_val).subtype_mk _
    let g : C(CompHaus.of Ki, ↥(A i)) :=
      ⟨fun k => ei.symm ⟨f k.1, k.2⟩,
        ei.symm.continuous.comp hfsub⟩
    have hg : IsClosed (Set.range g) :=
      (X i).is_weakHausdorff.isClosed_range (CompHaus.of Ki) g
    rw [show Sigma.mk i ⁻¹' Set.range f = Set.range g by
      ext x
      constructor
      · rintro ⟨k, hk⟩
        have hk' : f k ∈ Set.range ι := ⟨x, hk.symm⟩
        refine ⟨⟨k, hk'⟩, ?_⟩
        apply ei.injective
        change ei (ei.symm ⟨f k, hk'⟩) = ei x
        rw [ei.apply_symm_apply]
        apply Subtype.ext
        simpa only [ei, hι, ι,
          Topology.IsEmbedding.toHomeomorph_apply_coe] using hk
      · rintro ⟨k, rfl⟩
        refine ⟨k.1, ?_⟩
        rcases k.2 with ⟨x, hx⟩
        have hgx : g k = x := by
          apply ei.injective
          change ei (ei.symm ⟨f k.1, k.2⟩) = ei x
          rw [ei.apply_symm_apply]
          apply Subtype.ext
          simpa only [ei, hι, ι,
            Topology.IsEmbedding.toHomeomorph_apply_coe] using hx.symm
        rw [hgx]
        simpa only [ι] using hx.symm]
    exact hg
  have homeo_preserves
      {B C : Type v} [TopologicalSpace B] [TopologicalSpace C]
      (h : B ≃ₜ C) (hB : UWeakHausdorffSpace.{u} B) :
      UWeakHausdorffSpace.{u} C := by
    refine ⟨fun K f => ?_⟩
    let f' : C(K, B) :=
      ⟨fun k => h.symm (f k), h.symm.continuous.comp f.continuous⟩
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
  exact homeo_preserves e.symm hsigma

/-- The ordinary topological coproduct of CGWH spaces is canonically the
underlying space of their native coproduct. -/
noncomputable def coproductComparisonIso
    {I : Type v} (X : I → CGWH.{u, v}) :
    (∐ fun i => cgwhToTop.obj (X i)) ≅
      cgwhToTop.obj (∐ X) := by
  let F := Discrete.functor X
  let d := F ⋙ cgwhToTop
  let sourceIso : Limits.colimit d ≅
      (∐ fun i => cgwhToTop.obj (X i)) :=
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := d))
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2
      ((colimitComparisonFromTop_isHomeomorph_iff F).2
        (rawCoproduct_isWeakHausdorff X))
  exact sourceIso.symm ≪≫ asIso (colimitComparisonFromTop F)

/-- A topological coproduct injection followed by the canonical comparison
is the underlying native CGWH coproduct injection. -/
@[reassoc]
theorem coproductComparisonIso_ι
    {I : Type v} (X : I → CGWH.{u, v}) (i : I) :
    Limits.Sigma.ι (fun j => cgwhToTop.obj (X j)) i ≫
        (coproductComparisonIso X).hom =
      cgwhToTop.map (Limits.Sigma.ι X i) := by
  unfold coproductComparisonIso
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom,
    HasColimit.ι_isoOfNatIso_inv_assoc,
    Discrete.natIsoFunctor_inv_app]
  exact colimitComparisonFromTop_ι (Discrete.functor X) (Discrete.mk i)

private def closedPushoutSetoid
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    Setoid (↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y)) := by
  let i₀ : (↥(cgwhToTop.obj W) : Type v) ⟶
      (↥(cgwhToTop.obj X) : Type v) :=
    TypeCat.ofHom (ConcreteCategory.hom (cgwhToTop.map i))
  let f₀ : (↥(cgwhToTop.obj W) : Type v) ⟶
      (↥(cgwhToTop.obj Y) : Type v) :=
    TypeCat.ofHom (ConcreteCategory.hom (cgwhToTop.map f))
  let _ : Mono i₀ := (CategoryTheory.mono_iff_injective i₀).2 (by
    intro w w' h
    exact hi.injective h)
  exact
    { r := CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
      iseqv :=
        CategoryTheory.Limits.Types.Pushout.equivalence_rel' i₀ f₀ }

private theorem closedPushoutSetoid_isClosed
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i)))
    [UCompactlyGeneratedSpace.{u}
      (↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y))] :
    closedEquivalenceRelation
      (CompactlyGenerated.of
        (↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y)))
      (closedPushoutSetoid i f hi) := by
  let W' := cgwhToCompactlyGenerated.obj W
  let X' := cgwhToCompactlyGenerated.obj X
  let Y' := cgwhToCompactlyGenerated.obj Y
  let S : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of (↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y))
  let i' : W' ⟶ X' := cgwhToCompactlyGenerated.map i
  let f' : W' ⟶ Y' := cgwhToCompactlyGenerated.map f
  let i₀ : (↥(cgwhToTop.obj W) : Type v) ⟶
      (↥(cgwhToTop.obj X) : Type v) :=
    TypeCat.ofHom (ConcreteCategory.hom (cgwhToTop.map i))
  let f₀ : (↥(cgwhToTop.obj W) : Type v) ⟶
      (↥(cgwhToTop.obj Y) : Type v) :=
    TypeCat.ofHom (ConcreteCategory.hom (cgwhToTop.map f))
  let _ : Mono i₀ := (CategoryTheory.mono_iff_injective i₀).2 (by
    intro w w' h
    exact hi.injective h)
  let inl : X' ⟶ S :=
    ConcreteCategory.ofHom ⟨Sum.inl, continuous_inl⟩
  let inr : Y' ⟶ S :=
    ConcreteCategory.ofHom ⟨Sum.inr, continuous_inr⟩
  have hinl : IsClosedEmbedding (ConcreteCategory.hom inl) :=
    IsClosedEmbedding.inl
  have hinr : IsClosedEmbedding (ConcreteCategory.hom inr) :=
    IsClosedEmbedding.inr
  have hi' : IsClosedEmbedding (ConcreteCategory.hom i') := by
    exact hi
  have tensor_fst
      {A B C D : CompactlyGenerated.{u, v}}
      (a : A ⟶ B) (b : C ⟶ D) (p : ↥((A ⊗ C).toTop)) :
      CartesianMonoidalCategory.fst B D ((a ⊗ₘ b) p) =
        a (CartesianMonoidalCategory.fst A C p) :=
    ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_fst a b) p
  have tensor_snd
      {A B C D : CompactlyGenerated.{u, v}}
      (a : A ⟶ B) (b : C ⟶ D) (p : ↥((A ⊗ C).toTop)) :
      CartesianMonoidalCategory.snd B D ((a ⊗ₘ b) p) =
        b (CartesianMonoidalCategory.snd A C p) :=
    ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.tensorHom_snd a b) p
  have lift_fst_point
      {T A B : CompactlyGenerated.{u, v}}
      (a : T ⟶ A) (b : T ⟶ B) (t : T) :
      CartesianMonoidalCategory.fst A B
          (CartesianMonoidalCategory.lift a b t) = a t :=
    ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst a b) t
  have lift_snd_point
      {T A B : CompactlyGenerated.{u, v}}
      (a : T ⟶ A) (b : T ⟶ B) (t : T) :
      CartesianMonoidalCategory.snd A B
          (CartesianMonoidalCategory.lift a b t) = b t :=
    ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd a b) t
  let pairPoint (A B : CompactlyGenerated.{u, v}) (a : A) (b : B) :
      ↥((A ⊗ B).toTop) :=
    let P : CompactlyGenerated.{u, v} :=
      CompactlyGenerated.of PUnit.{v + 1}
    let ca : P ⟶ A :=
      ConcreteCategory.ofHom
        ⟨fun _ : PUnit.{v + 1} => a, continuous_const⟩
    let cb : P ⟶ B :=
      ConcreteCategory.ofHom
        ⟨fun _ : PUnit.{v + 1} => b, continuous_const⟩
    CartesianMonoidalCategory.lift ca cb
      (PUnit.unit : PUnit.{v + 1})
  have pairPoint_fst (A B : CompactlyGenerated.{u, v}) (a : A) (b : B) :
      CartesianMonoidalCategory.fst A B (pairPoint A B a b) = a := by
    let P : CompactlyGenerated.{u, v} :=
      CompactlyGenerated.of PUnit.{v + 1}
    let ca : P ⟶ A := ConcreteCategory.ofHom
      ⟨fun _ : PUnit.{v + 1} => a, continuous_const⟩
    let cb : P ⟶ B := ConcreteCategory.ofHom
      ⟨fun _ : PUnit.{v + 1} => b, continuous_const⟩
    change CartesianMonoidalCategory.fst A B
      (CartesianMonoidalCategory.lift ca cb
        (PUnit.unit : PUnit.{v + 1})) = a
    exact (lift_fst_point ca cb
      (PUnit.unit : PUnit.{v + 1})).trans rfl
  have pairPoint_snd (A B : CompactlyGenerated.{u, v}) (a : A) (b : B) :
      CartesianMonoidalCategory.snd A B (pairPoint A B a b) = b := by
    let P : CompactlyGenerated.{u, v} :=
      CompactlyGenerated.of PUnit.{v + 1}
    let ca : P ⟶ A := ConcreteCategory.ofHom
      ⟨fun _ : PUnit.{v + 1} => a, continuous_const⟩
    let cb : P ⟶ B := ConcreteCategory.ofHom
      ⟨fun _ : PUnit.{v + 1} => b, continuous_const⟩
    change CartesianMonoidalCategory.snd A B
      (CartesianMonoidalCategory.lift ca cb
        (PUnit.unit : PUnit.{v + 1})) = b
    exact (lift_snd_point ca cb
      (PUnit.unit : PUnit.{v + 1})).trans rfl
  have point_ext (A B : CompactlyGenerated.{u, v})
      {p q : ↥((A ⊗ B).toTop)}
      (hfst : CartesianMonoidalCategory.fst A B p =
        CartesianMonoidalCategory.fst A B q)
      (hsnd : CartesianMonoidalCategory.snd A B p =
        CartesianMonoidalCategory.snd A B q) : p = q := by
    let P : CompactlyGenerated.{u, v} :=
      CompactlyGenerated.of PUnit.{v + 1}
    let cp : P ⟶ A ⊗ B :=
      ConcreteCategory.ofHom ⟨fun _ => p, continuous_const⟩
    let cq : P ⟶ A ⊗ B :=
      ConcreteCategory.ofHom ⟨fun _ => q, continuous_const⟩
    have hpq : cp = cq := by
      apply CartesianMonoidalCategory.hom_ext
      · apply ConcreteCategory.hom_ext
        intro z
        exact hfst
      · apply ConcreteCategory.hom_ext
        intro z
        exact hsnd
    exact ConcreteCategory.congr_hom hpq
      (PUnit.unit : PUnit.{v + 1})
  let diagonalX : Set ↥((X' ⊗ X').toTop) :=
    {p | CartesianMonoidalCategory.fst X' X' p =
      CartesianMonoidalCategory.snd X' X' p}
  let diagonalY : Set ↥((Y' ⊗ Y').toTop) :=
    {p | CartesianMonoidalCategory.fst Y' Y' p =
      CartesianMonoidalCategory.snd Y' Y' p}
  have hdiagonalX : IsClosed diagonalX :=
    (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
      X').mp X.is_weakHausdorff
  have hdiagonalY : IsClosed diagonalY :=
    (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
      Y').mp Y.is_weakHausdorff
  let ff : W' ⊗ W' ⟶ Y' ⊗ Y' := f' ⊗ₘ f'
  let kernel : Set ↥((W' ⊗ W').toTop) :=
    {p | f' (CartesianMonoidalCategory.fst W' W' p) =
      f' (CartesianMonoidalCategory.snd W' W' p)}
  have hkernel : IsClosed kernel := by
    rw [show kernel = (ConcreteCategory.hom ff) ⁻¹' diagonalY by
      ext p
      change (f' (CartesianMonoidalCategory.fst W' W' p) =
        f' (CartesianMonoidalCategory.snd W' W' p)) ↔
        CartesianMonoidalCategory.fst Y' Y' (ff p) =
          CartesianMonoidalCategory.snd Y' Y' (ff p)
      rw [tensor_fst, tensor_snd]]
    exact hdiagonalY.preimage (ConcreteCategory.hom ff).continuous
  let ii : W' ⊗ W' ⟶ X' ⊗ X' := i' ⊗ₘ i'
  have hii : IsClosedEmbedding (ConcreteCategory.hom ii) :=
    CompactlyGenerated.isClosedEmbedding_prodMap i' i' hi' hi'
  let kernelImage : Set ↥((X' ⊗ X').toTop) :=
    ConcreteCategory.hom ii '' kernel
  have hkernelImage : IsClosed kernelImage :=
    hii.isClosedMap _ hkernel
  let xPiece := diagonalX ∪ kernelImage
  have hxPiece : IsClosed xPiece := hdiagonalX.union hkernelImage
  let gamma : W' ⟶ W' ⊗ Y' :=
    CartesianMonoidalCategory.lift (𝟙 W') f'
  have hgammaEmbedding : IsEmbedding (ConcreteCategory.hom gamma) := by
    have hleft : Function.LeftInverse
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.fst W' Y'))
        (ConcreteCategory.hom gamma) := by
      intro w
      exact lift_fst_point (𝟙 W') f' w
    exact hleft.isEmbedding
      (ConcreteCategory.hom
        (CartesianMonoidalCategory.fst W' Y')).continuous
      (ConcreteCategory.hom gamma).continuous
  let gammaTest : W' ⊗ Y' ⟶ Y' ⊗ Y' :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst W' Y' ≫ f')
      (CartesianMonoidalCategory.snd W' Y')
  have gamma_fst (w : W') :
      CartesianMonoidalCategory.fst W' Y' (gamma w) = w := by
    change CartesianMonoidalCategory.fst W' Y'
      (CartesianMonoidalCategory.lift (𝟙 W') f' w) = w
    simp only [lift_fst_point, ConcreteCategory.id_apply]
  have gamma_snd (w : W') :
      CartesianMonoidalCategory.snd W' Y' (gamma w) = f' w := by
    change CartesianMonoidalCategory.snd W' Y'
      (CartesianMonoidalCategory.lift (𝟙 W') f' w) = f' w
    exact lift_snd_point (𝟙 W') f' w
  have gammaTest_fst (p : ↥((W' ⊗ Y').toTop)) :
      CartesianMonoidalCategory.fst Y' Y' (gammaTest p) =
        f' (CartesianMonoidalCategory.fst W' Y' p) := by
    change CartesianMonoidalCategory.fst Y' Y'
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst W' Y' ≫ f')
        (CartesianMonoidalCategory.snd W' Y') p) = _
    simp only [lift_fst_point, ConcreteCategory.comp_apply]
  have gammaTest_snd (p : ↥((W' ⊗ Y').toTop)) :
      CartesianMonoidalCategory.snd Y' Y' (gammaTest p) =
        CartesianMonoidalCategory.snd W' Y' p := by
    change CartesianMonoidalCategory.snd Y' Y'
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst W' Y' ≫ f')
        (CartesianMonoidalCategory.snd W' Y') p) = _
    exact lift_snd_point _ _ p
  have hgammaRange : IsClosed (Set.range (ConcreteCategory.hom gamma)) := by
    rw [show Set.range (ConcreteCategory.hom gamma) =
        (ConcreteCategory.hom gammaTest) ⁻¹' diagonalY by
      ext p
      constructor
      · rintro ⟨w, rfl⟩
        change gammaTest (gamma w) ∈ diagonalY
        dsimp only [diagonalY]
        change CartesianMonoidalCategory.fst Y' Y'
            (gammaTest (gamma w)) =
          CartesianMonoidalCategory.snd Y' Y'
            (gammaTest (gamma w))
        rw [gammaTest_fst, gammaTest_snd, gamma_fst, gamma_snd]
      · intro hp
        refine ⟨CartesianMonoidalCategory.fst W' Y' p, ?_⟩
        apply point_ext W' Y'
        · exact gamma_fst _
        · rw [gamma_snd]
          change gammaTest p ∈ diagonalY at hp
          dsimp only [diagonalY] at hp
          have hp' : CartesianMonoidalCategory.fst Y' Y' (gammaTest p) =
              CartesianMonoidalCategory.snd Y' Y' (gammaTest p) := hp
          rw [gammaTest_fst, gammaTest_snd] at hp'
          exact hp']
    exact hdiagonalY.preimage
      (ConcreteCategory.hom gammaTest).continuous
  have hgamma : IsClosedEmbedding (ConcreteCategory.hom gamma) :=
    ⟨hgammaEmbedding, hgammaRange⟩
  let iY : W' ⊗ Y' ⟶ X' ⊗ Y' := i' ⊗ₘ 𝟙 Y'
  have hiY : IsClosedEmbedding (ConcreteCategory.hom iY) :=
    CompactlyGenerated.isClosedEmbedding_prodMap i' (𝟙 Y') hi'
      IsClosedEmbedding.id
  let graphXY : W' ⟶ X' ⊗ Y' := gamma ≫ iY
  have hgraphXY : IsClosedEmbedding (ConcreteCategory.hom graphXY) := by
    change IsClosedEmbedding
      (ConcreteCategory.hom iY ∘ ConcreteCategory.hom gamma)
    exact hiY.comp hgamma
  let _ : BraidedCategory CompactlyGenerated.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let graphYX : W' ⟶ Y' ⊗ X' := graphXY ≫ (β_ X' Y').hom
  have hbraid : IsClosedEmbedding
      (ConcreteCategory.hom (β_ X' Y').hom) :=
    (CompactlyGenerated.homeoOfIso (β_ X' Y')).isHomeomorph.isClosedEmbedding
  have hgraphYX : IsClosedEmbedding (ConcreteCategory.hom graphYX) := by
    change IsClosedEmbedding
      (ConcreteCategory.hom (β_ X' Y').hom ∘
        ConcreteCategory.hom graphXY)
    exact hbraid.comp hgraphXY
  have graphXY_fst (w : W') :
      CartesianMonoidalCategory.fst X' Y' (graphXY w) = i' w := by
    change CartesianMonoidalCategory.fst X' Y' (iY (gamma w)) = i' w
    rw [tensor_fst, gamma_fst]
  have graphXY_snd (w : W') :
      CartesianMonoidalCategory.snd X' Y' (graphXY w) = f' w := by
    change CartesianMonoidalCategory.snd X' Y' (iY (gamma w)) = f' w
    rw [tensor_snd, gamma_snd]
    simp only [ConcreteCategory.id_apply]
  have graphYX_fst (w : W') :
      CartesianMonoidalCategory.fst Y' X' (graphYX w) = f' w := by
    change CartesianMonoidalCategory.fst Y' X'
      ((β_ X' Y').hom (graphXY w)) = f' w
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.braiding_hom_fst X' Y') (graphXY w)
    change CartesianMonoidalCategory.fst Y' X'
        ((β_ X' Y').hom (graphXY w)) =
      CartesianMonoidalCategory.snd X' Y' (graphXY w) at h
    exact h.trans (graphXY_snd w)
  have graphYX_snd (w : W') :
      CartesianMonoidalCategory.snd Y' X' (graphYX w) = i' w := by
    change CartesianMonoidalCategory.snd Y' X'
      ((β_ X' Y').hom (graphXY w)) = i' w
    have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.braiding_hom_snd X' Y') (graphXY w)
    change CartesianMonoidalCategory.snd Y' X'
        ((β_ X' Y').hom (graphXY w)) =
      CartesianMonoidalCategory.fst X' Y' (graphXY w) at h
    exact h.trans (graphXY_fst w)
  let qXX : X' ⊗ X' ⟶ S ⊗ S := inl ⊗ₘ inl
  let qXY : X' ⊗ Y' ⟶ S ⊗ S := inl ⊗ₘ inr
  let qYX : Y' ⊗ X' ⟶ S ⊗ S := inr ⊗ₘ inl
  let qYY : Y' ⊗ Y' ⟶ S ⊗ S := inr ⊗ₘ inr
  have hqXX : IsClosedEmbedding (ConcreteCategory.hom qXX) :=
    CompactlyGenerated.isClosedEmbedding_prodMap inl inl hinl hinl
  have hqXY : IsClosedEmbedding (ConcreteCategory.hom qXY) :=
    CompactlyGenerated.isClosedEmbedding_prodMap inl inr hinl hinr
  have hqYX : IsClosedEmbedding (ConcreteCategory.hom qYX) :=
    CompactlyGenerated.isClosedEmbedding_prodMap inr inl hinr hinl
  have hqYY : IsClosedEmbedding (ConcreteCategory.hom qYY) :=
    CompactlyGenerated.isClosedEmbedding_prodMap inr inr hinr hinr
  let relationClosed : Set ↥((S ⊗ S).toTop) :=
    (ConcreteCategory.hom qXX '' xPiece) ∪
      ((ConcreteCategory.hom qXY '' Set.range
          (ConcreteCategory.hom graphXY)) ∪
        ((ConcreteCategory.hom qYX '' Set.range
            (ConcreteCategory.hom graphYX)) ∪
          (ConcreteCategory.hom qYY '' diagonalY)))
  have hrelationClosed : IsClosed relationClosed :=
    (hqXX.isClosedMap _ hxPiece).union
      ((hqXY.isClosedMap _ hgraphXY.isClosed_range).union
        ((hqYX.isClosedMap _ hgraphYX.isClosed_range).union
          (hqYY.isClosedMap _ hdiagonalY)))
  unfold closedEquivalenceRelation
  rw [show {p : ↥((S ⊗ S).toTop) |
      closedPushoutSetoid i f hi
        (CartesianMonoidalCategory.fst S S p)
        (CartesianMonoidalCategory.snd S S p)} = relationClosed by
    ext p
    constructor
    · intro hp
      change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
        (CartesianMonoidalCategory.fst S S p)
        (CartesianMonoidalCategory.snd S S p) at hp
      generalize ha : CartesianMonoidalCategory.fst S S p = a at hp
      generalize hb : CartesianMonoidalCategory.snd S S p = b at hp
      rcases hp with (_ | ⟨w, w', hw⟩ | w | w)
      · rcases a with x | y
        · let q := pairPoint X' X' x x
          refine Or.inl ⟨q, Or.inl ?_, ?_⟩
          · exact (pairPoint_fst X' X' x x).trans
              (pairPoint_snd X' X' x x).symm
          · apply point_ext S S
            · rw [tensor_fst]
              rw [show CartesianMonoidalCategory.fst X' X' q = x by
                simpa only [q] using pairPoint_fst X' X' x x]
              change Sum.inl x = CartesianMonoidalCategory.fst S S p
              exact ha.symm
            · rw [tensor_snd]
              rw [show CartesianMonoidalCategory.snd X' X' q = x by
                simpa only [q] using pairPoint_snd X' X' x x]
              change Sum.inl x = CartesianMonoidalCategory.snd S S p
              exact hb.symm
        · let q := pairPoint Y' Y' y y
          refine Or.inr (Or.inr (Or.inr ⟨q, ?_, ?_⟩))
          · exact (pairPoint_fst Y' Y' y y).trans
              (pairPoint_snd Y' Y' y y).symm
          · apply point_ext S S
            · rw [tensor_fst]
              rw [show CartesianMonoidalCategory.fst Y' Y' q = y by
                simpa only [q] using pairPoint_fst Y' Y' y y]
              change Sum.inr y = CartesianMonoidalCategory.fst S S p
              exact ha.symm
            · rw [tensor_snd]
              rw [show CartesianMonoidalCategory.snd Y' Y' q = y by
                simpa only [q] using pairPoint_snd Y' Y' y y]
              change Sum.inr y = CartesianMonoidalCategory.snd S S p
              exact hb.symm
      · let r := pairPoint W' W' w w'
        let q := ii r
        refine Or.inl ⟨q, Or.inr ⟨r, ?_, rfl⟩, ?_⟩
        · change f' w = f' w' at hw
          dsimp only [kernel]
          change f' (CartesianMonoidalCategory.fst W' W' r) =
            f' (CartesianMonoidalCategory.snd W' W' r)
          rw [show CartesianMonoidalCategory.fst W' W' r = w by
              simpa only [r] using pairPoint_fst W' W' w w',
            show CartesianMonoidalCategory.snd W' W' r = w' by
              simpa only [r] using pairPoint_snd W' W' w w']
          exact hw
        · apply point_ext S S
          · rw [tensor_fst, tensor_fst]
            rw [show CartesianMonoidalCategory.fst W' W' r = w by
              simpa only [r] using pairPoint_fst W' W' w w']
            change Sum.inl (i₀ w) =
              CartesianMonoidalCategory.fst S S p
            exact ha.symm
          · rw [tensor_snd, tensor_snd]
            rw [show CartesianMonoidalCategory.snd W' W' r = w' by
              simpa only [r] using pairPoint_snd W' W' w w']
            change Sum.inl (i₀ w') =
              CartesianMonoidalCategory.snd S S p
            exact hb.symm
      · let q := graphXY w
        refine Or.inr (Or.inl ⟨q, ⟨w, rfl⟩, ?_⟩)
        apply point_ext S S
        · rw [tensor_fst]
          rw [show CartesianMonoidalCategory.fst X' Y' q = i' w by
            simpa only [q] using graphXY_fst w]
          change Sum.inl (i₀ w) =
            CartesianMonoidalCategory.fst S S p
          exact ha.symm
        · rw [tensor_snd]
          rw [show CartesianMonoidalCategory.snd X' Y' q = f' w by
            simpa only [q] using graphXY_snd w]
          change Sum.inr (f₀ w) =
            CartesianMonoidalCategory.snd S S p
          exact hb.symm
      · let q := graphYX w
        refine Or.inr (Or.inr (Or.inl ⟨q, ⟨w, rfl⟩, ?_⟩))
        apply point_ext S S
        · rw [tensor_fst]
          rw [show CartesianMonoidalCategory.fst Y' X' q = f' w by
            simpa only [q] using graphYX_fst w]
          change Sum.inr (f₀ w) =
            CartesianMonoidalCategory.fst S S p
          exact ha.symm
        · rw [tensor_snd]
          rw [show CartesianMonoidalCategory.snd Y' X' q = i' w by
            simpa only [q] using graphYX_snd w]
          change Sum.inl (i₀ w) =
            CartesianMonoidalCategory.snd S S p
          exact hb.symm
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩ |
          ⟨q, ⟨w, rfl⟩, rfl⟩ |
          ⟨q, ⟨w, rfl⟩, rfl⟩ |
          ⟨q, hq, rfl⟩
      · change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
          (CartesianMonoidalCategory.fst S S (qXX q))
          (CartesianMonoidalCategory.snd S S (qXX q))
        rw [tensor_fst, tensor_snd]
        rcases hq with hdiag | ⟨r, hr, rfl⟩
        · change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
            (Sum.inl (CartesianMonoidalCategory.fst X' X' q))
            (Sum.inl (CartesianMonoidalCategory.snd X' X' q))
          rw [hdiag]
          exact CategoryTheory.Limits.Types.Pushout.Rel'.refl _
        · rw [tensor_fst, tensor_snd]
          change f' (CartesianMonoidalCategory.fst W' W' r) =
            f' (CartesianMonoidalCategory.snd W' W' r) at hr
          exact CategoryTheory.Limits.Types.Pushout.Rel'.inl_inl _ _ hr
      · change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
          (CartesianMonoidalCategory.fst S S (qXY (graphXY w)))
          (CartesianMonoidalCategory.snd S S (qXY (graphXY w)))
        rw [tensor_fst, tensor_snd, graphXY_fst, graphXY_snd]
        exact CategoryTheory.Limits.Types.Pushout.Rel'.inl_inr _
      · change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
          (CartesianMonoidalCategory.fst S S (qYX (graphYX w)))
          (CartesianMonoidalCategory.snd S S (qYX (graphYX w)))
        rw [tensor_fst, tensor_snd, graphYX_fst, graphYX_snd]
        exact CategoryTheory.Limits.Types.Pushout.Rel'.inr_inl _
      · change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀
          (CartesianMonoidalCategory.fst S S (qYY q))
          (CartesianMonoidalCategory.snd S S (qYY q))
        rw [tensor_fst, tensor_snd, hq]
        exact CategoryTheory.Limits.Types.Pushout.Rel'.refl _]
  exact hrelationClosed

private noncomputable def closedPushoutCocone
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    PushoutCocone (cgwhToTop.map i) (cgwhToTop.map f) := by
  let s := closedPushoutSetoid i f hi
  let Q : TopCat.{v} := TopCat.of (Quotient s)
  let qX : cgwhToTop.obj X ⟶ Q := TopCat.ofHom
    ⟨fun x => @Quotient.mk' _ s (Sum.inl x),
      continuous_quotient_mk'.comp continuous_inl⟩
  let qY : cgwhToTop.obj Y ⟶ Q := TopCat.ofHom
    ⟨fun y => @Quotient.mk' _ s (Sum.inr y),
      continuous_quotient_mk'.comp continuous_inr⟩
  refine PushoutCocone.mk qX qY ?_
  apply TopCat.hom_ext
  ext w
  apply Quotient.sound
  exact CategoryTheory.Limits.Types.Pushout.Rel'.inl_inr _

private noncomputable def closedPushoutCoconeIsColimit
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    IsColimit (closedPushoutCocone i f hi) := by
  let s := closedPushoutSetoid i f hi
  let Q : TopCat.{v} := TopCat.of (Quotient s)
  let qX : cgwhToTop.obj X ⟶ Q := TopCat.ofHom
    ⟨fun x => @Quotient.mk' _ s (Sum.inl x),
      continuous_quotient_mk'.comp continuous_inl⟩
  let qY : cgwhToTop.obj Y ⟶ Q := TopCat.ofHom
    ⟨fun y => @Quotient.mk' _ s (Sum.inr y),
      continuous_quotient_mk'.comp continuous_inr⟩
  let i₀ : (↥(cgwhToTop.obj W) : Type v) ⟶
      (↥(cgwhToTop.obj X) : Type v) :=
    TypeCat.ofHom (ConcreteCategory.hom (cgwhToTop.map i))
  let f₀ : (↥(cgwhToTop.obj W) : Type v) ⟶
      (↥(cgwhToTop.obj Y) : Type v) :=
    TypeCat.ofHom (ConcreteCategory.hom (cgwhToTop.map f))
  let descend (t : PushoutCocone (cgwhToTop.map i) (cgwhToTop.map f)) :
      Q ⟶ t.pt := by
    let h : C(↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y), t.pt) :=
      ⟨Sum.elim t.inl t.inr,
        (ConcreteCategory.hom t.inl).continuous.sumElim
          (ConcreteCategory.hom t.inr).continuous⟩
    have hrespects : ∀ a b, s a b → h a = h b := by
      intro a b hab
      change CategoryTheory.Limits.Types.Pushout.Rel' i₀ f₀ a b at hab
      rcases hab with (_ | ⟨w, w', hw⟩ | w | w)
      · rfl
      · have hc (z : W) := ConcreteCategory.congr_hom t.condition z
        calc
          t.inl (i₀ w) = t.inr (f₀ w) := hc w
          _ = t.inr (f₀ w') := congrArg t.inr hw
          _ = t.inl (i₀ w') := (hc w').symm
      · exact ConcreteCategory.congr_hom t.condition w
      · exact (ConcreteCategory.congr_hom t.condition w).symm
    exact TopCat.ofHom
      ⟨Quotient.lift h hrespects,
        h.continuous.quotient_lift hrespects⟩
  have hcond : cgwhToTop.map i ≫ qX = cgwhToTop.map f ≫ qY := by
    apply TopCat.hom_ext
    ext w
    apply Quotient.sound
    exact CategoryTheory.Limits.Types.Pushout.Rel'.inl_inr _
  change IsColimit (PushoutCocone.mk qX qY hcond)
  refine PushoutCocone.IsColimit.mk hcond descend ?_ ?_ ?_
  · intro t
    apply TopCat.hom_ext
    ext x
    rfl
  · intro t
    apply TopCat.hom_ext
    ext y
    rfl
  · intro t m hmX hmY
    apply TopCat.hom_ext
    ext z
    induction z using Quotient.inductionOn'
    rename_i z
    rcases z with x | y
    · exact ConcreteCategory.congr_hom hmX x
    · exact ConcreteCategory.congr_hom hmY y

private noncomputable def closedPushoutQuotientIso
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    TopCat.of (Quotient (closedPushoutSetoid i f hi)) ≅
      pushout (cgwhToTop.map i) (cgwhToTop.map f) := by
  change (closedPushoutCocone i f hi).pt ≅
    (PushoutCocone.mk
      (pushout.inl (cgwhToTop.map i) (cgwhToTop.map f))
      (pushout.inr (cgwhToTop.map i) (cgwhToTop.map f))
      (pushout.condition : _)).pt
  exact (closedPushoutCoconeIsColimit i f hi).coconePointUniqueUpToIso
    (pushoutIsPushout (cgwhToTop.map i) (cgwhToTop.map f))

private theorem rawPushout_isWeakHausdorff
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    UWeakHausdorffSpace.{u}
      ↥(pushout (cgwhToTop.map i) (cgwhToTop.map f)) := by
  let _ : UCompactlyGeneratedSpace.{u} ↥(cgwhToTop.obj X) :=
    X.toCompactlyGenerated.is_compactly_generated
  let _ : UCompactlyGeneratedSpace.{u} ↥(cgwhToTop.obj Y) :=
    Y.toCompactlyGenerated.is_compactly_generated
  let _ : UCompactlyGeneratedSpace.{u}
      (↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y)) := by
    apply uCompactlyGeneratedSpace_of_isClosed
    intro A hA
    rw [isClosed_sum_iff]
    constructor
    · apply UCompactlyGeneratedSpace.isClosed
      intro K g
      have h := hA K
        ⟨Sum.inl ∘ g, continuous_inl.comp g.continuous⟩
      change IsClosed ((fun x => Sum.inl (g x)) ⁻¹' A)
      change IsClosed ((fun x => Sum.inl (g x)) ⁻¹' A) at h
      exact h
    · apply UCompactlyGeneratedSpace.isClosed
      intro K g
      have h := hA K
        ⟨Sum.inr ∘ g, continuous_inr.comp g.continuous⟩
      change IsClosed ((fun x => Sum.inr (g x)) ⁻¹' A)
      change IsClosed ((fun x => Sum.inr (g x)) ⁻¹' A) at h
      exact h
  let S : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of (↥(cgwhToTop.obj X) ⊕ ↥(cgwhToTop.obj Y))
  let s := closedPushoutSetoid i f hi
  have hs : closedEquivalenceRelation S s :=
    closedPushoutSetoid_isClosed i f hi
  have hQ : UWeakHausdorffSpace.{u} (Quotient s) :=
    (quotient_isWeakHausdorff_iff_isClosed S s).2 hs
  let e : Quotient s ≃ₜ
      ↥(pushout (cgwhToTop.map i) (cgwhToTop.map f)) :=
    TopCat.homeoOfIso (closedPushoutQuotientIso i f hi)
  refine ⟨fun K g => ?_⟩
  let g' : C(K, Quotient s) :=
    ⟨fun k => e.symm (g k), e.symm.continuous.comp g.continuous⟩
  have hc : IsClosed (Set.range g') := hQ.isClosed_range K g'
  have hrange : Set.range g = e '' Set.range g' := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨g' k, ⟨k, rfl⟩, e.apply_symm_apply (g k)⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (e.apply_symm_apply (g k)).symm⟩
  rw [hrange]
  exact e.isClosedMap _ hc

/-- A pushout along a closed embedding is created by the inclusion of CGWH
spaces into topological spaces. -/
noncomputable def pushoutClosedComparisonIso
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    pushout (cgwhToTop.map i) (cgwhToTop.map f) ≅
      cgwhToTop.obj (pushout i f) := by
  let E : WalkingSpan ≌
      ULiftHom.{v} (ULift.{v} WalkingSpan) :=
    ULiftHomULiftCategory.equiv WalkingSpan
  let F : ULiftHom.{v} (ULift.{v} WalkingSpan) ⥤ CGWH.{u, v} :=
    E.inverse ⋙ span.{v} i f
  let commute : E.functor ⋙ F ≅ span.{v} i f :=
    (Functor.associator E.functor E.inverse (span.{v} i f)).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm (span.{v} i f) ≪≫
      Functor.leftUnitor (span.{v} i f)
  let nativeShapeIso : Limits.colimit (span.{v} i f) ≅
      Limits.colimit F :=
    HasColimit.isoOfEquivalence E commute
  let rawCommute : E.functor ⋙ (F ⋙ cgwhToTop) ≅
      span.{v} i f ⋙ cgwhToTop :=
    (Functor.associator E.functor F cgwhToTop).symm ≪≫
      Functor.isoWhiskerRight commute cgwhToTop
  let rawShapeIso :
      Limits.colimit (span.{v} i f ⋙ cgwhToTop) ≅
        Limits.colimit (F ⋙ cgwhToTop) :=
    HasColimit.isoOfEquivalence E rawCommute
  let sourceIso : Limits.colimit (span.{v} i f ⋙ cgwhToTop) ≅
      pushout (cgwhToTop.map i) (cgwhToTop.map f) :=
    HasColimit.isoOfNatIso (diagramIsoSpan (span.{v} i f ⋙ cgwhToTop))
  let targetIso : Limits.colimit (span.{v} i f) ≅ pushout i f :=
    HasColimit.isoOfNatIso (diagramIsoSpan (span.{v} i f))
  let e : ↥(Limits.colimit (span.{v} i f ⋙ cgwhToTop)) ≃ₜ
      ↥(pushout (cgwhToTop.map i) (cgwhToTop.map f)) :=
    TopCat.homeoOfIso sourceIso
  have homeo_preserves
      {A B : Type v} [TopologicalSpace A] [TopologicalSpace B]
      (h : A ≃ₜ B) (hA : UWeakHausdorffSpace.{u} A) :
      UWeakHausdorffSpace.{u} B := by
    refine ⟨fun K g => ?_⟩
    let g' : C(K, A) :=
      ⟨fun k => h.symm (g k), h.symm.continuous.comp g.continuous⟩
    have hc : IsClosed (Set.range g') := hA.isClosed_range K g'
    have hrange : Set.range g = h '' Set.range g' := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨g' k, ⟨k, rfl⟩, h.apply_symm_apply (g k)⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (h.apply_symm_apply (g k)).symm⟩
    rw [hrange]
    exact h.isClosedMap _ hc
  have hcolim : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (span.{v} i f ⋙ cgwhToTop)) :=
    homeo_preserves e.symm (rawPushout_isWeakHausdorff i f hi)
  have hLifted : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ cgwhToTop)) :=
    homeo_preserves (TopCat.homeoOfIso rawShapeIso) hcolim
  have hcomparison : IsHomeomorph (colimitComparisonFromTop F) :=
    (colimitComparisonFromTop_isHomeomorph_iff F).2 hLifted
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2 hcomparison
  let result := sourceIso.symm ≪≫ rawShapeIso ≪≫
    asIso (colimitComparisonFromTop F) ≪≫
      cgwhToTop.mapIso (nativeShapeIso.symm ≪≫ targetIso)
  exact result

/-- The closed-pushout comparison carries the raw left injection to the
included native left injection. -/
theorem pushoutClosedComparisonIso_hom_inl
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    pushout.inl (cgwhToTop.map i) (cgwhToTop.map f) ≫
        (pushoutClosedComparisonIso i f hi).hom =
      cgwhToTop.map (pushout.inl i f) := by
  let E : WalkingSpan ≌
      ULiftHom.{v} (ULift.{v} WalkingSpan) :=
    ULiftHomULiftCategory.equiv WalkingSpan
  let F : ULiftHom.{v} (ULift.{v} WalkingSpan) ⥤ CGWH.{u, v} :=
    E.inverse ⋙ span.{v} i f
  let commute : E.functor ⋙ F ≅ span.{v} i f :=
    (Functor.associator E.functor E.inverse (span.{v} i f)).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm (span.{v} i f) ≪≫
      Functor.leftUnitor (span.{v} i f)
  let nativeShapeIso : Limits.colimit (span.{v} i f) ≅
      Limits.colimit F :=
    HasColimit.isoOfEquivalence E commute
  let rawCommute : E.functor ⋙ (F ⋙ cgwhToTop) ≅
      span.{v} i f ⋙ cgwhToTop :=
    (Functor.associator E.functor F cgwhToTop).symm ≪≫
      Functor.isoWhiskerRight commute cgwhToTop
  let rawShapeIso :
      Limits.colimit (span.{v} i f ⋙ cgwhToTop) ≅
        Limits.colimit (F ⋙ cgwhToTop) :=
    HasColimit.isoOfEquivalence E rawCommute
  let sourceIso : Limits.colimit (span.{v} i f ⋙ cgwhToTop) ≅
      pushout (cgwhToTop.map i) (cgwhToTop.map f) :=
    HasColimit.isoOfNatIso (diagramIsoSpan (span.{v} i f ⋙ cgwhToTop))
  let targetIso : Limits.colimit (span.{v} i f) ≅ pushout i f :=
    HasColimit.isoOfNatIso (diagramIsoSpan (span.{v} i f))
  have hshape : commute.inv.app WalkingSpan.left ≫
        Limits.colimit.ι F (E.functor.obj WalkingSpan.left) ≫
        nativeShapeIso.inv =
      Limits.colimit.ι (span.{v} i f) WalkingSpan.left := by
    rw [← Category.assoc,
      ← HasColimit.ι_isoOfEquivalence_hom E commute]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hshapeTop :
      cgwhToTop.map (commute.inv.app WalkingSpan.left) ≫
          cgwhToTop.map
            (Limits.colimit.ι F (E.functor.obj WalkingSpan.left)) ≫
          cgwhToTop.map nativeShapeIso.inv =
        cgwhToTop.map
          (Limits.colimit.ι (span.{v} i f) WalkingSpan.left) := by
    rw [← cgwhToTop.map_comp, ← cgwhToTop.map_comp, hshape]
  have hshapeTopAssoc :
      cgwhToTop.map (commute.inv.app WalkingSpan.left) ≫
          CompactlyGenerated.compactlyGeneratedToTop.map
            (cgwhToCompactlyGenerated.map
              (Limits.colimit.ι F (E.functor.obj WalkingSpan.left))) ≫
          cgwhToTop.map nativeShapeIso.inv ≫
          cgwhToTop.map targetIso.hom =
          cgwhToTop.map
            (Limits.colimit.ι (span.{v} i f) WalkingSpan.left) ≫
          cgwhToTop.map targetIso.hom := by
    apply TopCat.hom_ext
    ext x
    have h := congrArg
      (fun q => q ≫ cgwhToTop.map targetIso.hom) hshapeTop
    exact ConcreteCategory.congr_hom h x
  have hsource :
      pushout.inl (cgwhToTop.map i) (cgwhToTop.map f) ≫
          sourceIso.inv =
        Limits.colimit.ι (span.{v} i f ⋙ cgwhToTop)
          WalkingSpan.left := by
    apply (cancel_mono sourceIso.hom).1
    simp [sourceIso]
  have hrawCommute : rawCommute.inv.app WalkingSpan.left =
      cgwhToTop.map (commute.inv.app WalkingSpan.left) := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hrawShape :
      Limits.colimit.ι (span.{v} i f ⋙ cgwhToTop)
          WalkingSpan.left ≫ rawShapeIso.hom =
        rawCommute.inv.app WalkingSpan.left ≫
          Limits.colimit.ι (F ⋙ cgwhToTop)
            (E.functor.obj WalkingSpan.left) :=
    HasColimit.ι_isoOfEquivalence_hom E rawCommute WalkingSpan.left
  have htarget :
      Limits.colimit.ι (span.{v} i f) WalkingSpan.left ≫
          targetIso.hom = pushout.inl i f := by
    simp [targetIso]
  have homeo_preserves
      {A B : Type v} [TopologicalSpace A] [TopologicalSpace B]
      (h : A ≃ₜ B) (hA : UWeakHausdorffSpace.{u} A) :
      UWeakHausdorffSpace.{u} B := by
    refine ⟨fun K g => ?_⟩
    let g' : C(K, A) :=
      ⟨fun k => h.symm (g k), h.symm.continuous.comp g.continuous⟩
    have hc : IsClosed (Set.range g') := hA.isClosed_range K g'
    have hrange : Set.range g = h '' Set.range g' := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨g' k, ⟨k, rfl⟩, h.apply_symm_apply (g k)⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (h.apply_symm_apply (g k)).symm⟩
    rw [hrange]
    exact h.isClosedMap _ hc
  have hOriginal : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (span.{v} i f ⋙ cgwhToTop)) :=
    homeo_preserves (TopCat.homeoOfIso sourceIso).symm
      (rawPushout_isWeakHausdorff i f hi)
  have hLifted : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ cgwhToTop)) :=
    homeo_preserves (TopCat.homeoOfIso rawShapeIso) hOriginal
  have hcomparison : IsHomeomorph (colimitComparisonFromTop F) :=
    (colimitComparisonFromTop_isHomeomorph_iff F).2 hLifted
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2 hcomparison
  change pushout.inl (cgwhToTop.map i) (cgwhToTop.map f) ≫
      (sourceIso.symm ≪≫ rawShapeIso ≪≫
        asIso (colimitComparisonFromTop F) ≪≫
        cgwhToTop.mapIso (nativeShapeIso.symm ≪≫ targetIso)).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Functor.mapIso_hom, Functor.map_comp]
  rw [← Category.assoc, hsource]
  rw [← Category.assoc, hrawShape, hrawCommute]
  rw [Category.assoc, colimitComparisonFromTop_ι_assoc]
  rw [hshapeTopAssoc]
  rw [← cgwhToTop.map_comp, htarget]

/-- The closed-pushout comparison carries the raw right injection to the
included native right injection. -/
theorem pushoutClosedComparisonIso_hom_inr
    {W X Y : CGWH.{u, v}} (i : W ⟶ X) (f : W ⟶ Y)
    (hi : IsClosedEmbedding
      (ConcreteCategory.hom (cgwhToTop.map i))) :
    pushout.inr (cgwhToTop.map i) (cgwhToTop.map f) ≫
        (pushoutClosedComparisonIso i f hi).hom =
      cgwhToTop.map (pushout.inr i f) := by
  let E : WalkingSpan ≌
      ULiftHom.{v} (ULift.{v} WalkingSpan) :=
    ULiftHomULiftCategory.equiv WalkingSpan
  let F : ULiftHom.{v} (ULift.{v} WalkingSpan) ⥤ CGWH.{u, v} :=
    E.inverse ⋙ span.{v} i f
  let commute : E.functor ⋙ F ≅ span.{v} i f :=
    (Functor.associator E.functor E.inverse (span.{v} i f)).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm (span.{v} i f) ≪≫
      Functor.leftUnitor (span.{v} i f)
  let nativeShapeIso : Limits.colimit (span.{v} i f) ≅
      Limits.colimit F :=
    HasColimit.isoOfEquivalence E commute
  let rawCommute : E.functor ⋙ (F ⋙ cgwhToTop) ≅
      span.{v} i f ⋙ cgwhToTop :=
    (Functor.associator E.functor F cgwhToTop).symm ≪≫
      Functor.isoWhiskerRight commute cgwhToTop
  let rawShapeIso :
      Limits.colimit (span.{v} i f ⋙ cgwhToTop) ≅
        Limits.colimit (F ⋙ cgwhToTop) :=
    HasColimit.isoOfEquivalence E rawCommute
  let sourceIso : Limits.colimit (span.{v} i f ⋙ cgwhToTop) ≅
      pushout (cgwhToTop.map i) (cgwhToTop.map f) :=
    HasColimit.isoOfNatIso (diagramIsoSpan (span.{v} i f ⋙ cgwhToTop))
  let targetIso : Limits.colimit (span.{v} i f) ≅ pushout i f :=
    HasColimit.isoOfNatIso (diagramIsoSpan (span.{v} i f))
  have hshape : commute.inv.app WalkingSpan.right ≫
        Limits.colimit.ι F (E.functor.obj WalkingSpan.right) ≫
        nativeShapeIso.inv =
      Limits.colimit.ι (span.{v} i f) WalkingSpan.right := by
    rw [← Category.assoc,
      ← HasColimit.ι_isoOfEquivalence_hom E commute]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hshapeTop :
      cgwhToTop.map (commute.inv.app WalkingSpan.right) ≫
          cgwhToTop.map
            (Limits.colimit.ι F (E.functor.obj WalkingSpan.right)) ≫
          cgwhToTop.map nativeShapeIso.inv =
        cgwhToTop.map
          (Limits.colimit.ι (span.{v} i f) WalkingSpan.right) := by
    rw [← cgwhToTop.map_comp, ← cgwhToTop.map_comp, hshape]
  have hshapeTopAssoc :
      cgwhToTop.map (commute.inv.app WalkingSpan.right) ≫
          CompactlyGenerated.compactlyGeneratedToTop.map
            (cgwhToCompactlyGenerated.map
              (Limits.colimit.ι F (E.functor.obj WalkingSpan.right))) ≫
          cgwhToTop.map nativeShapeIso.inv ≫
          cgwhToTop.map targetIso.hom =
        cgwhToTop.map
            (Limits.colimit.ι (span.{v} i f) WalkingSpan.right) ≫
          cgwhToTop.map targetIso.hom := by
    apply TopCat.hom_ext
    ext x
    have h := congrArg
      (fun q => q ≫ cgwhToTop.map targetIso.hom) hshapeTop
    exact ConcreteCategory.congr_hom h x
  have hsource :
      pushout.inr (cgwhToTop.map i) (cgwhToTop.map f) ≫
          sourceIso.inv =
        Limits.colimit.ι (span.{v} i f ⋙ cgwhToTop)
          WalkingSpan.right := by
    apply (cancel_mono sourceIso.hom).1
    simp [sourceIso]
  have hrawCommute : rawCommute.inv.app WalkingSpan.right =
      cgwhToTop.map (commute.inv.app WalkingSpan.right) := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hrawShape :
      Limits.colimit.ι (span.{v} i f ⋙ cgwhToTop)
          WalkingSpan.right ≫ rawShapeIso.hom =
        rawCommute.inv.app WalkingSpan.right ≫
          Limits.colimit.ι (F ⋙ cgwhToTop)
            (E.functor.obj WalkingSpan.right) :=
    HasColimit.ι_isoOfEquivalence_hom E rawCommute WalkingSpan.right
  have htarget :
      Limits.colimit.ι (span.{v} i f) WalkingSpan.right ≫
          targetIso.hom = pushout.inr i f := by
    simp [targetIso]
  have homeo_preserves
      {A B : Type v} [TopologicalSpace A] [TopologicalSpace B]
      (h : A ≃ₜ B) (hA : UWeakHausdorffSpace.{u} A) :
      UWeakHausdorffSpace.{u} B := by
    refine ⟨fun K g => ?_⟩
    let g' : C(K, A) :=
      ⟨fun k => h.symm (g k), h.symm.continuous.comp g.continuous⟩
    have hc : IsClosed (Set.range g') := hA.isClosed_range K g'
    have hrange : Set.range g = h '' Set.range g' := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨g' k, ⟨k, rfl⟩, h.apply_symm_apply (g k)⟩
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (h.apply_symm_apply (g k)).symm⟩
    rw [hrange]
    exact h.isClosedMap _ hc
  have hOriginal : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (span.{v} i f ⋙ cgwhToTop)) :=
    homeo_preserves (TopCat.homeoOfIso sourceIso).symm
      (rawPushout_isWeakHausdorff i f hi)
  have hLifted : UWeakHausdorffSpace.{u}
      ↥(Limits.colimit (F ⋙ cgwhToTop)) :=
    homeo_preserves (TopCat.homeoOfIso rawShapeIso) hOriginal
  have hcomparison : IsHomeomorph (colimitComparisonFromTop F) :=
    (colimitComparisonFromTop_isHomeomorph_iff F).2 hLifted
  let _ : IsIso (colimitComparisonFromTop F) :=
    (TopCat.isIso_iff_isHomeomorph _).2 hcomparison
  change pushout.inr (cgwhToTop.map i) (cgwhToTop.map f) ≫
      (sourceIso.symm ≪≫ rawShapeIso ≪≫
        asIso (colimitComparisonFromTop F) ≪≫
        cgwhToTop.mapIso (nativeShapeIso.symm ≪≫ targetIso)).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Functor.mapIso_hom, Functor.map_comp]
  rw [← Category.assoc, hsource]
  rw [← Category.assoc, hrawShape, hrawCommute]
  rw [Category.assoc, colimitComparisonFromTop_ι_assoc]
  rw [hshapeTopAssoc]
  rw [← cgwhToTop.map_comp, htarget]

end CGWH
