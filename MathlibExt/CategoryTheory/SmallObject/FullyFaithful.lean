/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import MathlibExt.CategoryTheory.Functor.FullyFaithfulLifting

/-!
# Small-object transfer along fully faithful functors

This file maps cell attachments and relative cell complexes through
colimit-preserving functors, and transfers small-object cardinal and
generated-left-class data through fully faithful functors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v vD uC uD

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

namespace AttachCells

/-- A colimit-preserving functor maps a cell attachment to the attachment
by the mapped family. -/
noncomputable def map
    {alpha : Type*} {A B : alpha → C}
    {g : (a : alpha) → A a ⟶ B a}
    {X Y : C} {f : X ⟶ Y}
    (c : AttachCells.{w} g f) (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} F] :
    AttachCells.{w} (fun a => F.map (g a)) (F.map f) := by
  let cofan₁ : Cofan (fun i => F.obj (A (c.π i))) :=
    Cofan.mk (F.obj c.cofan₁.pt) (fun i => F.map (c.cofan₁.inj i))
  let cofan₂ : Cofan (fun i => F.obj (B (c.π i))) :=
    Cofan.mk (F.obj c.cofan₂.pt) (fun i => F.map (c.cofan₂.inj i))
  let asMappedCocone₁ (s : Cofan (fun i => F.obj (A (c.π i)))) :
      Cocone ((Discrete.functor fun i => A (c.π i)) ⋙ F) :=
    { pt := s.pt
      ι :=
        { app := fun j => s.inj j.as
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ φ
            obtain rfl := Discrete.eq_of_hom φ
            simp } }
  let asMappedCocone₂ (s : Cofan (fun i => F.obj (B (c.π i)))) :
      Cocone ((Discrete.functor fun i => B (c.π i)) ⋙ F) :=
    { pt := s.pt
      ι :=
        { app := fun j => s.inj j.as
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ φ
            obtain rfl := Discrete.eq_of_hom φ
            simp } }
  let hc₁ := isColimitOfPreserves F c.isColimit₁
  let hc₂ := isColimitOfPreserves F c.isColimit₂
  have hcofan₁ : IsColimit cofan₁ := Cofan.IsColimit.mk cofan₁
      (fun s => hc₁.desc (asMappedCocone₁ s))
      (fun s i => hc₁.fac (asMappedCocone₁ s) ⟨i⟩)
      (fun s m hm => hc₁.uniq (asMappedCocone₁ s) m (fun ⟨i⟩ => hm i))
  have hcofan₂ : IsColimit cofan₂ := Cofan.IsColimit.mk cofan₂
      (fun s => hc₂.desc (asMappedCocone₂ s))
      (fun s i => hc₂.fac (asMappedCocone₂ s) ⟨i⟩)
      (fun s m hm => hc₂.uniq (asMappedCocone₂ s) m (fun ⟨i⟩ => hm i))
  let _ : PreservesColimitsOfSize.{0, 0} F :=
    preservesSmallestColimits_of_preservesColimits F
  exact
    { ι := c.ι
      π := c.π
      cofan₁ := cofan₁
      cofan₂ := cofan₂
      isColimit₁ := hcofan₁
      isColimit₂ := hcofan₂
      m := F.map c.m
      hm i := by
        change F.map (c.cofan₁.inj i) ≫ F.map c.m =
          F.map (g (c.π i)) ≫ F.map (c.cofan₂.inj i)
        simpa only [Functor.map_comp] using congrArg F.map (c.hm i)
      g₁ := F.map c.g₁
      g₂ := F.map c.g₂
      isPushout := c.isPushout.map F }

end AttachCells

namespace RelativeCellComplex

/-- A functor preserving the structural colimits maps a relative cell
complex to the relative complex of mapped cells. -/
noncomputable def map
    {K : Type*} [LinearOrder K] [OrderBot K] [SuccOrder K]
    [WellFoundedLT K]
    {alpha : K → Type*}
    {A B : (k : K) → alpha k → C}
    {cell : (k : K) → (a : alpha k) → A k a ⟶ B k a}
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} cell f) (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape K F]
    [PreservesWellOrderContinuousOfShape K F] :
    RelativeCellComplex.{w} (fun k a => F.map (cell k a)) (F.map f) where
  __ := c.toTransfiniteCompositionOfShape.map F
  attachCells k hk := (c.attachCells k hk).map F

/-- Reindex the mapped cells of a relative complex into an ambient
morphism property. -/
noncomputable def mapOfLE
    (F : C ⥤ D) (P : MorphismProperty C)
    (Q : MorphismProperty D) (hPQ : P ≤ Q.inverseImage F)
    {K : Type*} [LinearOrder K] [OrderBot K] [SuccOrder K]
    [WellFoundedLT K]
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun (_ : K) => P.homFamily) f)
    [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape K F]
    [PreservesWellOrderContinuousOfShape K F] :
    RelativeCellComplex.{w} (fun (_ : K) => Q.homFamily) (F.map f) where
  __ := (c.map F).toTransfiniteCompositionOfShape
  attachCells k hk :=
    ((c.attachCells k hk).map F).reindexCellTypes Q.homFamily
      (fun a => ⟨Arrow.mk (F.map a.1.hom), hPQ _ a.2⟩)
      (fun _ => Iso.refl _)

end RelativeCellComplex

end HomotopicalAlgebra

namespace CategoryTheory

variable {C : Type uC} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

namespace MorphismProperty

namespace IsCardinalForSmallObjectArgument

/-- Transfer the same small-object cardinal through a fully faithful functor
with independent Hom universes, preserving the relevant original colimits. -/
theorem of_fullyFaithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType]
    [P.IsSmall.{w}] [LocallySmall.{w} C]
    [HasPushouts C] [HasCoproducts.{w} C]
    [HasIterationOfShape κ.ord.ToType C]
    [PreservesColimitsOfSize.{w, w} F]
    [Q.IsCardinalForSmallObjectArgument κ]
    (hPQ : P ≤ Q.inverseImage F) :
    P.IsCardinalForSmallObjectArgument κ where
  preservesColimit {A B X Y} i hi f hf := by
    let _ : PreservesWellOrderContinuousOfShape κ.ord.ToType F :=
      { preservesColimitsOfShape := fun _ _ => inferInstance }
    let hfD := hf.mapOfLE F P Q hPQ
    have hAmbient : PreservesColimit hfD.F
        (coyoneda.obj (Opposite.op (F.obj A))) :=
      SmallObject.preservesColimit Q κ (F.map i) (hPQ i hi)
        (F.map f) hfD
    have hDiagram : hfD.F = hf.F ⋙ F := rfl
    let _ : PreservesColimit (hf.F ⋙ F)
        (coyoneda.obj (Opposite.op (F.obj A))) :=
      hDiagram ▸ hAmbient
    let _ : PreservesColimit hf.F F := inferInstance
    let HD : D ⥤ Type vD := coyoneda.obj (Opposite.op (F.obj A))
    let HC : C ⥤ Type v := coyoneda.obj (Opposite.op A)
    let UD : Type vD ⥤ Type (max v vD) := uliftFunctor.{v, vD}
    let UC : Type v ⥤ Type (max v vD) := uliftFunctor.{vD, v}
    let _ : PreservesColimit hf.F ((F ⋙ HD) ⋙ UD) := inferInstance
    let e : (F ⋙ HD) ⋙ UD ≅ HC ⋙ UC :=
      (Functor.associator F HD UD) ≪≫
        (Functor.FullyFaithful.ofFullyFaithful F).homNatIso' A
    let _ : PreservesColimit hf.F (HC ⋙ UC) := preservesColimit_of_natIso hf.F e
    exact preservesColimit_of_reflects_of_preserves HC UC

end IsCardinalForSmallObjectArgument

private theorem colimitsOfShape_le_inverseImage_map
    {J : Type w} [Category.{w} J]
    (F : C ⥤ D) [PreservesColimitsOfShape J F]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    (hPQ : P ≤ Q.inverseImage F) :
    P.colimitsOfShape J ≤ (Q.colimitsOfShape J).inverseImage F := by
  rintro X Y f ⟨X₁, X₂, c₁, c₂, h₁, h₂, φ, hφ⟩
  refine .mk' (X₁ ⋙ F) (X₂ ⋙ F) (F.mapCocone c₁) (F.mapCocone c₂)
    (isColimitOfPreserves F h₁) (isColimitOfPreserves F h₂)
    (Functor.whiskerRight φ F) (fun j ↦ hPQ _ (hφ j))
    (F.map (h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι)))) ?_
  intro j
  change F.map (c₁.ι.app j) ≫
      F.map (h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι))) =
    F.map (φ.app j) ≫ F.map (c₂.ι.app j)
  rw [← F.map_comp, ← F.map_comp]
  exact F.congr_map (by
    simpa only [NatTrans.comp_app] using
      h₁.fac (Cocone.mk c₂.pt (φ ≫ c₂.ι)) j)

private theorem coproducts_le_inverseImage_map
    (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    (hPQ : P ≤ Q.inverseImage F) :
    coproducts.{w} P ≤ (coproducts.{w} Q).inverseImage F := by
  intro X Y f hf
  rw [coproducts_iff] at hf
  change coproducts.{w} Q (F.map f)
  rw [coproducts_iff]
  obtain ⟨J, hf⟩ := hf
  exact ⟨J, colimitsOfShape_le_inverseImage_map F P Q hPQ _ hf⟩

private theorem pushouts_le_inverseImage_map
    (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    (hPQ : P ≤ Q.inverseImage F) :
    P.pushouts ≤ Q.pushouts.inverseImage F := by
  let _ : PreservesColimitsOfSize.{0, 0} F :=
    preservesSmallestColimits_of_preservesColimits F
  rintro X Y f ⟨A, B, p, i, r, hp, h⟩
  exact ⟨F.obj A, F.obj B, F.map p, F.map i, F.map r,
    hPQ _ hp, h.map F⟩

private theorem transfiniteCompositions_le_inverseImage_map
    (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    (hPQ : P ≤ Q.inverseImage F) :
    transfiniteCompositions.{w} P ≤
      (transfiniteCompositions.{w} Q).inverseImage F := by
  intro X Y f hf
  rw [transfiniteCompositions_iff] at hf
  change transfiniteCompositions.{w} Q (F.map f)
  rw [transfiniteCompositions_iff]
  obtain ⟨J, _, _, _, _, hf⟩ := hf
  let _ : PreservesWellOrderContinuousOfShape J F :=
    { preservesColimitsOfShape := fun _ _ ↦ inferInstance }
  exact ⟨J, inferInstance, inferInstance, inferInstance, inferInstance,
    transfiniteCompositionsOfShape_map_of_preserves (J := J) (P := Q) F f
      (transfiniteCompositionsOfShape_monotone J hPQ _ hf)⟩

/-- A fully faithful colimit-preserving functor transports the left class
generated by a small-object family when it identifies the right classes. -/
theorem rlp_llp_eq_inverseImage_of_fullyFaithful
    (F : C ⥤ D) [F.Full] [F.Faithful]
    (P : MorphismProperty C) (Q : MorphismProperty D)
    [P.HasSmallObjectArgument.{w}]
    [PreservesColimitsOfSize.{w, w} F]
    (hPQ : P ≤ Q.inverseImage F)
    (hrlp : P.rlp = Q.rlp.inverseImage F) :
    P.rlp.llp = Q.rlp.llp.inverseImage F := by
  apply le_antisymm
  · intro X Y f hf
    rw [P.llp_rlp_of_hasSmallObjectArgument] at hf
    obtain ⟨Z, W, g, hfg, hg⟩ := hf
    apply Q.retracts_transfiniteComposition_pushouts_coproducts_le_llp_rlp
    refine ⟨F.obj Z, F.obj W, F.map g, hfg.map F, ?_⟩
    apply transfiniteCompositions_le_inverseImage_map F
      (coproducts.{w} P).pushouts (coproducts.{w} Q).pushouts
    · exact pushouts_le_inverseImage_map F
        (coproducts.{w} P) (coproducts.{w} Q)
        (coproducts_le_inverseImage_map F P Q hPQ)
    · exact hg
  · intro X Y f hf A B p hp
    rw [hrlp] at hp
    exact (Functor.hasLiftingProperty_map_iff_of_full_faithful F f p).mp
      (hf (F.map p) hp)

end MorphismProperty

end CategoryTheory
