/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctor

/-!
# Strict outer reindexing for Stage-shell Quillen simplices

The Quillen simplex extracted from an edgewise weak Stage commutes strictly
with every outer simplex reindexing.  This file names the Stage-side and
Quillen-chain-side reindex functors and records their strict identity and
composition laws.

No lift category, representative choice, contractibility, nerve,
realization, or Q/S comparison is constructed here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The canonical Waldhausen structure used by the original span-flag Stage reindexing functor. -/
local instance spanFlagStageShellFunctorReindexWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- Stage-side contravariant reindexing along an edgewise simplex map. -/
def edgewiseStageWeakReindex {a b : SimplexCategory} (α : a ⟶ b) :
    StageWeakCategory C (edgewiseQ.obj b).len ⥤
      StageWeakCategory C (edgewiseQ.obj a).len :=
  reindexStageWeak C (edgewiseQ.map α)

/-- Quillen-chain-side reindexing by precomposition with a simplex map. -/
def edgewiseQuillenSimplexReindex {a b : SimplexCategory} (α : a ⟶ b) :
    ComposableArrows (QuillenQ C) b.len ⥤
      ComposableArrows (QuillenQ C) a.len :=
  ComposableArrows.whiskerLeftFunctor
    (SimplexCategory.toCat.map α).toFunctor

private theorem underlyingIso_eqToIso_hom {X Y : C} (h : X = Y) :
    (QuillenQ.underlyingIso (eqToIso h)).hom =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) h) := by
  cases h
  change (QuillenQ.underlyingIso (Iso.refl X)).hom = 𝟙 _
  rw [QuillenQ.underlyingIso_refl]
  rfl

private theorem underlyingIso_eqToIso_inv {X Y : C} (h : X = Y) :
    (QuillenQ.underlyingIso (eqToIso h)).inv =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) h).symm := by
  cases h
  change (QuillenQ.underlyingIso (Iso.refl X)).inv = 𝟙 _
  rw [QuillenQ.underlyingIso_refl]
  rfl

private theorem underlyingIso_eqToIso_symm_hom {X Y : C} (h : X = Y) :
    (QuillenQ.underlyingIso (eqToIso h).symm).hom =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) h).symm := by
  cases h
  change (QuillenQ.underlyingIso (Iso.refl X)).hom = 𝟙 _
  rw [QuillenQ.underlyingIso_refl]
  rfl

/-- Reindexing carries a cross vertex strictly to the cross vertex at the
image index. -/
theorem edgewiseStageVertex_reindex {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C (edgewiseQ.obj b).len) (k : Fin (a.len + 1)) :
    edgewiseStageVertex
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) k =
      edgewiseStageVertex A (α.toOrderHom k) := by
  unfold edgewiseStageVertex
  change A.obj.obj ((indexFunctor (edgewiseQ.map α)).obj
      (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k) _)) = _
  apply congrArg A.obj.obj
  rw [indexFunctor_obj_interval]
  refine Arrow.ext (edgewiseQ_map_leftIndex α k)
    (edgewiseQ_map_rightIndex α k) ?_
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Normalized shell classes commute with outer edgewise reindexing, with
the canonical endpoint equality transports displayed explicitly. -/
theorem edgewiseStageShellClassNormalized_reindex
    {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C (edgewiseQ.obj b).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) k l hkl =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
          (edgewiseStageVertex_reindex α A k)) ≫
        edgewiseStageShellClassNormalized A
          (α.toOrderHom k) (α.toOrderHom l)
          (α.toOrderHom.monotone hkl) ≫
        eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
          (edgewiseStageVertex_reindex α A l)).symm := by
  let D₁ := edgewiseStageShellPacket
    ((reindexStage (C := C) (edgewiseQ.map α)).obj A) k l hkl
  let D₂ := edgewiseStageShellPacket A
    (α.toOrderHom k) (α.toOrderHom l) (α.toOrderHom.monotone hkl)
  have hPacket : D₁ = D₂ :=
    edgewiseStageShellPacket_reindex (C := C) α A k l hkl
  let s₁ : D₁.source =
      edgewiseStageVertex
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) k :=
    edgewiseStageShellSourceEqVertex _ k l hkl
  let s₂ : D₂.source = edgewiseStageVertex A (α.toOrderHom k) :=
    edgewiseStageShellSourceEqVertex _ _ _ _
  let t₁ : D₁.target =
      edgewiseStageVertex
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) l :=
    edgewiseStageShellTargetEqVertex _ k l hkl
  let t₂ : D₂.target = edgewiseStageVertex A (α.toOrderHom l) :=
    edgewiseStageShellTargetEqVertex _ _ _ _
  let vK := edgewiseStageVertex_reindex α A k
  let vL := edgewiseStageVertex_reindex α A l
  let pS : D₁.source = D₂.source :=
    congrArg QuillenStageShellData.source hPacket
  let pT : D₁.target = D₂.target :=
    congrArg QuillenStageShellData.target hPacket
  let z : ∀ D : QuillenStageShellData C,
      (⟨D.source⟩ : QuillenQ C) ⟶ ⟨D.target⟩ :=
    fun D ↦ D.quillenHom
  have hNat := eqToHom_naturality z hPacket
  have hRaw : D₁.quillenHom =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) pS) ≫
        D₂.quillenHom ≫
        eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) pT).symm := by
    apply (cancel_mono (eqToHom (congrArg
      (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) pT))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]
    simpa only [z] using hNat
  let preL :=
    eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) s₁).symm ≫
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) pS)
  let preR :=
    eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) vK) ≫
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) s₂).symm
  have hPre : preL = preR := by
    dsimp [preL, preR]
    simp only [Category.id_comp, Category.comp_id]
  let sufL :=
    eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) pT).symm ≫
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) t₁)
  let sufR :=
    eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) t₂) ≫
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) vL).symm
  have hSuf : sufL = sufR := by
    dsimp [sufL, sufR]
    simp only [Category.id_comp, Category.comp_id]
  unfold edgewiseStageShellClassNormalized
  change (QuillenQ.underlyingIso (eqToIso s₁)).inv ≫
      D₁.quillenHom ≫ (QuillenQ.underlyingIso (eqToIso t₁)).hom =
    eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) vK) ≫
      ((QuillenQ.underlyingIso (eqToIso s₂)).inv ≫
        D₂.quillenHom ≫ (QuillenQ.underlyingIso (eqToIso t₂)).hom) ≫
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C)) vL).symm
  simp only [underlyingIso_eqToIso_inv, underlyingIso_eqToIso_hom]
  rw [hRaw]
  have h := congrArg₂ (fun pre suf ↦ pre ≫ D₂.quillenHom ≫ suf)
    hPre hSuf
  simpa only [preL, preR, sufL, sufR, Category.assoc] using h

/-- Objectwise strict reindexing of the Quillen simplex extracted from a
Stage. -/
theorem edgewiseStageQuillenSimplex_reindex
    {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C (edgewiseQ.obj b).len) :
    edgewiseStageQuillenSimplex
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) =
      (edgewiseQuillenSimplexReindex (C := C) α).obj
        (edgewiseStageQuillenSimplex A) := by
  let hObj : ∀ k : Fin (a.len + 1),
      (edgewiseStageQuillenSimplex
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A)).obj k =
      ((edgewiseQuillenSimplexReindex (C := C) α).obj
        (edgewiseStageQuillenSimplex A)).obj k :=
    fun k ↦ congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
      (edgewiseStageVertex_reindex α A k)
  refine ComposableArrows.ext hObj ?_
  intro i hi
  let k : Fin (a.len + 1) := ⟨i, by omega⟩
  let l : Fin (a.len + 1) := ⟨i + 1, by omega⟩
  have hkl : k ≤ l := by
    rw [Fin.le_iff_val_le_val]
    simp [k, l]
  change edgewiseStageShellClassNormalized
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) k l _ =
      eqToHom (hObj k) ≫
        edgewiseStageShellClassNormalized A
          (α.toOrderHom k) (α.toOrderHom l) _ ≫
        eqToHom (hObj l).symm
  exact edgewiseStageShellClassNormalized_reindex α A k l hkl

private theorem edgewiseStageVertexIso_reindex_hom
    {a b : SimplexCategory} (α : a ⟶ b)
    {A B : StageWeakCategory C (edgewiseQ.obj b).len}
    (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageVertexIso
      ((edgewiseStageWeakReindex (C := C) α).map f) k).hom =
      eqToHom (edgewiseStageVertex_reindex α A.obj k) ≫
        (edgewiseStageVertexIso f (α.toOrderHom k)).hom ≫
        eqToHom (edgewiseStageVertex_reindex α B.obj k).symm := by
  let I := interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
    (edgewiseStageVertex_le a k)
  let J := interval
    (edgewiseLeftIndex b (α.toOrderHom k))
    (edgewiseRightIndex b (α.toOrderHom k))
    (edgewiseStageVertex_le b (α.toOrderHom k))
  have hIJ : (indexFunctor (edgewiseQ.map α)).obj I = J := by
    change (indexFunctor (edgewiseQ.map α)).obj
        (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k) _) =
      interval (edgewiseLeftIndex b (α.toOrderHom k))
        (edgewiseRightIndex b (α.toOrderHom k)) _
    calc
      _ = interval
          ((edgewiseQ.map α).toOrderHom (edgewiseLeftIndex a k))
          ((edgewiseQ.map α).toOrderHom (edgewiseRightIndex a k)) _ :=
        indexFunctor_obj_interval (edgewiseQ.map α)
          (edgewiseStageVertex_le a k)
      _ = _ := by
        refine Arrow.ext (edgewiseQ_map_leftIndex α k)
          (edgewiseQ_map_rightIndex α k) ?_
        exact Subsingleton.elim _ _
  change f.hom.hom.app ((indexFunctor (edgewiseQ.map α)).obj I) =
    eqToHom (congrArg A.obj.obj.obj hIJ) ≫
      f.hom.hom.app J ≫ eqToHom (congrArg B.obj.obj.obj hIJ).symm
  have h := f.hom.hom.congr hIJ
  rw [eqToHom_map, eqToHom_map] at h
  exact h

private theorem edgewiseUnderlyingVertexIso_reindex
    {a b : SimplexCategory} (α : a ⟶ b)
    {A B : StageWeakCategory C (edgewiseQ.obj b).len}
    (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (QuillenQ.underlyingIso
      (edgewiseStageVertexIso
        ((edgewiseStageWeakReindex (C := C) α).map f) k)).hom =
      eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
          (edgewiseStageVertex_reindex α A.obj k)) ≫
        (QuillenQ.underlyingIso
          (edgewiseStageVertexIso f (α.toOrderHom k))).hom ≫
        eqToHom (congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
          (edgewiseStageVertex_reindex α B.obj k)).symm := by
  let hA : edgewiseStageVertex
      ((edgewiseStageWeakReindex (C := C) α).obj A).obj k =
        edgewiseStageVertex A.obj (α.toOrderHom k) :=
    edgewiseStageVertex_reindex α A.obj k
  let hB : edgewiseStageVertex
      ((edgewiseStageWeakReindex (C := C) α).obj B).obj k =
        edgewiseStageVertex B.obj (α.toOrderHom k) :=
    edgewiseStageVertex_reindex α B.obj k
  have hIso :
      edgewiseStageVertexIso
          ((edgewiseStageWeakReindex (C := C) α).map f) k =
        (eqToIso hA).trans
          ((edgewiseStageVertexIso f (α.toOrderHom k)).trans
            (eqToIso hB).symm) := by
    apply Iso.ext
    exact edgewiseStageVertexIso_reindex_hom α f k
  rw [hIso]
  calc
    _ = (QuillenQ.underlyingIso (eqToIso hA)).hom ≫
          (QuillenQ.underlyingIso
            ((edgewiseStageVertexIso f (α.toOrderHom k)).trans
              (eqToIso hB).symm)).hom :=
      congrArg Iso.hom (QuillenQ.underlyingIso_trans
        (eqToIso hA)
        ((edgewiseStageVertexIso f (α.toOrderHom k)).trans
          (eqToIso hB).symm))
    _ = (QuillenQ.underlyingIso (eqToIso hA)).hom ≫
          (QuillenQ.underlyingIso
            (edgewiseStageVertexIso f (α.toOrderHom k))).hom ≫
          (QuillenQ.underlyingIso (eqToIso hB).symm).hom := by
      have ht :
          (QuillenQ.underlyingIso
            ((edgewiseStageVertexIso f (α.toOrderHom k)).trans
              (eqToIso hB).symm)).hom =
            (QuillenQ.underlyingIso
              (edgewiseStageVertexIso f (α.toOrderHom k))).hom ≫
              (QuillenQ.underlyingIso (eqToIso hB).symm).hom :=
        congrArg Iso.hom (QuillenQ.underlyingIso_trans
          (edgewiseStageVertexIso f (α.toOrderHom k))
          (eqToIso hB).symm)
      exact congrArg
        (fun g ↦ (QuillenQ.underlyingIso (eqToIso hA)).hom ≫ g) ht
    _ = _ := by
      rw [underlyingIso_eqToIso_hom,
        underlyingIso_eqToIso_symm_hom]
      congr

/-- Extracting a Quillen simplex commutes strictly with outer reindexing on
both objects and weak Stage morphisms. -/
theorem edgewiseStageQuillenSimplexFunctor_reindex
    {a b : SimplexCategory} (α : a ⟶ b) :
    edgewiseStageWeakReindex (C := C) α ⋙
        edgewiseStageQuillenSimplexFunctor C a =
      edgewiseStageQuillenSimplexFunctor C b ⋙
        edgewiseQuillenSimplexReindex (C := C) α := by
  let hObj : ∀ A : StageWeakCategory C (edgewiseQ.obj b).len,
      (edgewiseStageWeakReindex (C := C) α ⋙
        edgewiseStageQuillenSimplexFunctor C a).obj A =
      (edgewiseStageQuillenSimplexFunctor C b ⋙
        edgewiseQuillenSimplexReindex (C := C) α).obj A :=
    fun A ↦ edgewiseStageQuillenSimplex_reindex α A.obj
  refine CategoryTheory.Functor.ext hObj ?_
  intro A B f
  apply NatTrans.ext
  funext k
  simp only [Functor.comp_map, edgewiseStageQuillenSimplexFunctor_map,
    edgewiseStageQuillenSimplexMap_app, eqToHom_app,
    NatTrans.comp_app]
  change (QuillenQ.underlyingIso
      (edgewiseStageVertexIso
        ((edgewiseStageWeakReindex (C := C) α).map f) k)).hom =
    eqToHom (Functor.congr_obj (hObj A) k) ≫
      (QuillenQ.underlyingIso
        (edgewiseStageVertexIso f (α.toOrderHom k))).hom ≫
      eqToHom (Functor.congr_obj (hObj B) k).symm
  have hA : Functor.congr_obj (hObj A) k =
      congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
        (edgewiseStageVertex_reindex α A.obj k) :=
    Subsingleton.elim _ _
  have hB : Functor.congr_obj (hObj B) k =
      congrArg (fun Z : C ↦ (⟨Z⟩ : QuillenQ C))
        (edgewiseStageVertex_reindex α B.obj k) :=
    Subsingleton.elim _ _
  rw [hA, hB]
  exact edgewiseUnderlyingVertexIso_reindex α f k

/-- Quillen-simplex reindexing along the identity is strictly the identity
functor. -/
@[simp]
theorem edgewiseQuillenSimplexReindex_id (a : SimplexCategory) :
    edgewiseQuillenSimplexReindex (C := C) (𝟙 a) =
      𝟭 (ComposableArrows (QuillenQ C) a.len) := by
  rfl

/-- Quillen-simplex reindexing is strictly contravariant under composition. -/
@[simp]
theorem edgewiseQuillenSimplexReindex_comp
    {a b c : SimplexCategory} (α : a ⟶ b) (β : b ⟶ c) :
    edgewiseQuillenSimplexReindex (C := C) (α ≫ β) =
      edgewiseQuillenSimplexReindex (C := C) β ⋙
        edgewiseQuillenSimplexReindex (C := C) α := by
  rfl

end AlgebraicKTheory

end
