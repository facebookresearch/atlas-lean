/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShell
public import MathlibExt.KTheory.Exact.Quillen.SpanUnderlyingIsoNaturality
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Quillen simplices extracted from edgewise Stage shells

An edgewise finite Stage determines a composable chain in the Quillen
Q-construction: vertices are the literal cross cells and arbitrary interval
maps are the canonically endpoint-normalized shell classes.  Pointwise weak
isomorphisms of exact stages induce natural transformations of these chains.

This file constructs no outer reindexing, lift category, contractibility,
all-degree Q/S comparison, nerve, realization, or additivity theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C]
  [ExactCategory C]

local instance spanFlagStageShellFunctorWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- The left edgewise index is bounded by the right edgewise index at every
vertex. -/
theorem edgewiseStageVertex_le (a : SimplexCategory)
    (k : Fin (a.len + 1)) :
    edgewiseLeftIndex a k ≤ edgewiseRightIndex a k := by
  have h := (edgewiseShell a k k le_rfl).toOrderHom.monotone
    (show (1 : Fin 4) ≤ 2 by decide)
  simpa only [edgewiseShell_one, edgewiseShell_two] using h

/-- Literal cross vertex of an edgewise Stage. -/
noncomputable def edgewiseStageVertex {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) : C :=
  A.obj.obj (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
    (edgewiseStageVertex_le a k))

/-- The raw shell source is the cross vertex at its left endpoint. -/
theorem edgewiseStageShellSourceEqVertex {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket A k l hkl).source =
      edgewiseStageVertex A k := by
  apply congrArg A.obj.obj
  change (indexFunctor (edgewiseShell a k l hkl)).obj
      (interval (1 : Fin 4) 2 (by decide)) =
    interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k) _
  rw [indexFunctor_obj_interval]
  simp only [edgewiseShell_one, edgewiseShell_two]

/-- The raw shell target is the cross vertex at its right endpoint. -/
theorem edgewiseStageShellTargetEqVertex {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket A k l hkl).target =
      edgewiseStageVertex A l := by
  apply congrArg A.obj.obj
  change (indexFunctor (edgewiseShell a k l hkl)).obj
      (interval (0 : Fin 4) 3 (by decide)) =
    interval (edgewiseLeftIndex a l) (edgewiseRightIndex a l) _
  rw [indexFunctor_obj_interval]
  simp only [edgewiseShell_zero, edgewiseShell_three]

/-- Shell class with both endpoints transported to the fixed cross vertices. -/
noncomputable def edgewiseStageShellClassNormalized {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (⟨edgewiseStageVertex A k⟩ : QuillenQ C) ⟶
      ⟨edgewiseStageVertex A l⟩ :=
  (QuillenQ.underlyingIso
    (eqToIso (edgewiseStageShellSourceEqVertex A k l hkl))).inv ≫
    (edgewiseStageShellPacket A k l hkl).quillenHom ≫
    (QuillenQ.underlyingIso
      (eqToIso (edgewiseStageShellTargetEqVertex A k l hkl))).hom

private theorem underlyingIso_inv_eq_hom_symm {X Y : C} (e : X ≅ Y) :
    (QuillenQ.underlyingIso e).inv =
      (QuillenQ.underlyingIso e.symm).hom := by
  apply (cancel_mono (QuillenQ.underlyingIso e).hom).1
  rw [Iso.inv_hom_id]
  have h := congrArg Iso.hom
    (QuillenQ.underlyingIso_trans e.symm e)
  rw [show e.symm.trans e = Iso.refl Y by ext; simp,
    QuillenQ.underlyingIso_refl] at h
  exact h

/-- A repeated normalized shell is the identity. -/
@[simp]
theorem edgewiseStageShellClassNormalized_refl {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k : Fin (a.len + 1)) :
    edgewiseStageShellClassNormalized A k k le_rfl = 𝟙 _ := by
  rw [edgewiseStageShellClassNormalized,
    edgewiseStageShellClass_eq_underlyingIso_hom]
  rw [underlyingIso_inv_eq_hom_symm,
    ← Iso.trans_hom, ← Iso.trans_hom,
    ← QuillenQ.underlyingIso_trans,
    ← QuillenQ.underlyingIso_trans]
  have hIso :
      (eqToIso (edgewiseStageShellSourceEqVertex A k k le_rfl)).symm.trans
        ((eqToIso (edgewiseStageShellSourceEqTarget A k)).trans
          (eqToIso (edgewiseStageShellTargetEqVertex A k k le_rfl))) =
        Iso.refl (edgewiseStageVertex A k) := by
    apply Iso.ext
    simp
  rw [hIso, QuillenQ.underlyingIso_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Normalized shell classes compose on every ordered triple of vertices. -/
theorem edgewiseStageShellClassNormalized_comp {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    edgewiseStageShellClassNormalized A k l hkl ≫
        edgewiseStageShellClassNormalized A l r hlr =
      edgewiseStageShellClassNormalized A k r (hkl.trans hlr) := by
  have hMid :
      QuillenQ.underlyingIso
          (eqToIso (edgewiseStageShellTargetEqVertex A k l hkl)) =
        QuillenQ.underlyingIso
          (eqToIso (edgewiseStageShellSourceEqVertex A l r hlr)) := by
    congr 2
  rw [edgewiseStageShellClassNormalized,
    edgewiseStageShellClassNormalized,
    edgewiseStageShellClassNormalized, hMid]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
      (edgewiseStageShellPacket A k l hkl).quillenHom
      (edgewiseStageShellPacket A l r hlr).quillenHom,
    edgewiseStageShellClass_comp]

/-- The Quillen simplex extracted from all normalized shells of one edgewise
Stage. -/
noncomputable def edgewiseStageQuillenSimplex {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) :
    ComposableArrows (QuillenQ C) a.len where
  obj k := ⟨edgewiseStageVertex A k⟩
  map f := edgewiseStageShellClassNormalized A _ _ (leOfHom f)
  map_id k := edgewiseStageShellClassNormalized_refl A k
  map_comp f g :=
    (edgewiseStageShellClassNormalized_comp A
      (leOfHom f) (leOfHom g)).symm

@[simp]
theorem edgewiseStageQuillenSimplex_obj {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageQuillenSimplex A).obj k =
      ⟨edgewiseStageVertex A k⟩ :=
  rfl

/-- Arbitrary-interval map formula for the extracted Quillen simplex. -/
@[simp]
theorem edgewiseStageQuillenSimplex_map_homOfLE {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    (edgewiseStageQuillenSimplex A).map (homOfLE hkl) =
      edgewiseStageShellClassNormalized A k l hkl := by
  rfl

/-- Pointwise vertex isomorphism induced by a weak Stage morphism. -/
noncomputable def edgewiseStageVertexIso {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) (k : Fin (a.len + 1)) :
    edgewiseStageVertex A.obj k ≅ edgewiseStageVertex B.obj k := by
  have hf : IsIso (f.hom.hom.app
      (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
        (edgewiseStageVertex_le a k))) := by
    have hfW := f.property
    rw [mem_stageWeak] at hfW
    exact hfW _
  exact @asIso C _ _ _ _ hf

@[simp]
theorem edgewiseStageVertexIso_hom {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageVertexIso f k).hom =
      f.hom.hom.app
        (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
          (edgewiseStageVertex_le a k)) :=
  rfl

private noncomputable def edgewiseStageShellApexIso {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellPacket A.obj k l hkl).span.apex ≅
      (edgewiseStageShellPacket B.obj k l hkl).span.apex := by
  let I := interval (edgewiseLeftIndex a l) (edgewiseRightIndex a k)
    ((edgewiseLeftIndex_anti hkl).trans
      (edgewiseStageVertex_le a k))
  have hf : IsIso (f.hom.hom.app I) := by
    have hfW := f.property
    rw [mem_stageWeak] at hfW
    exact hfW I
  exact @asIso C _ _ _ _ hf

set_option linter.flexible false in
/-- Naturality of normalized shell classes under a pointwise weak Stage
morphism. -/
theorem edgewiseStageShellClassNormalized_naturality
    {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseStageShellClassNormalized A.obj k l hkl ≫
        (QuillenQ.underlyingIso (edgewiseStageVertexIso f l)).hom =
      (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom ≫
        edgewiseStageShellClassNormalized B.obj k l hkl := by
  let S := (edgewiseStageShellPacket A.obj k l hkl).span
  let T := (edgewiseStageShellPacket B.obj k l hkl).span
  let eX : (edgewiseStageShellPacket A.obj k l hkl).source ≅
      (edgewiseStageShellPacket B.obj k l hkl).source := by
    let I := interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
      (edgewiseStageVertex_le a k)
    have hf : IsIso (f.hom.hom.app I) := by
      have hfW := f.property
      rw [mem_stageWeak] at hfW
      exact hfW I
    exact @asIso C _ _ _ _ hf
  let eY : (edgewiseStageShellPacket A.obj k l hkl).target ≅
      (edgewiseStageShellPacket B.obj k l hkl).target := by
    let I := interval (edgewiseLeftIndex a l) (edgewiseRightIndex a l)
      (edgewiseStageVertex_le a l)
    have hf : IsIso (f.hom.hom.app I) := by
      have hfW := f.property
      rw [mem_stageWeak] at hfW
      exact hfW I
    exact @asIso C _ _ _ _ hf
  let eP := edgewiseStageShellApexIso f k l hkl
  have hRaw := QuillenQ.mkHom_naturality_of_span_iso S T eX eY eP
    (by
      exact (f.hom.hom.naturality _).symm)
    (by
      exact (f.hom.hom.naturality _).symm)
  let pXA := eqToIso (edgewiseStageShellSourceEqVertex A.obj k l hkl)
  let pXB := eqToIso (edgewiseStageShellSourceEqVertex B.obj k l hkl)
  let pYA := eqToIso (edgewiseStageShellTargetEqVertex A.obj k l hkl)
  let pYB := eqToIso (edgewiseStageShellTargetEqVertex B.obj k l hkl)
  have hSourceIso :
      (edgewiseStageVertexIso f k).trans pXB.symm =
        pXA.symm.trans eX := by
    apply Iso.ext
    simp [pXA, pXB, eX, edgewiseStageVertexIso]
    let z : ∀ h : edgewiseLeftIndex a k ≤ edgewiseRightIndex a k,
        A.obj.obj.obj (interval (edgewiseLeftIndex a k)
          (edgewiseRightIndex a k) h) ⟶
        B.obj.obj.obj (interval (edgewiseLeftIndex a k)
          (edgewiseRightIndex a k) h) :=
      fun h ↦ f.hom.hom.app (interval (edgewiseLeftIndex a k)
        (edgewiseRightIndex a k) h)
    exact eqToHom_naturality z (Subsingleton.elim _ _)
  have hTargetIso :
      pYA.trans (edgewiseStageVertexIso f l) =
        eY.trans pYB := by
    apply Iso.ext
    simp [pYA, pYB, eY, edgewiseStageVertexIso]
    let z : ∀ h : edgewiseLeftIndex a l ≤ edgewiseRightIndex a l,
        A.obj.obj.obj (interval (edgewiseLeftIndex a l)
          (edgewiseRightIndex a l) h) ⟶
        B.obj.obj.obj (interval (edgewiseLeftIndex a l)
          (edgewiseRightIndex a l) h) :=
      fun h ↦ f.hom.hom.app (interval (edgewiseLeftIndex a l)
        (edgewiseRightIndex a l) h)
    exact (eqToHom_naturality z (Subsingleton.elim _ _)).symm
  have hSource :
      (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom ≫
          (QuillenQ.underlyingIso pXB).inv =
        (QuillenQ.underlyingIso pXA).inv ≫
          (QuillenQ.underlyingIso eX).hom := by
    rw [underlyingIso_inv_eq_hom_symm,
      underlyingIso_inv_eq_hom_symm]
    calc
      _ = (QuillenQ.underlyingIso
          ((edgewiseStageVertexIso f k).trans pXB.symm)).hom :=
        (congrArg Iso.hom (QuillenQ.underlyingIso_trans
          (edgewiseStageVertexIso f k) pXB.symm)).symm
      _ = (QuillenQ.underlyingIso (pXA.symm.trans eX)).hom := by
        rw [hSourceIso]
      _ = _ := congrArg Iso.hom
        (QuillenQ.underlyingIso_trans pXA.symm eX)
  have hTarget :
      (QuillenQ.underlyingIso pYA).hom ≫
          (QuillenQ.underlyingIso (edgewiseStageVertexIso f l)).hom =
        (QuillenQ.underlyingIso eY).hom ≫
          (QuillenQ.underlyingIso pYB).hom := by
    calc
      _ = (QuillenQ.underlyingIso
          (pYA.trans (edgewiseStageVertexIso f l))).hom :=
        (congrArg Iso.hom (QuillenQ.underlyingIso_trans pYA
          (edgewiseStageVertexIso f l))).symm
      _ = (QuillenQ.underlyingIso (eY.trans pYB)).hom := by
        rw [hTargetIso]
      _ = _ := congrArg Iso.hom
        (QuillenQ.underlyingIso_trans eY pYB)
  unfold edgewiseStageShellClassNormalized QuillenStageShellData.quillenHom
  simp only [Category.assoc]
  change (QuillenQ.underlyingIso pXA).inv ≫
      QuillenQ.mkHom S ≫
        (QuillenQ.underlyingIso pYA).hom ≫
          (QuillenQ.underlyingIso (edgewiseStageVertexIso f l)).hom =
    (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom ≫
      (QuillenQ.underlyingIso pXB).inv ≫
        QuillenQ.mkHom T ≫ (QuillenQ.underlyingIso pYB).hom
  rw [hTarget]
  rw [← Category.assoc (QuillenQ.mkHom S)
      (QuillenQ.underlyingIso eY).hom,
    hRaw]
  rw [← Category.assoc
      (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom
      (QuillenQ.underlyingIso pXB).inv,
    hSource]
  simp only [Category.assoc]

/-- Natural transformation between extracted Quillen simplices induced by a
weak Stage morphism. -/
noncomputable def edgewiseStageQuillenSimplexMap {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) :
    edgewiseStageQuillenSimplex A.obj ⟶
      edgewiseStageQuillenSimplex B.obj where
  app k := (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom
  naturality {k l} h :=
    edgewiseStageShellClassNormalized_naturality f k l (leOfHom h)

@[simp]
theorem edgewiseStageQuillenSimplexMap_app {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) (k : Fin (a.len + 1)) :
    (edgewiseStageQuillenSimplexMap f).app k =
      (QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom :=
  rfl

/-- Functor from weak edgewise Stages to their extracted Quillen simplices. -/
noncomputable def edgewiseStageQuillenSimplexFunctor
    (C : Type u) [Category.{v} C] [Preadditive C]
    [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C (edgewiseQ.obj a).len) ⥤
      ComposableArrows (QuillenQ C) a.len := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  exact
    { obj := fun A ↦ edgewiseStageQuillenSimplex A.obj
      map := fun f ↦ edgewiseStageQuillenSimplexMap f
      map_id := fun A ↦ by
        apply NatTrans.ext
        funext k
        have hk : edgewiseStageVertexIso (𝟙 A) k =
            Iso.refl (edgewiseStageVertex A.obj k) := by
          apply Iso.ext
          rfl
        rw [edgewiseStageQuillenSimplexMap_app, hk,
          QuillenQ.underlyingIso_refl]
        rfl
      map_comp := fun f g ↦ by
        apply NatTrans.ext
        funext k
        have hk : edgewiseStageVertexIso (f ≫ g) k =
            (edgewiseStageVertexIso f k).trans
              (edgewiseStageVertexIso g k) := by
          apply Iso.ext
          rfl
        rw [edgewiseStageQuillenSimplexMap_app, hk,
          QuillenQ.underlyingIso_trans]
        rfl }

@[simp]
theorem edgewiseStageQuillenSimplexFunctor_obj
    (C : Type u) [Category.{v} C] [Preadditive C]
    [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory)
    (A : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C (edgewiseQ.obj a).len)) :
    (edgewiseStageQuillenSimplexFunctor C a).obj A =
      edgewiseStageQuillenSimplex A.obj :=
  rfl

@[simp]
theorem edgewiseStageQuillenSimplexFunctor_map
    (C : Type u) [Category.{v} C] [Preadditive C]
    [Limits.HasZeroObject C] [Limits.HasBinaryBiproducts C]
    [ExactCategory C] (a : SimplexCategory)
    {A B : (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      StageWeakCategory C (edgewiseQ.obj a).len)} (f : A ⟶ B) :
    (edgewiseStageQuillenSimplexFunctor C a).map f =
      edgewiseStageQuillenSimplexMap f :=
  rfl

end AlgebraicKTheory

end
