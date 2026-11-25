/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CategoryTheory_Pseudofunctor_DescentData_exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj.lean`
and
`P2M/Sol/S_CategoryTheory_Pseudofunctor_DescentData_exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

universe t v' u' v u

open CategoryTheory CategoryTheory.Limits Opposite


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false


namespace CategoryTheory
namespace Pseudofunctor
namespace DescentData
namespace LocalEffectivity

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) {S X : C} (f : X ⟶ S)

noncomputable def restr {Z : C} (z : Z ⟶ S) :
    F.DescentData (fun _ : Unit => f) ⥤ F.DescentData (fun _ : Unit => pullback.snd f z) :=
  pullFunctor F (f := fun _ : Unit => f) (p := z) (f' := fun _ : Unit => pullback.snd f z)
      (α := fun j => j)
    (p' := fun _ => pullback.fst f z) (fun _ => pullback.condition)

noncomputable def toDescentDataRestrIso {Z : C} (z : Z ⟶ S) :
    F.toDescentData (fun _ : Unit => f) ⋙ restr F f z ≅
      (F.map z.op.toLoc).toFunctor ⋙ F.toDescentData (fun _ : Unit => pullback.snd f z) :=
  toDescentDataCompPullFunctorIso F (f := fun _ : Unit => f) (p := z) (f' := fun _ : Unit =>
      pullback.snd f z)
    (α := fun j => j) (p' := fun _ => pullback.fst f z) (fun _ => pullback.condition)

noncomputable def restrMap {Z Z' : C} (z : Z ⟶ S) (z' : Z' ⟶ S) (g : Z' ⟶ Z) (hg : g ≫ z = z') :
    pullback f z' ⟶ pullback f z :=
  pullback.lift (pullback.fst f z') (pullback.snd f z' ≫ g)
    (by rw [pullback.condition, ← hg, Category.assoc])

@[reassoc (attr := simp)]
lemma restrMap_fst {Z Z' : C} (z : Z ⟶ S) (z' : Z' ⟶ S) (g : Z' ⟶ Z) (hg : g ≫ z = z') :
    restrMap f z z' g hg ≫ pullback.fst f z = pullback.fst f z' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma restrMap_snd {Z Z' : C} (z : Z ⟶ S) (z' : Z' ⟶ S) (g : Z' ⟶ Z) (hg : g ≫ z = z') :
    restrMap f z z' g hg ≫ pullback.snd f z = pullback.snd f z' ≫ g :=
  pullback.lift_snd _ _ _

noncomputable def restrAlong {Z Z' : C} (z : Z ⟶ S) (z' : Z' ⟶ S) (g : Z' ⟶ Z) (hg : g ≫ z = z') :
    F.DescentData (fun _ : Unit => pullback.snd f z) ⥤ F.DescentData (fun _ : Unit => pullback.snd
        f z') :=
  pullFunctor F (f := fun _ : Unit => pullback.snd f z) (p := g) (f' := fun _ : Unit =>
      pullback.snd f z')
    (α := fun j => j) (p' := fun _ => restrMap f z z' g hg) (fun _ => restrMap_snd f z z' g hg)

noncomputable def toDescentDataRestrAlongIso {Z Z' : C} (z : Z ⟶ S) (z' : Z' ⟶ S) (g : Z' ⟶ Z)
    (hg : g ≫ z = z') :
    F.toDescentData (fun _ : Unit => pullback.snd f z) ⋙ restrAlong F f z z' g hg ≅
      (F.map g.op.toLoc).toFunctor ⋙ F.toDescentData (fun _ : Unit => pullback.snd f z') :=
  toDescentDataCompPullFunctorIso F (f := fun _ : Unit => pullback.snd f z) (p := g)
    (f' := fun _ : Unit => pullback.snd f z') (α := fun j => j) (p' := fun _ => restrMap f z z' g
        hg)
    (fun _ => restrMap_snd f z z' g hg)

noncomputable def restrCompIso {Z Z' : C} (z : Z ⟶ S) (z' : Z' ⟶ S) (g : Z' ⟶ Z) (hg : g ≫ z = z') :
    restr F f z ⋙ restrAlong F f z z' g hg ≅ restr F f z' :=
  pullFunctorCompIso F (f := fun _ : Unit => f) (p := z) (f' := fun _ : Unit => pullback.snd f z)
    (α := fun j => j) (p' := fun _ => pullback.fst f z) (fun _ => pullback.condition)
    (q := g) (f'' := fun _ : Unit => pullback.snd f z') (β := fun j => j) (q' := fun _ => restrMap
        f z z' g hg)
    (fun _ => restrMap_snd f z z' g hg) z' (r' := fun _ => pullback.fst f z') hg
    (fun _ => restrMap_fst f z z' g hg)

lemma op_toLoc_comp {X₁ X₂ X₃ : C} (a : X₂ ⟶ X₃) (b : X₁ ⟶ X₂) {ab : X₁ ⟶ X₃} (h : b ≫ a = ab) :
    a.op.toLoc ≫ b.op.toLoc = ab.op.toLoc := by
  subst h; rfl

lemma map_map_eq {b₀ b₁ b₂ : LocallyDiscrete Cᵒᵖ} (a₁ : b₀ ⟶ b₁) (a₂ : b₁ ⟶ b₂) (a₁₂ : b₀ ⟶ b₂)
    (h : a₁ ≫ a₂ = a₁₂) {M N : F.obj b₀} (x : M ⟶ N) :
    (F.map a₂).toFunctor.map ((F.map a₁).toFunctor.map x) =
      (F.mapComp' a₁ a₂ a₁₂ h).inv.toNatTrans.app M ≫ (F.map a₁₂).toFunctor.map x ≫
        (F.mapComp' a₁ a₂ a₁₂ h).hom.toNatTrans.app N := by
  symm
  exact ((Cat.Hom.toNatIso (F.mapComp' a₁ a₂ a₁₂ h)).app M).inv_comp_eq.mpr
    (F.mapComp'_hom_naturality a₁ a₂ a₁₂ h x)

lemma map_eq {b₀ b₁ b₂ : LocallyDiscrete Cᵒᵖ} (a₁ : b₀ ⟶ b₁) (a₂ : b₁ ⟶ b₂) (a₁₂ : b₀ ⟶ b₂)
    (h : a₁ ≫ a₂ = a₁₂) {M N : F.obj b₀} (x : M ⟶ N) :
    (F.map a₁₂).toFunctor.map x =
      (F.mapComp' a₁ a₂ a₁₂ h).hom.toNatTrans.app M ≫ (F.map a₂).toFunctor.map
          ((F.map a₁).toFunctor.map x) ≫
        (F.mapComp' a₁ a₂ a₁₂ h).inv.toNatTrans.app N := by
  rw [← Category.assoc]
  symm
  exact ((Cat.Hom.toNatIso (F.mapComp' a₁ a₂ a₁₂ h)).app N).comp_inv_eq.mpr
    (F.mapComp'_hom_naturality a₁ a₂ a₁₂ h x).symm

lemma restrMap_comp_restrMap {Y₀' Y₀ Y : C} (g : Y₀' ⟶ Y₀) (q₀ : Y₀ ⟶ S) (q₀' : Y₀' ⟶ S) (hq : g
    ≫ q₀ = q₀')
    (y : Y ⟶ S) (fj : Y₀ ⟶ Y) (hfj : fj ≫ y = q₀) (gfj : Y₀' ⟶ Y) (hgfj : g ≫ fj = gfj) :
    restrMap f q₀ q₀' g hq ≫ restrMap f y q₀ fj hfj =
      restrMap f y q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, restrMap_fst, restrMap_fst, restrMap_fst]
  · rw [Category.assoc, restrMap_snd, restrMap_snd_assoc, restrMap_snd, hgfj]

@[simps]
def objIso {ι : Type t} {S' : C} {X' : ι → C} {f' : ∀ i, X' i ⟶ S'} {D₁ D₂ : F.DescentData f'}
    (e : D₁ ≅ D₂) (i : ι) : D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by rw [← comp_hom, e.hom_inv_id, id_hom]
  inv_hom_id := by rw [← comp_hom, e.inv_hom_id, id_hom]

section glue

variable {f}
  (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
  (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))),
      P M → P ((F.map g.op.toLoc).toFunctor.obj M))
  (hf : ∀ ⦃Z : C⦄ (z : Z ⟶ S) (M N : F.obj (.mk (op Z))), P M → P N →
    Function.Bijective ((F.toDescentData (fun _ : Unit => pullback.snd f z)).map : (M ⟶ N) → _))
  {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S)
  (D : F.DescentData (fun _ : Unit => f))
  (L : ∀ i, F.obj (.mk (op (U i)))) (hL : ∀ i, P (L i))
  (ψ : ∀ i, (F.toDescentData (fun _ : Unit => pullback.snd f (u i))).obj (L i) ≅ (restr F f
      (u i)).obj D)

noncomputable def theta {Y₀ : C} (q₀ : Y₀ ⟶ S) {i : ι} (g : Y₀ ⟶ U i) (hg : g ≫ u i = q₀) :
    (F.toDescentData (fun _ : Unit => pullback.snd f q₀)).obj ((F.map g.op.toLoc).toFunctor.obj
        (L i)) ≅
      (restr F f q₀).obj D :=
  ((toDescentDataRestrAlongIso F f (u i) q₀ g hg).app (L i)).symm ≪≫
    (restrAlong F f (u i) q₀ g hg).mapIso (ψ i) ≪≫ (restrCompIso F f (u i) q₀ g hg).app D

noncomputable def gluedHom {Y₀ : C} (q₀ : Y₀ ⟶ S) {i₁ i₂ : ι} (g₁ : Y₀ ⟶ U i₁) (g₂ : Y₀ ⟶ U i₂)
    (h₁ : g₁ ≫ u i₁ = q₀) (h₂ : g₂ ≫ u i₂ = q₀) :
    (F.map g₁.op.toLoc).toFunctor.obj (L i₁) ⟶ (F.map g₂.op.toLoc).toFunctor.obj (L i₂) :=
  (Equiv.ofBijective _ (hf q₀ _ _ (hP g₁ _ (hL i₁)) (hP g₂ _ (hL i₂)))).symm
    (theta F u D L ψ q₀ g₁ h₁ ≪≫ (theta F u D L ψ q₀ g₂ h₂).symm).hom

lemma map_gluedHom {Y₀ : C} (q₀ : Y₀ ⟶ S) {i₁ i₂ : ι} (g₁ : Y₀ ⟶ U i₁) (g₂ : Y₀ ⟶ U i₂)
    (h₁ : g₁ ≫ u i₁ = q₀) (h₂ : g₂ ≫ u i₂ = q₀) :
    (F.toDescentData (fun _ : Unit => pullback.snd f q₀)).map
        (gluedHom F P hP hf u D L hL ψ q₀ g₁ g₂ h₁ h₂) =
      (theta F u D L ψ q₀ g₁ h₁ ≪≫ (theta F u D L ψ q₀ g₂ h₂).symm).hom :=
  Equiv.ofBijective_apply_symm_apply _ _ _

set_option backward.defeqAttrib.useBackward true in
lemma theta_hom_hom {Y₀ : C} (q₀ : Y₀ ⟶ S) {i : ι} (fj : Y₀ ⟶ U i) (hfj : fj ≫ u i = q₀) :
    (theta F u D L ψ q₀ fj hfj).hom.hom () =
      (F.mapComp' fj.op.toLoc (pullback.snd f q₀).op.toLoc (pullback.snd f q₀ ≫ fj).op.toLoc
          rfl).inv.toNatTrans.app
          (L i) ≫
        (F.mapComp' (pullback.snd f (u i)).op.toLoc (restrMap f (u i) q₀ fj hfj).op.toLoc
          (pullback.snd f q₀ ≫ fj).op.toLoc (op_toLoc_comp _ _ (restrMap_snd f (u i) q₀ fj
              hfj))).hom.toNatTrans.app
          (L i) ≫
        (F.map (restrMap f (u i) q₀ fj hfj).op.toLoc).toFunctor.map ((ψ i).hom.hom ()) ≫
        (F.mapComp' (pullback.fst f (u i)).op.toLoc (restrMap f (u i) q₀ fj hfj).op.toLoc
            (pullback.fst f q₀).op.toLoc
          (op_toLoc_comp _ _ (restrMap_fst f (u i) q₀ fj hfj))).inv.toNatTrans.app (D.obj ()) := by
  simp only [theta, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
      comp_hom,
    toDescentDataRestrAlongIso, restrAlong, restrCompIso, toDescentDataCompPullFunctorIso,
    pullFunctorCompIso_hom_app_hom, pullFunctor_map_hom, NatIso.ofComponents_inv_app, isoMk_inv_hom,
    Iso.symm_inv, Cat.Hom.toNatIso_hom]
  try rw [F.isoMapOfCommSq_eq _ ((pullback.snd f q₀ ≫ fj).op.toLoc) rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app, Cat.Hom.toNatIso_hom, Category.assoc]
  exact Category.assoc _ _ _

set_option backward.defeqAttrib.useBackward true in
lemma theta_hom_hom_comp {Y₀' Y₀ : C} (g : Y₀' ⟶ Y₀) (q₀ : Y₀ ⟶ S) (q₀' : Y₀' ⟶ S) (hq : g ≫ q₀
    = q₀')
    {i : ι} (fj : Y₀ ⟶ U i) (hfj : fj ≫ u i = q₀) (gfj : Y₀' ⟶ U i) (hgfj : g ≫ fj = gfj) :
    (theta F u D L ψ q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq])).hom.hom () =
      (F.map (pullback.snd f q₀').op.toLoc).toFunctor.map
          ((F.mapComp' fj.op.toLoc g.op.toLoc gfj.op.toLoc (op_toLoc_comp _ _
              hgfj)).hom.toNatTrans.app (L i)) ≫
        (F.mapComp' g.op.toLoc (pullback.snd f q₀').op.toLoc (pullback.snd f q₀' ≫ g).op.toLoc
            rfl).inv.toNatTrans.app
          ((F.map fj.op.toLoc).toFunctor.obj (L i)) ≫
        (F.mapComp' (pullback.snd f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc (pullback.snd f
            q₀' ≫ g).op.toLoc
          (op_toLoc_comp _ _ (restrMap_snd f q₀ q₀' g hq))).hom.toNatTrans.app
            ((F.map fj.op.toLoc).toFunctor.obj (L i)) ≫
        (F.map (restrMap f q₀ q₀' g hq).op.toLoc).toFunctor.map ((theta F u D L ψ q₀ fj
            hfj).hom.hom ()) ≫
        (F.mapComp' (pullback.fst f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc (pullback.fst f
            q₀').op.toLoc
          (op_toLoc_comp _ _ (restrMap_fst f q₀ q₀' g hq))).inv.toNatTrans.app (D.obj ()) := by
  have hρr := restrMap_comp_restrMap f g q₀ q₀' hq (u i) fj hfj gfj hgfj
  rw [theta_hom_hom, theta_hom_hom]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have h1 := map_map_eq F (restrMap f (u i) q₀ fj hfj).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc
    (restrMap f (u i) q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq])).op.toLoc (op_toLoc_comp _
        _ hρr)
    ((ψ i).hom.hom ())
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at h1
  rw [h1]
  try simp only [Category.assoc]
  have h2 := F.mapComp'₀₁₃_inv_app (pullback.fst f (u i)).op.toLoc (restrMap f (u i) q₀ fj
      hfj).op.toLoc
    (restrMap f q₀ q₀' g hq).op.toLoc (pullback.fst f q₀).op.toLoc
    (restrMap f (u i) q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq])).op.toLoc (pullback.fst f
        q₀').op.toLoc
    (op_toLoc_comp _ _ (restrMap_fst f (u i) q₀ fj hfj)) (op_toLoc_comp _ _ hρr)
    (op_toLoc_comp _ _ (restrMap_fst f (u i) q₀' gfj _)) (D.obj ())
  rw [← h2]
  have h3 := F.mapComp'₀₁₃_hom_app (pullback.snd f (u i)).op.toLoc (restrMap f (u i) q₀ fj
      hfj).op.toLoc
    (restrMap f q₀ q₀' g hq).op.toLoc (pullback.snd f q₀ ≫ fj).op.toLoc
    (restrMap f (u i) q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq])).op.toLoc (pullback.snd f
        q₀' ≫ gfj).op.toLoc
    (op_toLoc_comp _ _ (restrMap_snd f (u i) q₀ fj hfj)) (op_toLoc_comp _ _ hρr)
    (op_toLoc_comp _ _ (restrMap_snd f (u i) q₀' gfj _)) (L i)
  rw [h3]
  try simp only [Category.assoc]
  have h4 := F.mapComp'₀₂₃_hom_app fj.op.toLoc (pullback.snd f q₀).op.toLoc (restrMap f q₀ q₀' g
      hq).op.toLoc
    (pullback.snd f q₀ ≫ fj).op.toLoc (pullback.snd f q₀' ≫ g).op.toLoc (pullback.snd f q₀'
        ≫ gfj).op.toLoc
    rfl (op_toLoc_comp _ _ (restrMap_snd f q₀ q₀' g hq))
    (op_toLoc_comp _ _ (by rw [restrMap_snd_assoc, hgfj])) (L i)
  rw [h4]
  try simp only [Category.assoc]
  have h5 := F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app fj.op.toLoc g.op.toLoc (pullback.snd f
      q₀').op.toLoc
    gfj.op.toLoc (pullback.snd f q₀' ≫ g).op.toLoc (pullback.snd f q₀' ≫ gfj).op.toLoc
    (op_toLoc_comp _ _ hgfj) rfl (op_toLoc_comp _ _ rfl) (L i)
  rw [reassoc_of% h5]

set_option backward.defeqAttrib.useBackward true in
lemma theta_inv_hom_comp {Y₀' Y₀ : C} (g : Y₀' ⟶ Y₀) (q₀ : Y₀ ⟶ S) (q₀' : Y₀' ⟶ S) (hq : g ≫ q₀
    = q₀')
    {i : ι} (fj : Y₀ ⟶ U i) (hfj : fj ≫ u i = q₀) (gfj : Y₀' ⟶ U i) (hgfj : g ≫ fj = gfj) :
    (theta F u D L ψ q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq])).inv.hom () =
      (F.mapComp' (pullback.fst f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc (pullback.fst f
          q₀').op.toLoc
          (op_toLoc_comp _ _ (restrMap_fst f q₀ q₀' g hq))).hom.toNatTrans.app (D.obj ()) ≫
        (F.map (restrMap f q₀ q₀' g hq).op.toLoc).toFunctor.map ((theta F u D L ψ q₀ fj
            hfj).inv.hom ()) ≫
        (F.mapComp' (pullback.snd f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc (pullback.snd f
            q₀' ≫ g).op.toLoc
          (op_toLoc_comp _ _ (restrMap_snd f q₀ q₀' g hq))).inv.toNatTrans.app
            ((F.map fj.op.toLoc).toFunctor.obj (L i)) ≫
        (F.mapComp' g.op.toLoc (pullback.snd f q₀').op.toLoc (pullback.snd f q₀' ≫ g).op.toLoc
            rfl).hom.toNatTrans.app
          ((F.map fj.op.toLoc).toFunctor.obj (L i)) ≫
        (F.map (pullback.snd f q₀').op.toLoc).toFunctor.map
          ((F.mapComp' fj.op.toLoc g.op.toLoc gfj.op.toLoc (op_toLoc_comp _ _
              hgfj)).inv.toNatTrans.app (L i)) := by
  let B : (F.map (pullback.snd f q₀').op.toLoc).toFunctor.obj ((F.map gfj.op.toLoc).toFunctor.obj
      (L i)) ≅
      (F.map (pullback.fst f q₀').op.toLoc).toFunctor.obj (D.obj ()) :=
    (F.map (pullback.snd f q₀').op.toLoc).toFunctor.mapIso
        ((Cat.Hom.toNatIso (F.mapComp' fj.op.toLoc g.op.toLoc gfj.op.toLoc (op_toLoc_comp _ _
            hgfj))).app (L i)) ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' g.op.toLoc (pullback.snd f q₀').op.toLoc (pullback.snd f q₀'
          ≫ g).op.toLoc
        rfl)).app ((F.map fj.op.toLoc).toFunctor.obj (L i))).symm ≪≫
      (Cat.Hom.toNatIso (F.mapComp' (pullback.snd f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc
        (pullback.snd f q₀' ≫ g).op.toLoc (op_toLoc_comp _ _ (restrMap_snd f q₀ q₀' g hq)))).app
          ((F.map fj.op.toLoc).toFunctor.obj (L i)) ≪≫
      (F.map (restrMap f q₀ q₀' g hq).op.toLoc).toFunctor.mapIso (objIso F (theta F u D L ψ q₀ fj
          hfj) ()) ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' (pullback.fst f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc
        (pullback.fst f q₀').op.toLoc (op_toLoc_comp _ _ (restrMap_fst f q₀ q₀' g hq)))).app (D.obj
            ())).symm
  have hAB : objIso F (theta F u D L ψ q₀' gfj (by rw [← hgfj, Category.assoc, hfj, hq])) ()
      = B := by
    ext
    exact theta_hom_hom_comp F u D L ψ g q₀ q₀' hq fj hfj gfj hgfj
  have := congrArg Iso.inv hAB
  simp only [objIso_inv] at this
  rw [this]
  simp only [B, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
      objIso_inv,
    Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Category.assoc]
  try rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
theorem pullHom_gluedHom ⦃Y₀' Y₀ : C⦄ (g : Y₀' ⟶ Y₀) (q₀ : Y₀ ⟶ S) (q₀' : Y₀' ⟶ S) (hq : g ≫ q₀
    = q₀')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y₀ ⟶ U i₁) (f₂ : Y₀ ⟶ U i₂) (hf₁ : f₁ ≫ u i₁ = q₀) (hf₂ : f₂ ≫ u i₂ = q₀)
    (gf₁ : Y₀' ⟶ U i₁) (gf₂ : Y₀' ⟶ U i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    LocallyDiscreteOpToCat.pullHom (gluedHom F P hP hf u D L hL ψ q₀ f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁
        hgf₂ =
      gluedHom F P hP hf u D L hL ψ q₀' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) := by
  apply (hf q₀' _ _ (hP gf₁ _ (hL i₁)) (hP gf₂ _ (hL i₂))).1
  rw [map_gluedHom]
  ext ⟨⟩
  have key : (F.map (pullback.snd f q₀).op.toLoc).toFunctor.map (gluedHom F P hP hf u D L hL ψ q₀
      f₁ f₂ hf₁ hf₂) =
      (theta F u D L ψ q₀ f₁ hf₁).hom.hom () ≫ (theta F u D L ψ q₀ f₂ hf₂).inv.hom () := by
    have := congrArg (fun χ => DescentData.Hom.hom χ ()) (map_gluedHom F P hP hf u D L hL ψ q₀ f₁
        f₂ hf₁ hf₂)
    simp only [toDescentData_map_hom, Iso.trans_hom, Iso.symm_hom, comp_hom] at this
    exact this
  simp only [toDescentData_map_hom, Iso.trans_hom, Iso.symm_hom, comp_hom]
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have e1 := map_map_eq F g.op.toLoc (pullback.snd f q₀').op.toLoc (pullback.snd f q₀'
      ≫ g).op.toLoc rfl
    (gluedHom F P hP hf u D L hL ψ q₀ f₁ f₂ hf₁ hf₂)
  have e2 := map_eq F (pullback.snd f q₀).op.toLoc (restrMap f q₀ q₀' g hq).op.toLoc (pullback.snd
      f q₀' ≫ g).op.toLoc
    (op_toLoc_comp _ _ (restrMap_snd f q₀ q₀' g hq)) (gluedHom F P hP hf u D L hL ψ q₀ f₁ f₂ hf₁
        hf₂)
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at e1 e2 key
  rw [e1, e2, key]
  simp only [Functor.map_comp, Category.assoc]
  rw [theta_hom_hom_comp F u D L ψ g q₀ q₀' hq f₁ hf₁ gf₁ hgf₁,
    theta_inv_hom_comp F u D L ψ g q₀ q₀' hq f₂ hf₂ gf₂ hgf₂]
  have e3 := Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' (pullback.fst f q₀).op.toLoc
    (restrMap f q₀ q₀' g hq).op.toLoc (pullback.fst f q₀').op.toLoc (op_toLoc_comp _ _
        (restrMap_fst f q₀ q₀' g hq)))
    (D.obj ())
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at e3
  simp only [Category.assoc]
  first
    | rw [reassoc_of% e3]
    | erw [reassoc_of% e3]
  try rfl

noncomputable def gluedData : F.DescentData u where
  obj := L
  hom Y₀ q₀ i₁ i₂ g₁ g₂ h₁ h₂ := gluedHom F P hP hf u D L hL ψ q₀ g₁ g₂ h₁ h₂
  pullHom_hom Y₀' Y₀ g q₀ q₀' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    pullHom_gluedHom F P hP hf u D L hL ψ g q₀ q₀' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  hom_self Y₀ q₀ i g hg := by
    apply (hf q₀ _ _ (hP g _ (hL i)) (hP g _ (hL i))).1
    rw [map_gluedHom, Iso.self_symm_id, Functor.map_id]
    rfl
  hom_comp Y₀ q₀ i₁ i₂ i₃ g₁ g₂ g₃ h₁ h₂ h₃ := by
    apply (hf q₀ _ _ (hP g₁ _ (hL i₁)) (hP g₃ _ (hL i₃))).1
    rw [Functor.map_comp, map_gluedHom, map_gluedHom, map_gluedHom]
    simp

@[scoped simp]
lemma gluedData_obj (i : ι) : (gluedData F P hP hf u D L hL ψ).obj i = L i := rfl

set_option backward.defeqAttrib.useBackward true in
lemma theta_inv_hom {Y₀ : C} (q₀ : Y₀ ⟶ S) {i : ι} (fj : Y₀ ⟶ U i) (hfj : fj ≫ u i = q₀) :
    (theta F u D L ψ q₀ fj hfj).inv.hom () =
      (F.mapComp' (pullback.fst f (u i)).op.toLoc (restrMap f (u i) q₀ fj hfj).op.toLoc
          (pullback.fst f q₀).op.toLoc
          (op_toLoc_comp _ _ (restrMap_fst f (u i) q₀ fj hfj))).hom.toNatTrans.app (D.obj ()) ≫
        (F.map (restrMap f (u i) q₀ fj hfj).op.toLoc).toFunctor.map ((ψ i).inv.hom ()) ≫
        (F.mapComp' (pullback.snd f (u i)).op.toLoc (restrMap f (u i) q₀ fj hfj).op.toLoc
          (pullback.snd f q₀ ≫ fj).op.toLoc (op_toLoc_comp _ _ (restrMap_snd f (u i) q₀ fj
              hfj))).inv.toNatTrans.app
          (L i) ≫
        (F.mapComp' fj.op.toLoc (pullback.snd f q₀).op.toLoc (pullback.snd f q₀ ≫ fj).op.toLoc
            rfl).hom.toNatTrans.app
          (L i) := by
  let B : (F.map (pullback.snd f q₀).op.toLoc).toFunctor.obj ((F.map fj.op.toLoc).toFunctor.obj
      (L i)) ≅
      (F.map (pullback.fst f q₀).op.toLoc).toFunctor.obj (D.obj ()) :=
    ((Cat.Hom.toNatIso (F.mapComp' fj.op.toLoc (pullback.snd f q₀).op.toLoc (pullback.snd f q₀
        ≫ fj).op.toLoc
        rfl)).app (L i)).symm ≪≫
      (Cat.Hom.toNatIso (F.mapComp' (pullback.snd f (u i)).op.toLoc (restrMap f (u i) q₀ fj
          hfj).op.toLoc
        (pullback.snd f q₀ ≫ fj).op.toLoc (op_toLoc_comp _ _ (restrMap_snd f (u i) q₀ fj
            hfj)))).app (L i) ≪≫
      (F.map (restrMap f (u i) q₀ fj hfj).op.toLoc).toFunctor.mapIso (objIso F (ψ i) ()) ≪≫
      ((Cat.Hom.toNatIso (F.mapComp' (pullback.fst f (u i)).op.toLoc (restrMap f (u i) q₀ fj
          hfj).op.toLoc
        (pullback.fst f q₀).op.toLoc (op_toLoc_comp _ _ (restrMap_fst f (u i) q₀ fj hfj)))).app
            (D.obj ())).symm
  have hAB : objIso F (theta F u D L ψ q₀ fj hfj) () = B := by
    ext
    exact theta_hom_hom F u D L ψ q₀ fj hfj
  have := congrArg Iso.inv hAB
  simp only [objIso_inv] at this
  rw [this]
  simp only [B, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
      objIso_inv,
    Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv, Category.assoc]
  try rfl

lemma map_snd_gluedHom {Y₀ : C} (q₀ : Y₀ ⟶ S) {i₁ i₂ : ι} (g₁ : Y₀ ⟶ U i₁) (g₂ : Y₀ ⟶ U i₂)
    (h₁ : g₁ ≫ u i₁ = q₀) (h₂ : g₂ ≫ u i₂ = q₀) :
    (F.map (pullback.snd f q₀).op.toLoc).toFunctor.map (gluedHom F P hP hf u D L hL ψ q₀ g₁ g₂ h₁
        h₂) =
      (theta F u D L ψ q₀ g₁ h₁).hom.hom () ≫ (theta F u D L ψ q₀ g₂ h₂).inv.hom () := by
  have := congrArg (fun χ => DescentData.Hom.hom χ ()) (map_gluedHom F P hP hf u D L hL ψ q₀ g₁ g₂
      h₁ h₂)
  simp only [toDescentData_map_hom, Iso.trans_hom, Iso.symm_hom, comp_hom] at this
  exact this

noncomputable def sectionOf ⦃W : C⦄ (w : W ⟶ X) : W ⟶ pullback f (w ≫ f) :=
  pullback.lift w (𝟙 W) (by simp)

@[reassoc (attr := simp)]
lemma sectionOf_fst ⦃W : C⦄ (w : W ⟶ X) : sectionOf (f := f) w ≫ pullback.fst f (w ≫ f)
    = w := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sectionOf_snd ⦃W : C⦄ (w : W ⟶ X) : sectionOf (f := f) w ≫ pullback.snd f (w ≫ f)
    = 𝟙 W := pullback.lift_snd _ _ _

lemma sectionOf_restrMap ⦃W : C⦄ (w : W ⟶ X) {i : ι} (k : W ⟶ pullback f (u i))
    (hk : k ≫ pullback.fst f (u i) = w) (h : (k ≫ pullback.snd f (u i)) ≫ u i = w ≫ f) :
    sectionOf (f := f) w ≫ restrMap f (u i) (w ≫ f) (k ≫ pullback.snd f (u i)) h = k := by
  apply pullback.hom_ext
  · rw [Category.assoc, restrMap_fst, sectionOf_fst, hk]
  · rw [Category.assoc, restrMap_snd, sectionOf_snd_assoc]

set_option backward.defeqAttrib.useBackward true in
lemma gluedHom_eq_of_fac ⦃W : C⦄ (w : W ⟶ X) ⦃i₁ i₂ : ι⦄ (k₁ : W ⟶ pullback f (u i₁))
    (k₂ : W ⟶ pullback f (u i₂)) (hk₁ : k₁ ≫ pullback.fst f (u i₁) = w) (hk₂ : k₂ ≫ pullback.fst f
        (u i₂) = w)
    (h₁ : (k₁ ≫ pullback.snd f (u i₁)) ≫ u i₁ = w ≫ f) (h₂ : (k₂ ≫ pullback.snd f (u i₂)) ≫ u i₂
        = w ≫ f) :
    gluedHom F P hP hf u D L hL ψ (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) (k₂ ≫ pullback.snd f (u i₂))
        h₁ h₂ =
      (F.mapComp' (pullback.snd f (u i₁)).op.toLoc k₁.op.toLoc (k₁ ≫ pullback.snd f (u i₁)).op.toLoc
          rfl).hom.toNatTrans.app (L i₁) ≫
        (F.map k₁.op.toLoc).toFunctor.map ((ψ i₁).hom.hom ()) ≫
        (F.mapComp' (pullback.fst f (u i₁)).op.toLoc k₁.op.toLoc w.op.toLoc
          (op_toLoc_comp _ _ hk₁)).inv.toNatTrans.app (D.obj ()) ≫
        (F.mapComp' (pullback.fst f (u i₂)).op.toLoc k₂.op.toLoc w.op.toLoc
          (op_toLoc_comp _ _ hk₂)).hom.toNatTrans.app (D.obj ()) ≫
        (F.map k₂.op.toLoc).toFunctor.map ((ψ i₂).inv.hom ()) ≫
        (F.mapComp' (pullback.snd f (u i₂)).op.toLoc k₂.op.toLoc (k₂ ≫ pullback.snd f
            (u i₂)).op.toLoc
          rfl).inv.toNatTrans.app (L i₂) := by
  have hσ₁ := sectionOf_restrMap (f := f) u w k₁ hk₁ h₁
  have hσ₂ := sectionOf_restrMap (f := f) u w k₂ hk₂ h₂
  have hs₁ : (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f (u i₁)) ≫ u i₁ = pullback.snd f (w ≫ f)
      ≫ w ≫ f := by
    rw [Category.assoc, Category.assoc, ← Category.assoc k₁, h₁]
  have hs₂ : (pullback.snd f (w ≫ f) ≫ k₂ ≫ pullback.snd f (u i₂)) ≫ u i₂ = pullback.snd f (w ≫ f)
      ≫ w ≫ f := by
    rw [Category.assoc, Category.assoc, ← Category.assoc k₂, h₂]
  have A1 := pullHom_gluedHom F P hP hf u D L hL ψ (pullback.snd f (w ≫ f)) (w ≫ f)
    (pullback.snd f (w ≫ f) ≫ w ≫ f) rfl (k₁ ≫ pullback.snd f (u i₁)) (k₂ ≫ pullback.snd f (u i₂))
        h₁ h₂
    (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f (u i₁)) (pullback.snd f (w ≫ f) ≫ k₂
        ≫ pullback.snd f (u i₂)) rfl rfl
  have A2 := pullHom_gluedHom F P hP hf u D L hL ψ (sectionOf (f := f) w) (pullback.snd f (w ≫ f)
      ≫ w ≫ f) (w ≫ f)
    (by rw [sectionOf_snd_assoc]) (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f (u i₁))
    (pullback.snd f (w ≫ f) ≫ k₂ ≫ pullback.snd f (u i₂)) hs₁ hs₂
    (k₁ ≫ pullback.snd f (u i₁)) (k₂ ≫ pullback.snd f (u i₂)) (by rw [sectionOf_snd_assoc]) (by rw
        [sectionOf_snd_assoc])
  rw [← A2]
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  rw [← A1]
  dsimp only [LocallyDiscreteOpToCat.pullHom]
  rw [map_snd_gluedHom, theta_hom_hom, theta_inv_hom]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj]
  have cG₁ := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' (k₁ ≫ pullback.snd f (u i₁)).op.toLoc
    (pullback.snd f (w ≫ f)).op.toLoc (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f
        (u i₁)).op.toLoc rfl) (L i₁)
  have cG₂ := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' (k₂ ≫ pullback.snd f (u i₂)).op.toLoc
    (pullback.snd f (w ≫ f)).op.toLoc (pullback.snd f (w ≫ f) ≫ k₂ ≫ pullback.snd f
        (u i₂)).op.toLoc rfl) (L i₂)
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at cG₁ cG₂
  simp only [Category.assoc]
  rw [reassoc_of% cG₁, cG₂, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  have m1 := map_map_eq F (restrMap f (u i₁) (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) h₁).op.toLoc
      (sectionOf (f := f) w).op.toLoc
    k₁.op.toLoc (op_toLoc_comp _ _ hσ₁) ((ψ i₁).hom.hom ())
  have m2 := map_map_eq F (restrMap f (u i₂) (w ≫ f) (k₂ ≫ pullback.snd f (u i₂)) h₂).op.toLoc
      (sectionOf (f := f) w).op.toLoc
    k₂.op.toLoc (op_toLoc_comp _ _ hσ₂) ((ψ i₂).inv.hom ())
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at m1 m2
  rw [m1, m2]
  simp only [Category.assoc]
  have b1 := F.mapComp'₀₂₃_hom_app (pullback.snd f (u i₁)).op.toLoc
    (restrMap f (u i₁) (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) h₁).op.toLoc (sectionOf (f := f)
        w).op.toLoc
    (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f (u i₁)).op.toLoc k₁.op.toLoc (k₁ ≫ pullback.snd f
        (u i₁)).op.toLoc
    (op_toLoc_comp _ _ (restrMap_snd f (u i₁) (w ≫ f) _ h₁)) (op_toLoc_comp _ _ hσ₁)
    (op_toLoc_comp _ _ (by rw [sectionOf_snd_assoc])) (L i₁)
  rw [b1]
  simp only [Category.assoc]
  have cA : (F.map (sectionOf (f := f) w).op.toLoc).toFunctor.map ((F.mapComp' (pullback.snd f
      (u i₁)).op.toLoc
      (restrMap f (u i₁) (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) h₁).op.toLoc
      (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f (u i₁)).op.toLoc
      (op_toLoc_comp _ _ (restrMap_snd f (u i₁) (w ≫ f) _ h₁))).inv.toNatTrans.app (L i₁)) ≫
      (F.map (sectionOf (f := f) w).op.toLoc).toFunctor.map ((F.mapComp' (pullback.snd f
          (u i₁)).op.toLoc
      (restrMap f (u i₁) (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) h₁).op.toLoc
      (pullback.snd f (w ≫ f) ≫ k₁ ≫ pullback.snd f (u i₁)).op.toLoc
      (op_toLoc_comp _ _ (restrMap_snd f (u i₁) (w ≫ f) _ h₁))).hom.toNatTrans.app (L i₁))
          = 𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id]
  have cB := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp'
    (restrMap f (u i₁) (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) h₁).op.toLoc (sectionOf (f := f)
        w).op.toLoc k₁.op.toLoc
    (op_toLoc_comp _ _ hσ₁)) ((F.map (pullback.snd f (u i₁)).op.toLoc).toFunctor.obj (L i₁))
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at cA cB
  rw [reassoc_of% cA, reassoc_of% cB]
  have b2 := F.mapComp'₀₁₃_inv_app (pullback.fst f (u i₁)).op.toLoc
    (restrMap f (u i₁) (w ≫ f) (k₁ ≫ pullback.snd f (u i₁)) h₁).op.toLoc (sectionOf (f := f)
        w).op.toLoc
    (pullback.fst f (w ≫ f)).op.toLoc k₁.op.toLoc w.op.toLoc
    (op_toLoc_comp _ _ (restrMap_fst f (u i₁) (w ≫ f) _ h₁)) (op_toLoc_comp _ _ hσ₁) (op_toLoc_comp
        _ _ hk₁) (D.obj ())
  have b3 := F.mapComp'₀₁₃_hom_app (pullback.fst f (u i₂)).op.toLoc
    (restrMap f (u i₂) (w ≫ f) (k₂ ≫ pullback.snd f (u i₂)) h₂).op.toLoc (sectionOf (f := f)
        w).op.toLoc
    (pullback.fst f (w ≫ f)).op.toLoc k₂.op.toLoc w.op.toLoc
    (op_toLoc_comp _ _ (restrMap_fst f (u i₂) (w ≫ f) _ h₂)) (op_toLoc_comp _ _ hσ₂) (op_toLoc_comp
        _ _ hk₂) (D.obj ())
  rw [b2, b3]
  simp only [Category.assoc]
  have cC := Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' (pullback.fst f (w ≫ f)).op.toLoc
    (sectionOf (f := f) w).op.toLoc w.op.toLoc (op_toLoc_comp _ _ (sectionOf_fst (f := f) w)))
        (D.obj ())
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at cC
  rw [reassoc_of% cC]
  have b4 := F.mapComp'₀₂₃_inv_app (pullback.snd f (u i₂)).op.toLoc
    (restrMap f (u i₂) (w ≫ f) (k₂ ≫ pullback.snd f (u i₂)) h₂).op.toLoc (sectionOf (f := f)
        w).op.toLoc
    (pullback.snd f (w ≫ f) ≫ k₂ ≫ pullback.snd f (u i₂)).op.toLoc k₂.op.toLoc (k₂ ≫ pullback.snd f
        (u i₂)).op.toLoc
    (op_toLoc_comp _ _ (restrMap_snd f (u i₂) (w ≫ f) _ h₂)) (op_toLoc_comp _ _ hσ₂)
    (op_toLoc_comp _ _ (by rw [sectionOf_snd_assoc])) (L i₂)
  rw [b4]
  have cD : (F.map (sectionOf (f := f) w).op.toLoc).toFunctor.map ((F.mapComp' (pullback.snd f
      (u i₂)).op.toLoc
      (restrMap f (u i₂) (w ≫ f) (k₂ ≫ pullback.snd f (u i₂)) h₂).op.toLoc
      (pullback.snd f (w ≫ f) ≫ k₂ ≫ pullback.snd f (u i₂)).op.toLoc
      (op_toLoc_comp _ _ (restrMap_snd f (u i₂) (w ≫ f) _ h₂))).inv.toNatTrans.app (L i₂)) ≫
      (F.map (sectionOf (f := f) w).op.toLoc).toFunctor.map ((F.mapComp' (pullback.snd f
          (u i₂)).op.toLoc
      (restrMap f (u i₂) (w ≫ f) (k₂ ≫ pullback.snd f (u i₂)) h₂).op.toLoc
      (pullback.snd f (w ≫ f) ≫ k₂ ≫ pullback.snd f (u i₂)).op.toLoc
      (op_toLoc_comp _ _ (restrMap_snd f (u i₂) (w ≫ f) _ h₂))).hom.toNatTrans.app (L i₂))
          = 𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id]
  have cE := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp'
    (restrMap f (u i₂) (w ≫ f) (k₂ ≫ pullback.snd f (u i₂)) h₂).op.toLoc (sectionOf (f := f)
        w).op.toLoc k₂.op.toLoc
    (op_toLoc_comp _ _ hσ₂)) ((F.map (pullback.snd f (u i₂)).op.toLoc).toFunctor.obj (L i₂))
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at cD cE
  rw [reassoc_of% cD, reassoc_of% cE]

end glue

section compare

variable {f} {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S) (D : F.DescentData (fun _ : Unit => f))
  (L₀ : F.obj (.mk (op S)))
  (Ψloc : ∀ i, (restr F f (u i)).obj ((F.toDescentData (fun _ : Unit => f)).obj L₀) ≅ (restr F f
      (u i)).obj D)
  (hX : (F.toDescentData (fun i => pullback.fst f (u i))).FullyFaithful)

variable
  (hΨ : ∀ ⦃W : C⦄ (w : W ⟶ X) ⦃i₁ i₂ : ι⦄ (k₁ : W ⟶ pullback f (u i₁)) (k₂ : W ⟶ pullback f (u i₂))
    (hk₁ : k₁ ≫ pullback.fst f (u i₁) = w) (hk₂ : k₂ ≫ pullback.fst f (u i₂) = w),
    (F.map k₁.op.toLoc).toFunctor.map ((Ψloc i₁).hom.hom ()) ≫
        ((F.toDescentData (fun i => pullback.fst f (u i))).obj (D.obj ())).hom w k₁ k₂ hk₁ hk₂ =
      ((F.toDescentData (fun i => pullback.fst f (u i))).obj
          ((F.map f.op.toLoc).toFunctor.obj L₀)).hom w k₁ k₂ hk₁ hk₂ ≫
        (F.map k₂.op.toLoc).toFunctor.map ((Ψloc i₂).hom.hom ()))

noncomputable def compareDescentDataIso :
    (F.toDescentData (fun i => pullback.fst f (u i))).obj ((F.map f.op.toLoc).toFunctor.obj L₀) ≅
      (F.toDescentData (fun i => pullback.fst f (u i))).obj (D.obj ()) :=
  isoMk (fun i => objIso F (Ψloc i) ()) (fun W w i₁ i₂ k₁ k₂ hk₁ hk₂ => hΨ w k₁ k₂ hk₁ hk₂)

noncomputable def compareIso : (F.map f.op.toLoc).toFunctor.obj L₀ ≅ D.obj () :=
  hX.preimageIso (compareDescentDataIso F u D L₀ Ψloc hΨ)

lemma map_compareIso_hom (i : ι) :
    (F.map (pullback.fst f (u i)).op.toLoc).toFunctor.map (compareIso F u D L₀ Ψloc hX hΨ).hom
        = (Ψloc i).hom.hom () := by
  have := congrArg (fun χ => DescentData.Hom.hom χ i) (hX.map_preimage (compareDescentDataIso F u D
      L₀ Ψloc hΨ).hom)
  simp only [compareIso, Functor.FullyFaithful.preimageIso_hom, toDescentData_map_hom,
      compareDescentDataIso,
    isoMk_hom_hom, objIso_hom] at this
  exact this

noncomputable def liftTest ⦃W : C⦄ (w : W ⟶ S) (k : W ⟶ X) (hk : k ≫ f = w) (i : ι) :
    pullback w (u i) ⟶ pullback f (u i) :=
  pullback.lift (pullback.fst w (u i) ≫ k) (pullback.snd w (u i))
    (by rw [Category.assoc, hk, pullback.condition])

@[reassoc (attr := simp)]
lemma liftTest_fst ⦃W : C⦄ (w : W ⟶ S) (k : W ⟶ X) (hk : k ≫ f = w) (i : ι) :
    liftTest u w k hk i ≫ pullback.fst f (u i) = pullback.fst w (u i) ≫ k := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma liftTest_snd ⦃W : C⦄ (w : W ⟶ S) (k : W ⟶ X) (hk : k ≫ f = w) (i : ι) :
    liftTest u w k hk i ≫ pullback.snd f (u i) = pullback.snd w (u i) := pullback.lift_snd _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
theorem compareIso_comm
    (hW : ∀ ⦃W : C⦄ (w : W ⟶ S), (F.toDescentData (fun i => pullback.fst w (u i))).FullyFaithful)
    ⦃W : C⦄ (w : W ⟶ S) (k₁ k₂ : W ⟶ X) (hk₁ : k₁ ≫ f = w) (hk₂ : k₂ ≫ f = w) :
    (F.map k₁.op.toLoc).toFunctor.map (compareIso F u D L₀ Ψloc hX hΨ).hom ≫
        D.hom w k₁ k₂ (i₁ := ()) (i₂ := ()) hk₁ hk₂ =
      ((F.toDescentData (fun _ : Unit => f)).obj L₀).hom w (i₁ := ()) (i₂ := ()) k₁ k₂ hk₁ hk₂ ≫
        (F.map k₂.op.toLoc).toFunctor.map (compareIso F u D L₀ Ψloc hX hΨ).hom := by
  apply (hW w).map_injective
  ext i

  have hm₁ : pullback.fst w (u i) ≫ k₁ = liftTest u w k₁ hk₁ i ≫ pullback.fst f (u i) :=
      (liftTest_fst u w k₁ hk₁ i).symm
  have hm₂ : pullback.fst w (u i) ≫ k₂ = liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i) :=
      (liftTest_fst u w k₂ hk₂ i).symm
  have hw' : pullback.fst w (u i) ≫ w = pullback.snd w (u i) ≫ u i := pullback.condition
  simp only [comp_hom, toDescentData_map_hom, toDescentData_obj]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj]
  simp only [Functor.map_comp]
  rw [LocallyDiscreteOpToCat.map_eq_pullHom (D.hom w k₁ k₂ hk₁ hk₂) (pullback.fst w (u i)) _ _ hm₁
      hm₂,
    D.pullHom_hom (pullback.fst w (u i)) w (pullback.snd w (u i) ≫ u i) hw' k₁ k₂ hk₁ hk₂ _ _ hm₁
        hm₂]
  have e0 := LocallyDiscreteOpToCat.map_eq_pullHom
    ((DescentData.ofObj (f := fun _ : Unit => f) L₀).hom w k₁ k₂ (i₁ := ()) (i₂ := ()) hk₁ hk₂)
    (pullback.fst w (u i)) _ _ hm₁ hm₂
  rw [(DescentData.ofObj (f := fun _ : Unit => f) L₀).pullHom_hom (pullback.fst w (u i)) w
    (pullback.snd w (u i) ≫ u i) hw' k₁ k₂ hk₁ hk₂ _ _ hm₁ hm₂] at e0
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at e0
  rw [e0]
  have e1 := map_map_eq F k₁.op.toLoc (pullback.fst w (u i)).op.toLoc
    (liftTest u w k₁ hk₁ i ≫ pullback.fst f (u i)).op.toLoc (op_toLoc_comp _ _ hm₁) (compareIso F u
        D L₀ Ψloc hX hΨ).hom
  have e2 := map_map_eq F k₂.op.toLoc (pullback.fst w (u i)).op.toLoc
    (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)).op.toLoc (op_toLoc_comp _ _ hm₂) (compareIso F u
        D L₀ Ψloc hX hΨ).hom
  have e3 := map_eq F (pullback.fst f (u i)).op.toLoc (liftTest u w k₁ hk₁ i).op.toLoc
    (liftTest u w k₁ hk₁ i ≫ pullback.fst f (u i)).op.toLoc (op_toLoc_comp _ _ rfl) (compareIso F u
        D L₀ Ψloc hX hΨ).hom
  have e4 := map_eq F (pullback.fst f (u i)).op.toLoc (liftTest u w k₂ hk₂ i).op.toLoc
    (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)).op.toLoc (op_toLoc_comp _ _ rfl) (compareIso F u
        D L₀ Ψloc hX hΨ).hom
  rw [map_compareIso_hom] at e3 e4
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at e1 e2 e3 e4
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj]
  rw [e1, e2]
  rw [e3, e4]
  simp only [Category.assoc]

  have eA := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' k₁.op.toLoc (pullback.fst w
      (u i)).op.toLoc
    (liftTest u w k₁ hk₁ i ≫ pullback.fst f (u i)).op.toLoc (op_toLoc_comp _ _ hm₁)) (D.obj ())
  have eB := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' k₂.op.toLoc (pullback.fst w
      (u i)).op.toLoc
    (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)).op.toLoc (op_toLoc_comp _ _ hm₂))
    ((F.map f.op.toLoc).toFunctor.obj L₀)
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at eA eB
  rw [reassoc_of% eA, reassoc_of% eB]

  have hc := (Ψloc i).hom.comm (pullback.snd w (u i)) (i₁ := ()) (i₂ := ()) (liftTest u w k₁ hk₁ i)
    (liftTest u w k₂ hk₂ i) (liftTest_snd u w k₁ hk₁ i) (liftTest_snd u w k₂ hk₂ i)
  dsimp only [restr, pullFunctor_obj, pullFunctorObj_hom] at hc
  have hq₂ : liftTest u w k₂ hk₂ i ≫ pullback.snd f (u i) = liftTest u w k₁ hk₁ i ≫ pullback.snd f
      (u i) := by
    rw [liftTest_snd, liftTest_snd]
  have hq' : (liftTest u w k₁ hk₁ i ≫ pullback.snd f (u i)) ≫ u i = pullback.snd w (u i) ≫ u i := by
    rw [liftTest_snd]
  have r1 := pullFunctorObjHom_eq (F := F) (f := fun _ : Unit => f) (p := u i)
      (f' := fun _ : Unit => pullback.snd f (u i)) (α := fun j : Unit => j) (p' := fun _ =>
          pullback.fst f (u i))
      (fun _ => pullback.condition) D (liftTest u w k₁ hk₁ i ≫ pullback.snd f (u i)) (j₁ := ())
          (j₂ := ())
      (liftTest u w k₁ hk₁ i)
      (liftTest u w k₂ hk₂ i) (pullback.snd w (u i) ≫ u i) (liftTest u w k₁ hk₁ i ≫ pullback.fst f
          (u i))
      (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)) rfl hq₂ hq' rfl rfl
  have r2 := pullFunctorObjHom_eq (F := F) (f := fun _ : Unit => f) (p := u i)
      (f' := fun _ : Unit => pullback.snd f (u i)) (α := fun j : Unit => j) (p' := fun _ =>
          pullback.fst f (u i))
      (fun _ => pullback.condition) ((F.toDescentData (fun _ : Unit => f)).obj L₀)
      (liftTest u w k₁ hk₁ i ≫ pullback.snd f (u i)) (j₁ := ()) (j₂ := ()) (liftTest u w k₁ hk₁ i)
      (liftTest u w k₂ hk₂ i) (pullback.snd w (u i) ≫ u i) (liftTest u w k₁ hk₁ i ≫ pullback.fst f
          (u i))
      (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)) rfl hq₂ hq' rfl rfl
  rw [r1, r2] at hc
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at hc
  simp only [Category.assoc] at hc

  have eP₂ := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' (pullback.fst f (u i)).op.toLoc
    (liftTest u w k₂ hk₂ i).op.toLoc (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)).op.toLoc
        (op_toLoc_comp _ _ rfl))
    (D.obj ())
  have eP₁ := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' (pullback.fst f (u i)).op.toLoc
    (liftTest u w k₁ hk₁ i).op.toLoc (liftTest u w k₁ hk₁ i ≫ pullback.fst f (u i)).op.toLoc
        (op_toLoc_comp _ _ rfl))
    ((F.map f.op.toLoc).toFunctor.obj L₀)
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at eP₁ eP₂
  have hc2 := congrArg (fun t => t ≫ (F.mapComp' (pullback.fst f (u i)).op.toLoc
    (liftTest u w k₂ hk₂ i).op.toLoc (liftTest u w k₂ hk₂ i ≫ pullback.fst f (u i)).op.toLoc
    (op_toLoc_comp _ _ rfl)).inv.toNatTrans.app (D.obj ())) hc
  beta_reduce at hc2
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at hc2
  simp only [Category.assoc] at hc2
  rw [eP₂, Category.comp_id] at hc2
  rw [reassoc_of% hc2, reassoc_of% eP₁]

noncomputable def comparison
    (hW : ∀ ⦃W : C⦄ (w : W ⟶ S), (F.toDescentData (fun i => pullback.fst w (u i))).FullyFaithful) :
    (F.toDescentData (fun _ : Unit => f)).obj L₀ ≅ D :=
  isoMk (fun j => by cases j; exact compareIso F u D L₀ Ψloc hX hΨ) (fun W w j₁ j₂ k₁ k₂ hk₁ hk₂ =>
      by
    cases j₁; cases j₂; exact compareIso_comm F u D L₀ Ψloc hX hΨ hW w k₁ k₂ hk₁ hk₂)

end compare

section psi

variable {f}
  (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
  (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))),
      P M → P ((F.map g.op.toLoc).toFunctor.obj M))
  (hf : ∀ ⦃Z : C⦄ (z : Z ⟶ S) (M N : F.obj (.mk (op Z))), P M → P N →
    Function.Bijective ((F.toDescentData (fun _ : Unit => pullback.snd f z)).map : (M ⟶ N) → _))
  {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S)
  (D : F.DescentData (fun _ : Unit => f))
  (L : ∀ i, F.obj (.mk (op (U i)))) (hL : ∀ i, P (L i))
  (ψ : ∀ i, (F.toDescentData (fun _ : Unit => pullback.snd f (u i))).obj (L i) ≅ (restr F f
      (u i)).obj D)
  (L₀ : F.obj (.mk (op S))) (e : (F.toDescentData u).obj L₀ ≅ gluedData F P hP hf u D L hL ψ)

noncomputable def psiLoc (i : ι) :
    (restr F f (u i)).obj ((F.toDescentData (fun _ : Unit => f)).obj L₀) ≅ (restr F f (u i)).obj
        D :=
  (toDescentDataRestrIso F f (u i)).app L₀ ≪≫
    (F.toDescentData (fun _ : Unit => pullback.snd f (u i))).mapIso (objIso F e i) ≪≫ ψ i

set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
theorem psiLoc_comm ⦃W : C⦄ (w : W ⟶ X) ⦃i₁ i₂ : ι⦄ (k₁ : W ⟶ pullback f (u i₁)) (k₂ : W ⟶ pullback
    f (u i₂))
    (hk₁ : k₁ ≫ pullback.fst f (u i₁) = w) (hk₂ : k₂ ≫ pullback.fst f (u i₂) = w) :
    (F.map k₁.op.toLoc).toFunctor.map ((psiLoc F P hP hf u D L hL ψ L₀ e i₁).hom.hom ()) ≫
        ((F.toDescentData (fun i => pullback.fst f (u i))).obj (D.obj ())).hom w k₁ k₂ hk₁ hk₂ =
      ((F.toDescentData (fun i => pullback.fst f (u i))).obj
          ((F.map f.op.toLoc).toFunctor.obj L₀)).hom w k₁ k₂ hk₁ hk₂ ≫
        (F.map k₂.op.toLoc).toFunctor.map ((psiLoc F P hP hf u D L hL ψ L₀ e i₂).hom.hom ()) := by

  have h₁ : (k₁ ≫ pullback.snd f (u i₁)) ≫ u i₁ = w ≫ f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk₁]
  have h₂ : (k₂ ≫ pullback.snd f (u i₂)) ≫ u i₂ = w ≫ f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk₂]

  have F1 := e.hom.comm (w ≫ f) (i₁ := i₁) (i₂ := i₂) (k₁ ≫ pullback.snd f (u i₁)) (k₂
      ≫ pullback.snd f (u i₂)) h₁ h₂
  dsimp only [gluedData] at F1
  rw [gluedHom_eq_of_fac F P hP hf u D L hL ψ w k₁ k₂ hk₁ hk₂ h₁ h₂] at F1
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at F1

  have F1' := congrArg (fun t => t ≫ (F.mapComp' (pullback.snd f (u i₂)).op.toLoc k₂.op.toLoc
      (k₂ ≫ pullback.snd f (u i₂)).op.toLoc rfl).hom.toNatTrans.app (L i₂) ≫
      (F.map k₂.op.toLoc).toFunctor.map ((ψ i₂).hom.hom ())) F1
  simp only [Category.assoc] at F1'
  have cP₂ := Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' (pullback.snd f (u i₂)).op.toLoc
      k₂.op.toLoc
      (k₂ ≫ pullback.snd f (u i₂)).op.toLoc rfl) (L i₂)
  have cψ₂ : (F.map k₂.op.toLoc).toFunctor.map ((ψ i₂).inv.hom ()) ≫
      (F.map k₂.op.toLoc).toFunctor.map ((ψ i₂).hom.hom ()) = 𝟙 _ := by
    rw [← Functor.map_comp, ← comp_hom, Iso.inv_hom_id, id_hom, Functor.map_id]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at cP₂ cψ₂ F1'
  rw [reassoc_of% cP₂, cψ₂, Category.comp_id] at F1'

  simp only [psiLoc, Iso.trans_hom, comp_hom, Iso.app_hom, Functor.mapIso_hom,
      toDescentData_map_hom, objIso_hom,
    toDescentData_obj, ofObj_hom, toDescentDataRestrIso, toDescentDataCompPullFunctorIso,
        NatIso.ofComponents_hom_app,
    isoMk_hom_hom, Iso.symm_hom, Iso.app_inv, Cat.Hom.toNatIso_hom]
  try rw [F.isoMapOfCommSq_eq _ ((pullback.snd f (u i₁) ≫ u i₁).op.toLoc) rfl,
    F.isoMapOfCommSq_eq _ ((pullback.snd f (u i₂) ≫ u i₂).op.toLoc) rfl]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Cat.Hom₂.comp_app,
      Cat.Hom.toNatIso_hom,
    Cat.Hom.toNatIso_inv]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]

  have me₁ := map_map_eq F (pullback.snd f (u i₁)).op.toLoc k₁.op.toLoc (k₁ ≫ pullback.snd f
      (u i₁)).op.toLoc rfl
    (e.hom.hom i₁)
  have me₂ := map_map_eq F (pullback.snd f (u i₂)).op.toLoc k₂.op.toLoc (k₂ ≫ pullback.snd f
      (u i₂)).op.toLoc rfl
    (e.hom.hom i₂)
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at me₁ me₂
  rw [me₁, me₂]
  simp only [Category.assoc]
  try dsimp only [gluedData_obj] at F1' ⊢
  first
    | rw [reassoc_of% F1']
    | rw [F1']
  simp only [ofObj_hom, Category.assoc]

  have Na₁ := F.mapComp'₀₁₃_inv_app (u i₁).op.toLoc (pullback.snd f (u i₁)).op.toLoc k₁.op.toLoc
    (pullback.snd f (u i₁) ≫ u i₁).op.toLoc (k₁ ≫ pullback.snd f (u i₁)).op.toLoc (w ≫ f).op.toLoc
    (op_toLoc_comp _ _ rfl) rfl (op_toLoc_comp _ _ h₁) L₀
  have Nb₁ := F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app f.op.toLoc (pullback.fst f
      (u i₁)).op.toLoc k₁.op.toLoc
    (pullback.snd f (u i₁) ≫ u i₁).op.toLoc w.op.toLoc (w ≫ f).op.toLoc (op_toLoc_comp _ _
        pullback.condition)
    (op_toLoc_comp _ _ hk₁) (op_toLoc_comp _ _ (by rw [← Category.assoc]; exact h₁)) L₀
  have Na₂ := F.mapComp'₀₁₃_hom_app (u i₂).op.toLoc (pullback.snd f (u i₂)).op.toLoc k₂.op.toLoc
    (pullback.snd f (u i₂) ≫ u i₂).op.toLoc (k₂ ≫ pullback.snd f (u i₂)).op.toLoc (w ≫ f).op.toLoc
    (op_toLoc_comp _ _ rfl) rfl (op_toLoc_comp _ _ h₂) L₀
  have Nb₂ := F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app f.op.toLoc (pullback.fst f
      (u i₂)).op.toLoc k₂.op.toLoc
    (pullback.snd f (u i₂) ≫ u i₂).op.toLoc w.op.toLoc (w ≫ f).op.toLoc (op_toLoc_comp _ _
        pullback.condition)
    (op_toLoc_comp _ _ hk₂) (op_toLoc_comp _ _ (by rw [← Category.assoc]; exact h₂)) L₀
  have cU₁ : (F.map k₁.op.toLoc).toFunctor.map ((F.mapComp' (u i₁).op.toLoc (pullback.snd f
      (u i₁)).op.toLoc
      (pullback.snd f (u i₁) ≫ u i₁).op.toLoc (op_toLoc_comp _ _ rfl)).hom.toNatTrans.app L₀) ≫
      (F.map k₁.op.toLoc).toFunctor.map ((F.mapComp' (u i₁).op.toLoc (pullback.snd f
          (u i₁)).op.toLoc
      (pullback.snd f (u i₁) ≫ u i₁).op.toLoc (op_toLoc_comp _ _ rfl)).inv.toNatTrans.app L₀)
          = 𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.hom_inv_id_toNatTrans_app, Functor.map_id]
  have cP₁ := Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' (pullback.snd f (u i₁)).op.toLoc
      k₁.op.toLoc
      (k₁ ≫ pullback.snd f (u i₁)).op.toLoc rfl) ((F.map (u i₁).op.toLoc).toFunctor.obj L₀)

  have cC₂ := Cat.Hom.inv_hom_id_toNatTrans_app (F.mapComp' (pullback.snd f (u i₂) ≫ u i₂).op.toLoc
      k₂.op.toLoc
      (w ≫ f).op.toLoc (op_toLoc_comp _ _ (by rw [← Category.assoc]; exact h₂))) L₀
  have cW₂ := Cat.Hom.hom_inv_id_toNatTrans_app (F.mapComp' (pullback.fst f (u i₂)).op.toLoc
      k₂.op.toLoc
      w.op.toLoc (op_toLoc_comp _ _ hk₂)) ((F.map f.op.toLoc).toFunctor.obj L₀)
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at Na₁ Nb₁ Na₂ Nb₂ cU₁ cP₁ cC₂ cW₂
  have hZ : (F.mapComp' f.op.toLoc w.op.toLoc (w ≫ f).op.toLoc (op_toLoc_comp _ _
      rfl)).inv.toNatTrans.app L₀ =
      (F.mapComp' (pullback.fst f (u i₂)).op.toLoc k₂.op.toLoc w.op.toLoc (op_toLoc_comp _ _
          hk₂)).hom.toNatTrans.app
        ((F.map f.op.toLoc).toFunctor.obj L₀) ≫
      (F.map k₂.op.toLoc).toFunctor.map ((F.mapComp' f.op.toLoc (pullback.fst f (u i₂)).op.toLoc
        (pullback.snd f (u i₂) ≫ u i₂).op.toLoc (op_toLoc_comp _ _
            pullback.condition)).inv.toNatTrans.app L₀) ≫
      (F.mapComp' (pullback.snd f (u i₂) ≫ u i₂).op.toLoc k₂.op.toLoc (w ≫ f).op.toLoc
        (op_toLoc_comp _ _ (by rw [← Category.assoc]; exact h₂))).inv.toNatTrans.app L₀ := by
    try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
        Cat.Hom.comp_toFunctor,
      Functor.comp_obj]
    rw [Nb₂, reassoc_of% cW₂]
  try dsimp only [restr, toDescentData_obj, ofObj_obj, pullFunctor_obj, pullFunctorObj_obj,
      Cat.Hom.comp_toFunctor,
    Functor.comp_obj] at hZ
  rw [Na₁]
  try simp only [Category.assoc]
  rw [reassoc_of% cP₁, reassoc_of% cU₁, reassoc_of% Nb₁]
  rw [Na₂]
  try simp only [Category.assoc]
  rw [hZ]
  try simp only [Category.assoc]
  rw [reassoc_of% cC₂]

end psi

theorem exists_iso_toDescentData_obj
    (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
    (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))),
        P M → P ((F.map g.op.toLoc).toFunctor.obj M))
    (hP' : ∀ ⦃Z : C⦄ (M N : F.obj (.mk (op Z))), Nonempty (M ≅ N) → P M → P N)
    {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S)
    (hS : F.IsStackFor (Presieve.ofArrows U u))
    (hZ : ∀ ⦃Z : C⦄ (z : Z ⟶ S),
      F.IsPrestackFor (Presieve.ofArrows (fun i => pullback z (u i)) (fun i => pullback.fst z
          (u i))))
    (hf : ∀ ⦃Z : C⦄ (z : Z ⟶ S) (M N : F.obj (.mk (op Z))), P M → P N →
      Function.Bijective ((F.toDescentData (fun _ : Unit => pullback.snd f z)).map : (M ⟶ N) → _))
    (D : F.DescentData (fun _ : Unit => f))
    (hD : ∀ i, ∃ L : F.obj (.mk (op (U i))), P L ∧
      Nonempty ((F.toDescentData (fun _ : Unit => pullback.snd f (u i))).obj L ≅ (restr F f
          (u i)).obj D)) :
    ∃ L : F.obj (.mk (op S)), (∀ i, P ((F.map (u i).op.toLoc).toFunctor.obj L)) ∧
      Nonempty ((F.toDescentData (fun _ : Unit => f)).obj L ≅ D) := by
  choose L hL ψ using hD
  replace ψ := fun i => (ψ i).some

  let E : F.DescentData u := gluedData F P hP hf u D L hL ψ
  haveI := (F.isStackFor_ofArrows_iff u).1 hS
  let L₀ : F.obj (.mk (op S)) := (F.toDescentData u).objPreimage E
  let e : (F.toDescentData u).obj L₀ ≅ E := (F.toDescentData u).objObjPreimageIso E
  have hL₀ : ∀ i, P ((F.map (u i).op.toLoc).toFunctor.obj L₀) := fun i =>
    hP' _ _ ⟨(objIso F e i).symm⟩ (hL i)

  let Ψloc : ∀ i, (restr F f (u i)).obj ((F.toDescentData (fun _ : Unit => f)).obj L₀) ≅
      (restr F f (u i)).obj D := psiLoc F P hP hf u D L hL ψ L₀ e
  have hΨ := psiLoc_comm F P hP hf u D L hL ψ L₀ e

  have hX := ((F.isPrestackFor_ofArrows_iff (fun i => pullback.fst f (u i))).1 (hZ f)).some
  have hW : ∀ ⦃W : C⦄ (w : W ⟶ S), (F.toDescentData (fun i => pullback.fst w
      (u i))).FullyFaithful :=
    fun W w => ((F.isPrestackFor_ofArrows_iff (fun i => pullback.fst w (u i))).1 (hZ w)).some
  exact ⟨L₀, hL₀, ⟨comparison F u D L₀ Ψloc hX hΨ hW⟩⟩

end CategoryTheory.Pseudofunctor.DescentData.LocalEffectivity

@[expose] public section

namespace CategoryTheory.Pseudofunctor.DescentData

/-- Local effectivity of descent data over a stack: if `F` is a stack for the covering `u` of
`S`, the pullbacks of the covering are prestack coverings, descent along `f` is fully faithful
on objects satisfying `P`, and a descent datum `D` along `f` is effective after pulling back
to each `U i` by objects satisfying `P`, then `D` is effective, by an object whose pullbacks
satisfy `P`. -/
theorem exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
    (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))),
        P M → P ((F.map g.op.toLoc).toFunctor.obj M))
    (hP' : ∀ ⦃Z : C⦄ (M N : F.obj (.mk (op Z))), Nonempty (M ≅ N) → P M → P N)
    {S X : C} (f : X ⟶ S) {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S)
    (hS : F.IsStackFor (Presieve.ofArrows U u))
    (hZ : ∀ ⦃Z : C⦄ (z : Z ⟶ S),
      F.IsPrestackFor (Presieve.ofArrows (fun i => pullback z (u i)) (fun i => pullback.fst z
          (u i))))
    (hf : ∀ ⦃Z : C⦄ (z : Z ⟶ S) (M N : F.obj (.mk (op Z))), P M → P N →
      Function.Bijective ((F.toDescentData (fun _ : Unit => pullback.snd f z)).map : (M ⟶ N) → _))
    (D : F.DescentData (fun _ : Unit => f))
    (hD : ∀ i, ∃ L : F.obj (.mk (op (U i))), P L ∧
      Nonempty ((F.toDescentData (fun _ : Unit => pullback.snd f (u i))).obj L ≅
        (Pseudofunctor.DescentData.pullFunctor F (f := fun _ : Unit => f) (p := u i)
          (f' := fun _ : Unit => pullback.snd f (u i)) (α := fun j => j) (p' := fun _ =>
              pullback.fst f (u i))
          (fun _ => pullback.condition)).obj D)) :
    ∃ L : F.obj (.mk (op S)), (∀ i, P ((F.map (u i).op.toLoc).toFunctor.obj L)) ∧
      Nonempty ((F.toDescentData (fun _ : Unit => f)).obj L ≅ D) :=
  CategoryTheory.Pseudofunctor.DescentData.LocalEffectivity.exists_iso_toDescentData_obj F f P hP
      hP' u hS hZ hf D hD

end CategoryTheory.Pseudofunctor.DescentData
