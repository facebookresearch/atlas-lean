/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# Maps from the fundamental groupoid into a groupoid

Functors from the fundamental groupoid of a simplicial set to a small
groupoid are equivalent to simplicial maps into its nerve.  The inverse is
the direct edge-generated descent from `FundamentalGroupoid.desc`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Nerve SimplicialObject.Truncated
  SimplexCategory.Truncated Opposite Limits
open scoped Simplicial

universe u

namespace SSet

private theorem fundamentalGroupoidRestrict_map_id
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G) (x) :
    F.map (SSet.Truncated.FundamentalGroupoid.homMk
        (SSet.Truncated.Edge.id x)) = 𝟙 _ := by
  rw [SSet.Truncated.FundamentalGroupoid.homMk_id, F.map_id]

private theorem fundamentalGroupoidRestrict_map_comp
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G)
    {x y z} {e₁ : SSet.Truncated.Edge x y}
    {e₂ : SSet.Truncated.Edge y z}
    {e₃ : SSet.Truncated.Edge x z}
    (h : SSet.Truncated.Edge.CompStruct e₁ e₂ e₃) :
    F.map (SSet.Truncated.FundamentalGroupoid.homMk e₁) ≫
        F.map (SSet.Truncated.FundamentalGroupoid.homMk e₂) =
      F.map (SSet.Truncated.FundamentalGroupoid.homMk e₃) := by
  rw [← F.map_comp, h.homMk_comp]

private def fundamentalGroupoidRestrict
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G) :
    SSet.HomotopyCategory X ⥤ G :=
  SSet.Truncated.HomotopyCategory.lift
    (fun x => F.obj (SSet.Truncated.FundamentalGroupoid.mk x))
    (fun e => F.map (SSet.Truncated.FundamentalGroupoid.homMk e))
    (fundamentalGroupoidRestrict_map_id X G F)
    (fundamentalGroupoidRestrict_map_comp X G F)

private theorem fundamentalGroupoidRestrict_map_homMk
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G)
    {x y} (e : SSet.Truncated.Edge x y) :
    (fundamentalGroupoidRestrict X G F).map
        (SSet.Truncated.HomotopyCategory.homMk e) =
      F.map (SSet.Truncated.FundamentalGroupoid.homMk e) :=
  SSet.Truncated.HomotopyCategory.lift_map_homMk _ _
    (fundamentalGroupoidRestrict_map_id X G F)
    (fundamentalGroupoidRestrict_map_comp X G F) e

private theorem fundamentalGroupoidExtend_map_comp
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.HomotopyCategory X ⥤ G)
    {x y z} {e₁ : SSet.Truncated.Edge x y}
    {e₂ : SSet.Truncated.Edge y z}
    {e₃ : SSet.Truncated.Edge x z}
    (h : SSet.Truncated.Edge.CompStruct e₁ e₂ e₃) :
    F.map (SSet.Truncated.HomotopyCategory.homMk e₁) ≫
        F.map (SSet.Truncated.HomotopyCategory.homMk e₂) =
      F.map (SSet.Truncated.HomotopyCategory.homMk e₃) := by
  rw [← F.map_comp,
    SSet.Truncated.HomotopyCategory.homMk_comp_homMk h]

private def fundamentalGroupoidExtend
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.HomotopyCategory X ⥤ G) :
    SSet.FundamentalGroupoid X ⥤ G :=
  SSet.Truncated.FundamentalGroupoid.desc
    (fun x => F.obj (SSet.Truncated.HomotopyCategory.mk x))
    (fun e => F.map (SSet.Truncated.HomotopyCategory.homMk e))
    (fundamentalGroupoidExtend_map_comp X G F)

private theorem fundamentalGroupoidExtend_map_homMk
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.HomotopyCategory X ⥤ G)
    {x y} (e : SSet.Truncated.Edge x y) :
    (fundamentalGroupoidExtend X G F).map
        (SSet.Truncated.FundamentalGroupoid.homMk e) =
      F.map (SSet.Truncated.HomotopyCategory.homMk e) :=
  SSet.Truncated.FundamentalGroupoid.desc_map_homMk _ _
    (fundamentalGroupoidExtend_map_comp X G F) e

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidExtend_obj_mk
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.HomotopyCategory X ⥤ G) (x : X _⦋0⦌) :
    (fundamentalGroupoidExtend X G F).obj
        (SSet.FundamentalGroupoid.mk x) =
      F.obj (SSet.HomotopyCategory.mk x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidExtend_map_homMk_full
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.HomotopyCategory X ⥤ G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (fundamentalGroupoidExtend X G F).map
        (SSet.FundamentalGroupoid.homMk e) =
      F.map (SSet.HomotopyCategory.homMk e) := by
  exact fundamentalGroupoidExtend_map_homMk X G F e.toTruncated

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidExtend_restrict
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G) :
    fundamentalGroupoidExtend X G
        (fundamentalGroupoidRestrict X G F) = F := by
  let hobj : ∀ x, (fundamentalGroupoidExtend X G
      (fundamentalGroupoidRestrict X G F)).obj
        (SSet.Truncated.FundamentalGroupoid.mk x) =
      F.obj (SSet.Truncated.FundamentalGroupoid.mk x) := fun _ => rfl
  refine SSet.Truncated.FundamentalGroupoid.functor_ext hobj ?_
  intro x y e
  simpa [hobj] using
    (fundamentalGroupoidExtend_map_homMk X G
      (fundamentalGroupoidRestrict X G F) e).trans
        (fundamentalGroupoidRestrict_map_homMk X G F e)

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidRestrict_extend
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.HomotopyCategory X ⥤ G) :
    fundamentalGroupoidRestrict X G
        (fundamentalGroupoidExtend X G F) = F := by
  let hobj : ∀ x, (fundamentalGroupoidRestrict X G
      (fundamentalGroupoidExtend X G F)).obj
        (SSet.Truncated.HomotopyCategory.mk x) =
      F.obj (SSet.Truncated.HomotopyCategory.mk x) := fun _ => rfl
  refine SSet.Truncated.HomotopyCategory.functor_ext hobj ?_
  intro x y e
  simpa [hobj] using
    (fundamentalGroupoidRestrict_map_homMk X G
      (fundamentalGroupoidExtend X G F) e).trans
        (fundamentalGroupoidExtend_map_homMk X G F e)

private noncomputable def fundamentalGroupoidRestrictionEquiv
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G] :
    (SSet.FundamentalGroupoid X ⥤ G) ≃
      (SSet.HomotopyCategory X ⥤ G) where
  toFun := fundamentalGroupoidRestrict X G
  invFun := fundamentalGroupoidExtend X G
  left_inv := fundamentalGroupoidExtend_restrict X G
  right_inv := fundamentalGroupoidRestrict_extend X G

private noncomputable def nerveTruncHomEquiv
    (X : SSet.{u}) (G : Type u) [SmallCategory G] :
    (X ⟶ CategoryTheory.nerve G) ≃
      ((SSet.truncation 2).obj X ⟶
        (SSet.truncation 2).obj (CategoryTheory.nerve G)) :=
  ((CategoryTheory.Nerve.cosk₂Iso.app ↧G).homToEquiv).trans
    ((SSet.coskAdj 2).homEquiv X
      ((SSet.truncation 2).obj (CategoryTheory.nerve G))).symm

@[simp]
private theorem nerveTruncHomEquiv_apply
    (X : SSet.{u}) (G : Type u) [SmallCategory G]
    (φ : X ⟶ CategoryTheory.nerve G) :
    nerveTruncHomEquiv X G φ = (SSet.truncation 2).map φ := by
  change (SSet.truncation 2).map
      (φ ≫ (SSet.coskAdj 2).unit.app (CategoryTheory.nerve G)) ≫
        (SSet.coskAdj 2).counit.app
          ((SSet.truncation 2).obj (CategoryTheory.nerve G)) =
    (SSet.truncation 2).map φ
  rw [Functor.map_comp, Category.assoc,
    (SSet.coskAdj 2).left_triangle_components, Category.comp_id]

@[simp]
private theorem homotopyCategoryNerveInv_obj
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) (x : X _⦋0⦌) :
    (SSet.Truncated.HomotopyCategory.functorEquiv.symm
      ((SSet.truncation 2).map φ)).obj
        (SSet.HomotopyCategory.mk x) =
      CategoryTheory.nerveEquiv (φ.app _ x) := by
  change (SSet.Truncated.HomotopyCategory.descOfTruncation
    ((SSet.truncation 2).map φ)).obj (SSet.HomotopyCategory.mk x) = _
  rfl

@[simp]
private theorem homotopyCategoryNerveInv_map
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (SSet.Truncated.HomotopyCategory.functorEquiv.symm
      ((SSet.truncation 2).map φ)).map
        (SSet.HomotopyCategory.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map φ) := by
  change (SSet.Truncated.HomotopyCategory.descOfTruncation
    ((SSet.truncation 2).map φ)).map
      (SSet.HomotopyCategory.homMk e) = _
  exact SSet.Truncated.HomotopyCategory.descOfTruncation_map_homMk
    _ e.toTruncated

private noncomputable def fundamentalGroupoidNerveAuxEquiv
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G] :
    (SSet.FundamentalGroupoid X ⥤ G) ≃
      (X ⟶ CategoryTheory.nerve G) :=
  ((fundamentalGroupoidRestrictionEquiv X G).trans
    SSet.Truncated.HomotopyCategory.functorEquiv).trans
      (nerveTruncHomEquiv X G).symm

private noncomputable def fundamentalGroupoidNerveDesc
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) :
    SSet.FundamentalGroupoid X ⥤ G :=
  SSet.FundamentalGroupoid.desc
    (fun x => CategoryTheory.nerveEquiv (φ.app _ x))
    (fun e => CategoryTheory.nerve.homEquiv (e.map φ))
    (fun h => CategoryTheory.nerve.homEquiv_comp (h.map φ))

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidNerveDesc_obj_mk
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) (x : X _⦋0⦌) :
    (fundamentalGroupoidNerveDesc φ).obj
        (SSet.FundamentalGroupoid.mk x) =
      CategoryTheory.nerveEquiv (φ.app _ x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidNerveDesc_map_homMk
    {X : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (fundamentalGroupoidNerveDesc φ).map
        (SSet.FundamentalGroupoid.homMk e) =
      CategoryTheory.nerve.homEquiv (e.map φ) :=
  SSet.FundamentalGroupoid.desc_map_homMk
    (fun x => CategoryTheory.nerveEquiv (φ.app _ x))
    (fun e => CategoryTheory.nerve.homEquiv (e.map φ))
    (fun h => CategoryTheory.nerve.homEquiv_comp (h.map φ)) e

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidNerveAuxEquiv_symm_eq_desc
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) :
    (fundamentalGroupoidNerveAuxEquiv X G).symm φ =
      fundamentalGroupoidNerveDesc φ := by
  change fundamentalGroupoidExtend X G
      (SSet.Truncated.HomotopyCategory.functorEquiv.symm
        (nerveTruncHomEquiv X G φ)) =
    fundamentalGroupoidNerveDesc φ
  rw [nerveTruncHomEquiv_apply]
  let hobj : ∀ x,
      (fundamentalGroupoidExtend X G
        (SSet.Truncated.HomotopyCategory.functorEquiv.symm
          ((SSet.truncation 2).map φ))).obj
          (SSet.FundamentalGroupoid.mk x) =
        (fundamentalGroupoidNerveDesc φ).obj
          (SSet.FundamentalGroupoid.mk x) := fun x => by
    rw [fundamentalGroupoidExtend_obj_mk,
      homotopyCategoryNerveInv_obj,
      fundamentalGroupoidNerveDesc_obj_mk]
  refine SSet.FundamentalGroupoid.functor_ext hobj ?_
  intro x y e
  have h := fundamentalGroupoidExtend_map_homMk_full X G
    (SSet.Truncated.HomotopyCategory.functorEquiv.symm
      ((SSet.truncation 2).map φ)) e
  rw [homotopyCategoryNerveInv_map] at h
  rw [h, ← fundamentalGroupoidNerveDesc_map_homMk φ e]
  cat_disch

/-- Functors from the simplicial fundamental groupoid to a small groupoid
are equivalent to simplicial maps into its nerve. -/
@[no_expose]
noncomputable def fundamentalGroupoidNerveEquiv
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G] :
    (SSet.FundamentalGroupoid X ⥤ G) ≃
      (X ⟶ CategoryTheory.nerve G) where
  toFun := fundamentalGroupoidNerveAuxEquiv X G
  invFun := fundamentalGroupoidNerveDesc
  left_inv F := by
    rw [← fundamentalGroupoidNerveAuxEquiv_symm_eq_desc X G]
    exact (fundamentalGroupoidNerveAuxEquiv X G).left_inv F
  right_inv φ := by
    rw [← fundamentalGroupoidNerveAuxEquiv_symm_eq_desc X G]
    exact (fundamentalGroupoidNerveAuxEquiv X G).apply_symm_apply φ

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidNerveEquiv_symm_eq_desc
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) :
    (fundamentalGroupoidNerveEquiv X G).symm φ =
      fundamentalGroupoidNerveDesc φ := by
  apply (fundamentalGroupoidNerveEquiv X G).injective
  rw [(fundamentalGroupoidNerveEquiv X G).apply_symm_apply]
  symm
  change fundamentalGroupoidNerveAuxEquiv X G
      (fundamentalGroupoidNerveDesc φ) = φ
  rw [← fundamentalGroupoidNerveAuxEquiv_symm_eq_desc X G φ]
  exact (fundamentalGroupoidNerveAuxEquiv X G).apply_symm_apply φ

@[simp]
theorem fundamentalGroupoidNerveEquiv_symm_obj_mk
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G) (x : X _⦋0⦌) :
    ((fundamentalGroupoidNerveEquiv X G).symm φ).obj
        (SSet.FundamentalGroupoid.mk x) =
      CategoryTheory.nerveEquiv (φ.app _ x) := by
  rw [fundamentalGroupoidNerveEquiv_symm_eq_desc,
    fundamentalGroupoidNerveDesc_obj_mk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem fundamentalGroupoidNerveEquiv_symm_map_homMk
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (φ : X ⟶ CategoryTheory.nerve G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    ((fundamentalGroupoidNerveEquiv X G).symm φ).map
        (SSet.FundamentalGroupoid.homMk e) =
      eqToHom
          (fundamentalGroupoidNerveEquiv_symm_obj_mk X G φ x) ≫
        CategoryTheory.nerve.homEquiv (e.map φ) ≫
      eqToHom
        (fundamentalGroupoidNerveEquiv_symm_obj_mk X G φ y).symm := by
  have h := CategoryTheory.Functor.congr_hom
    (fundamentalGroupoidNerveEquiv_symm_eq_desc X G φ)
    (SSet.FundamentalGroupoid.homMk e)
  rw [fundamentalGroupoidNerveDesc_map_homMk] at h
  convert h using 1

@[simp]
theorem fundamentalGroupoidNerveEquiv_app_zero
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G) (x : X _⦋0⦌) :
    (fundamentalGroupoidNerveEquiv X G F).app _ x =
      CategoryTheory.nerveEquiv.symm
        (F.obj (SSet.FundamentalGroupoid.mk x)) := by
  have h := congrArg
    (fun K => K.obj (SSet.FundamentalGroupoid.mk x))
    ((fundamentalGroupoidNerveEquiv X G).left_inv F)
  have hs := CategoryTheory.Functor.congr_obj
    (fundamentalGroupoidNerveEquiv_symm_eq_desc X G
      (fundamentalGroupoidNerveEquiv X G F))
    (SSet.FundamentalGroupoid.mk x)
  rw [fundamentalGroupoidNerveDesc_obj_mk] at hs
  have hx := hs.symm.trans h
  apply CategoryTheory.nerveEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact hx

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem fundamentalGroupoidNerveEquiv_app_edge
    (X : SSet.{u}) (G : Type u) [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid X ⥤ G)
    {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (fundamentalGroupoidNerveEquiv X G F).app _ e.edge =
      ComposableArrows.mk₁
        (F.map (SSet.FundamentalGroupoid.homMk e)) := by
  let φ := fundamentalGroupoidNerveEquiv X G F
  let hfun := (fundamentalGroupoidNerveEquiv X G).left_inv F
  let hleft : (φ.app _ e.edge).left =
      F.obj (SSet.FundamentalGroupoid.mk x) := by
    calc
      (φ.app _ e.edge).left =
          CategoryTheory.nerveEquiv (φ.app _ x) :=
        CategoryTheory.nerve.left_edge (e.map φ)
      _ = F.obj (SSet.FundamentalGroupoid.mk x) := by
        rw [fundamentalGroupoidNerveEquiv_app_zero,
          Equiv.apply_symm_apply]
  let hright : (φ.app _ e.edge).right =
      F.obj (SSet.FundamentalGroupoid.mk y) := by
    calc
      (φ.app _ e.edge).right =
          CategoryTheory.nerveEquiv (φ.app _ y) :=
        CategoryTheory.nerve.right_edge (e.map φ)
      _ = F.obj (SSet.FundamentalGroupoid.mk y) := by
        rw [fundamentalGroupoidNerveEquiv_app_zero,
          Equiv.apply_symm_apply]
  refine ComposableArrows.ext₁ hleft hright ?_
  change (φ.app _ e.edge).hom =
    eqToHom hleft ≫ F.map (SSet.FundamentalGroupoid.homMk e) ≫
      eqToHom hright.symm
  have h := CategoryTheory.Functor.congr_hom hfun
    (SSet.FundamentalGroupoid.homMk e)
  let hsfun := fundamentalGroupoidNerveEquiv_symm_eq_desc X G φ
  have hs := CategoryTheory.Functor.congr_hom hsfun
    (SSet.FundamentalGroupoid.homMk e)
  rw [fundamentalGroupoidNerveDesc_map_homMk] at hs
  dsimp [CategoryTheory.nerve.homEquiv] at hs
  let hx : ((fundamentalGroupoidNerveEquiv X G).symm φ).obj
      (SSet.FundamentalGroupoid.mk x) = (φ.app _ e.edge).left :=
    (CategoryTheory.Functor.congr_obj hsfun
      (SSet.FundamentalGroupoid.mk x)).trans
        ((fundamentalGroupoidNerveDesc_obj_mk φ x).trans
          (CategoryTheory.nerve.left_edge (e.map φ)).symm)
  let hx' : (φ.app _ e.edge).left =
      ((fundamentalGroupoidNerveEquiv X G).symm φ).obj
        (SSet.FundamentalGroupoid.mk x) :=
    (CategoryTheory.nerve.left_edge (e.map φ)).trans
      ((fundamentalGroupoidNerveDesc_obj_mk φ x).symm.trans
        (CategoryTheory.Functor.congr_obj hsfun
          (SSet.FundamentalGroupoid.mk x)).symm)
  let hy : ((fundamentalGroupoidNerveEquiv X G).symm φ).obj
      (SSet.FundamentalGroupoid.mk y) = (φ.app _ e.edge).right :=
    (CategoryTheory.Functor.congr_obj hsfun
      (SSet.FundamentalGroupoid.mk y)).trans
        ((fundamentalGroupoidNerveDesc_obj_mk φ y).trans
          (CategoryTheory.nerve.right_edge (e.map φ)).symm)
  let hy' : (φ.app _ e.edge).right =
      ((fundamentalGroupoidNerveEquiv X G).symm φ).obj
        (SSet.FundamentalGroupoid.mk y) :=
    (CategoryTheory.nerve.right_edge (e.map φ)).trans
      ((fundamentalGroupoidNerveDesc_obj_mk φ y).symm.trans
        (CategoryTheory.Functor.congr_obj hsfun
          (SSet.FundamentalGroupoid.mk y)).symm)
  have hx_hom : eqToHom hx =
      eqToHom (CategoryTheory.nerve.left_edge (e.map φ)).symm := by
    congr 1
  have hy_hom : eqToHom hy' =
      eqToHom (CategoryTheory.nerve.right_edge (e.map φ)) := by
    congr 1
  have hs' : ((fundamentalGroupoidNerveEquiv X G).symm φ).map
        (SSet.FundamentalGroupoid.homMk e) =
      eqToHom hx ≫ (φ.app _ e.edge).hom ≫ eqToHom hy' := by
    rw [hx_hom, hy_hom]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using hs
  have hh := hs'.symm.trans h
  let hfx := CategoryTheory.Functor.congr_obj hfun
    (SSet.FundamentalGroupoid.mk x)
  let hfy := CategoryTheory.Functor.congr_obj hfun
    (SSet.FundamentalGroupoid.mk y)
  have hleft_eq : hleft = hx'.trans hfx := Subsingleton.elim _ _
  have hright_eq : hright.symm =
      hfy.symm.trans hy :=
    Subsingleton.elim _ _
  have hx_toF : eqToHom hx ≫ eqToHom (hx'.trans hfx) =
      eqToHom hfx := by
    rw [eqToHom_trans]
  have hy_fromF : eqToHom (hfy.symm.trans hy) ≫ eqToHom hy' =
      eqToHom hfy.symm := by
    rw [eqToHom_trans]
  rw [hleft_eq, hright_eq]
  rw [← cancel_epi (eqToHom hx)]
  rw [← cancel_mono (eqToHom hy')]
  simp only [Category.assoc]
  apply hh.trans
  rw [← hx_toF, ← hy_fromF]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidNerveDesc_precomp
    {X Y : SSet.{u}} {G : Type u} [Groupoid.{u} G]
    (i : X ⟶ Y) (φ : Y ⟶ CategoryTheory.nerve G) :
    fundamentalGroupoidNerveDesc (i ≫ φ) =
      SSet.mapFundamentalGroupoid i ⋙
        fundamentalGroupoidNerveDesc φ := by
  refine SSet.FundamentalGroupoid.functor_ext (fun x => rfl) ?_
  intro x y e
  simp only [fundamentalGroupoidNerveDesc_map_homMk,
    Functor.comp_map, SSet.mapFundamentalGroupoid_map_homMk]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
private theorem nerveHomEquiv_map_nerveMap
    {G H : Type u} [Groupoid.{u} G] [Groupoid.{u} H]
    (Q : G ⥤ H) {x y : (CategoryTheory.nerve G) _⦋0⦌}
    (e : (CategoryTheory.nerve G).Edge x y) :
    CategoryTheory.nerve.homEquiv
        (e.map (CategoryTheory.nerveMap Q)) =
      Q.map (CategoryTheory.nerve.homEquiv e) := by
  obtain ⟨x, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective y
  obtain ⟨f, rfl⟩ := CategoryTheory.nerve.edgeMk_surjective e
  have h := CategoryTheory.nerve.homEquiv_edgeMk_map_nerveMap f Q
  rw [CategoryTheory.nerve.homEquiv_edgeMk]
  convert h using 1

set_option backward.isDefEq.respectTransparency false in
private theorem fundamentalGroupoidNerveDesc_postcomp
    {X : SSet.{u}} {G H : Type u}
    [Groupoid.{u} G] [Groupoid.{u} H]
    (φ : X ⟶ CategoryTheory.nerve G) (Q : G ⥤ H) :
    fundamentalGroupoidNerveDesc (φ ≫ CategoryTheory.nerveMap Q) =
      fundamentalGroupoidNerveDesc φ ⋙ Q := by
  let hobj : ∀ x,
      (fundamentalGroupoidNerveDesc
        (φ ≫ CategoryTheory.nerveMap Q)).obj
          (SSet.FundamentalGroupoid.mk x) =
        (fundamentalGroupoidNerveDesc φ ⋙ Q).obj
          (SSet.FundamentalGroupoid.mk x) := fun x => by
    rw [fundamentalGroupoidNerveDesc_obj_mk]
    change CategoryTheory.nerveEquiv
        ((CategoryTheory.nerveMap Q).app _ (φ.app _ x)) =
      Q.obj (CategoryTheory.nerveEquiv (φ.app _ x))
    obtain ⟨a, ha⟩ := CategoryTheory.nerveEquiv.symm.surjective
      (φ.app _ x)
    rw [← ha]
    have ha : CategoryTheory.nerveEquiv.symm a =
        ComposableArrows.mk₀ a := rfl
    rw [ha]
    rw [CategoryTheory.nerveMap_app_mk₀]
    rfl
  refine SSet.FundamentalGroupoid.functor_ext hobj ?_
  intro x y e
  have he : e.map (φ ≫ CategoryTheory.nerveMap Q) =
      (e.map φ).map (CategoryTheory.nerveMap Q) := rfl
  have hm : CategoryTheory.nerve.homEquiv
      (e.map (φ ≫ CategoryTheory.nerveMap Q)) =
      Q.map (CategoryTheory.nerve.homEquiv (e.map φ)) := by
    rw [he]
    exact nerveHomEquiv_map_nerveMap Q (e.map φ)
  rw [fundamentalGroupoidNerveDesc_map_homMk,
    Functor.comp_map, fundamentalGroupoidNerveDesc_map_homMk]
  cat_disch

/-- Naturality in the simplicial-set argument. -/
theorem fundamentalGroupoidNerveEquiv_precomp
    {X Y : SSet.{u}} (i : X ⟶ Y)
    {G : Type u} [Groupoid.{u} G]
    (F : SSet.FundamentalGroupoid Y ⥤ G) :
    fundamentalGroupoidNerveEquiv X G
        (SSet.mapFundamentalGroupoid i ⋙ F) =
      i ≫ fundamentalGroupoidNerveEquiv Y G F := by
  apply (fundamentalGroupoidNerveEquiv X G).symm.injective
  calc
    (fundamentalGroupoidNerveEquiv X G).symm
        (fundamentalGroupoidNerveEquiv X G
          (SSet.mapFundamentalGroupoid i ⋙ F)) =
        SSet.mapFundamentalGroupoid i ⋙ F :=
      (fundamentalGroupoidNerveEquiv X G).left_inv _
    _ = SSet.mapFundamentalGroupoid i ⋙
        fundamentalGroupoidNerveDesc
          (fundamentalGroupoidNerveEquiv Y G F) := by
      apply congrArg (fun K => SSet.mapFundamentalGroupoid i ⋙ K)
      exact ((fundamentalGroupoidNerveEquiv_symm_eq_desc Y G
        (fundamentalGroupoidNerveEquiv Y G F)).symm.trans
          ((fundamentalGroupoidNerveEquiv Y G).left_inv F)).symm
    _ = fundamentalGroupoidNerveDesc
        (i ≫ fundamentalGroupoidNerveEquiv Y G F) :=
      (fundamentalGroupoidNerveDesc_precomp i _).symm
    _ = (fundamentalGroupoidNerveEquiv X G).symm
        (i ≫ fundamentalGroupoidNerveEquiv Y G F) :=
      (fundamentalGroupoidNerveEquiv_symm_eq_desc X G _).symm

/-- Naturality in the target groupoid. -/
theorem fundamentalGroupoidNerveEquiv_postcomp
    {X : SSet.{u}} {G H : Type u}
    [Groupoid.{u} G] [Groupoid.{u} H]
    (F : SSet.FundamentalGroupoid X ⥤ G) (Q : G ⥤ H) :
    fundamentalGroupoidNerveEquiv X H (F ⋙ Q) =
      fundamentalGroupoidNerveEquiv X G F ≫
        CategoryTheory.nerveMap Q := by
  apply (fundamentalGroupoidNerveEquiv X H).symm.injective
  calc
    (fundamentalGroupoidNerveEquiv X H).symm
        (fundamentalGroupoidNerveEquiv X H (F ⋙ Q)) = F ⋙ Q :=
      (fundamentalGroupoidNerveEquiv X H).left_inv _
    _ = fundamentalGroupoidNerveDesc
          (fundamentalGroupoidNerveEquiv X G F) ⋙ Q := by
      apply congrArg (fun K => K ⋙ Q)
      exact ((fundamentalGroupoidNerveEquiv_symm_eq_desc X G
        (fundamentalGroupoidNerveEquiv X G F)).symm.trans
          ((fundamentalGroupoidNerveEquiv X G).left_inv F)).symm
    _ = fundamentalGroupoidNerveDesc
        (fundamentalGroupoidNerveEquiv X G F ≫
          CategoryTheory.nerveMap Q) :=
      (fundamentalGroupoidNerveDesc_postcomp _ Q).symm
    _ = (fundamentalGroupoidNerveEquiv X H).symm
        (fundamentalGroupoidNerveEquiv X G F ≫
          CategoryTheory.nerveMap Q) :=
      (fundamentalGroupoidNerveEquiv_symm_eq_desc X H _).symm

end SSet

end
