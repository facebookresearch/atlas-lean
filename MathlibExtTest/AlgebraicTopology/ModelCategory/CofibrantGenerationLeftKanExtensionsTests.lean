/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.LeftKanExtensions
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Original comma colimits, pointwise Kan values and native adjunctions -/
set_option autoImplicit false
noncomputable section
universe w uD vD uE vE uM vM
open CategoryTheory Functor Limits HomotopicalAlgebra

namespace MathlibExtTest.CofibrantGenerationLeftKanExtensions

variable {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [LocallySmall.{w} E]
  (dM : CofibrantGenerationData M κ) (u : D ⥤ E)

example (F : D ⥤ M) : u.HasPointwiseLeftKanExtension F :=
  dM.hasPointwiseLeftKanExtension u F

example (F : D ⥤ M) : u.HasLeftKanExtension F :=
  dM.hasLeftKanExtension u F

example (e : E) : EssentiallySmall.{w} (CostructuredArrow u e) := inferInstance

example (e : E) : HasColimitsOfShape (CostructuredArrow u e) M :=
  dM.hasColimitsOfShape

example (F : D ⥤ M) (e : E) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (u.pointwiseLeftKanExtension F).obj e =
      colimit (CostructuredArrow.proj u e ⋙ F) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact rfl

example (F : D ⥤ M) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (u.pointwiseLeftKanExtensionUnit F).app = fun (d : D) =>
      colimit.ι (CostructuredArrow.proj u (u.obj d) ⋙ F)
        (CostructuredArrow.mk (𝟙 (u.obj d))) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact rfl

example (F : D ⥤ M) {e e' : E} (a : e ⟶ e') (j : CostructuredArrow u e) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    colimit.ι (CostructuredArrow.proj u e ⋙ F) j ≫
        (u.pointwiseLeftKanExtension F).map a =
      colimit.ι (CostructuredArrow.proj u e' ⋙ F) ((CostructuredArrow.map a).obj j) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  rw [Functor.pointwiseLeftKanExtension_map]
  exact colimit.ι_desc _ j

example (F : D ⥤ M) (e : E) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (u.pointwiseLeftKanExtension F).map (𝟙 e) =
      𝟙 ((u.pointwiseLeftKanExtension F).obj e) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact (u.pointwiseLeftKanExtension F).map_id e

example (F : D ⥤ M) {e e' e'' : E} (a : e ⟶ e') (b : e' ⟶ e'') :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (u.pointwiseLeftKanExtension F).map (a ≫ b) =
      (u.pointwiseLeftKanExtension F).map a ≫ (u.pointwiseLeftKanExtension F).map b := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact (u.pointwiseLeftKanExtension F).map_comp a b

example (F : D ⥤ M) {d d' : D} (a : d ⟶ d') :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    F.map a ≫ (u.pointwiseLeftKanExtensionUnit F).app d' =
      (u.pointwiseLeftKanExtensionUnit F).app d ≫
        (u.pointwiseLeftKanExtension F).map (u.map a) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact (u.pointwiseLeftKanExtensionUnit F).naturality a

example (F : D ⥤ M) (G : E ⥤ M) (α : F ⟶ u ⋙ G) (e : E)
    (j : CostructuredArrow u e) :
    (costructuredArrowMapCocone u F G α e).ι.app j =
      α.app j.left ≫ G.map j.hom := rfl

example (F : D ⥤ M) (G : E ⥤ M) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (fun (α : F ⟶ u ⋙ G) (e : E) =>
      ((u.pointwiseLeftKanExtension F).descOfIsLeftKanExtension
        (u.pointwiseLeftKanExtensionUnit F) G α).app e) =
      fun (α : F ⟶ u ⋙ G) (e : E) =>
        colimit.desc (CostructuredArrow.proj u e ⋙ F)
          (costructuredArrowMapCocone u F G α e) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  funext α e
  exact pointwiseLeftKanExtension_desc_app u F G α e

example (F : D ⥤ M) (G : E ⥤ M) (α : F ⟶ u ⋙ G) (d : D) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (u.pointwiseLeftKanExtensionUnit F).app d ≫
      ((u.pointwiseLeftKanExtension F).descOfIsLeftKanExtension
        (u.pointwiseLeftKanExtensionUnit F) G α).app (u.obj d) = α.app d := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact (u.pointwiseLeftKanExtension F).descOfIsLeftKanExtension_fac_app
    (u.pointwiseLeftKanExtensionUnit F) G α d

example (F : D ⥤ M) (G : E ⥤ M) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    ∀ (β γ : u.pointwiseLeftKanExtension F ⟶ G),
      u.pointwiseLeftKanExtensionUnit F ≫ whiskerLeft u β =
        u.pointwiseLeftKanExtensionUnit F ≫ whiskerLeft u γ → β = γ := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  intro β γ h
  exact (u.pointwiseLeftKanExtension F).hom_ext_of_isLeftKanExtension
    (u.pointwiseLeftKanExtensionUnit F) β γ h

example (F : D ⥤ M) (e : E) (j : CostructuredArrow u e) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    colimit.ι (CostructuredArrow.proj u e ⋙ F) j ≫
        (u.leftKanExtensionObjIsoColimit F e).inv =
      (u.leftKanExtensionUnit F).app j.left ≫ (u.leftKanExtension F).map j.hom := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact ι_leftKanExtensionObjIsoColimit_inv u F e j

example (F : D ⥤ M) (d : D) :
    letI : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
    (u.leftKanExtensionUnit F).app d ≫
        (u.leftKanExtensionObjIsoColimit F (u.obj d)).hom =
      colimit.ι (CostructuredArrow.proj u (u.obj d) ⋙ F)
        (CostructuredArrow.mk (𝟙 (u.obj d))) := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  exact leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom u F d

example :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
    (u.lanAdjunction M).unit = u.lanUnit := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
  exact u.lanAdjunction_unit M

example (G : E ⥤ M) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
    (u.lanAdjunction M).counit.app G =
      (u.lan.obj (u ⋙ G)).descOfIsLeftKanExtension
        (u.lanUnit.app (u ⋙ G)) G (𝟙 (u ⋙ G)) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
  exact u.lanAdjunction_counit_app G

example (F : D ⥤ M) (G : E ⥤ M) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
    (fun (β : u.lan.obj F ⟶ G) (d : D) =>
      ((u.lanAdjunction M).homEquiv F G β).app d) =
      fun (β : u.lan.obj F ⟶ G) (d : D) =>
        ((u.lanAdjunction M).unit.app F).app d ≫ β.app (u.obj d) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
  funext β d
  rw [Adjunction.homEquiv_apply]
  rfl

example (F : D ⥤ M) (G : E ⥤ M) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
    (fun (α : F ⟶ u ⋙ G) (e : E) =>
      (((u.lanAdjunction M).homEquiv F G).symm α).app e) =
      fun (α : F ⟶ u ⋙ G) (e : E) =>
        (u.lan.map α).app e ≫ ((u.lanAdjunction M).counit.app G).app e := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
  funext α e
  rw [Adjunction.homEquiv_symm_apply]
  rfl

example (F : D ⥤ M) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
    u.lan.map ((u.lanAdjunction M).unit.app F) ≫
      (u.lanAdjunction M).counit.app (u.lan.obj F) = 𝟙 (u.lan.obj F) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
  exact (u.lanAdjunction M).left_triangle_components F

example (G : E ⥤ M) (d : D) :
    letI : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
    ((u.lanAdjunction M).unit.app (u ⋙ G)).app d ≫
      ((u.lanAdjunction M).counit.app G).app (u.obj d) = 𝟙 (G.obj (u.obj d)) := by
  let _ : ∀ H : D ⥤ M, u.HasLeftKanExtension H := fun H => dM.hasLeftKanExtension u H
  exact congr_app ((u.lanAdjunction M).right_triangle_components G) d

example (u₀ : Discrete PEmpty.{1} ⥤ E) (F : Discrete PEmpty.{1} ⥤ M) :
    u₀.HasLeftKanExtension F := dM.hasLeftKanExtension u₀ F

example (u₀ : Discrete ℕ ⥤ E) (F : Discrete ℕ ⥤ M) :
    u₀.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u₀ F

example (u₀ : SingleObj (Multiplicative ℕ) ⥤ E)
    (F : SingleObj (Multiplicative ℕ) ⥤ M) :
    u₀.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u₀ F

section Raised

local instance : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance : Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))
local instance : EssentiallySmall.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  (essentiallySmall_congr (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D)).mp inferInstance
local instance : Category.{vE} (ULift.{uE + 1} E) := uliftCategory E
local instance : Category.{max (vE + 1) vE} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) :=
  @ULiftHom.category (ULift.{uE + 1} E) (inferInstance : Category.{vE} (ULift.{uE + 1} E))
local instance : LocallySmall.{w} (ULiftHom.{vE + 1} (ULift.{uE + 1} E)) where
  hom_small x y := by
    let _ : Small.{w} (x.objDown.down ⟶ y.objDown.down) := LocallySmall.hom_small _ _
    exact small_map Equiv.ulift

example (u₀ : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ ULiftHom.{vE + 1} (ULift.{uE + 1} E))
    (F : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :
    u₀.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u₀ F

end Raised
end MathlibExtTest.CofibrantGenerationLeftKanExtensions
