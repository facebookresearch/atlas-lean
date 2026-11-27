/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import MathlibExt.CategoryTheory.Limits.DiscreteSourceMapping

/-!
# Whole source-object and source-map families retain their exact transports

The complete generic declarations are retained from the original native
Omega weak-class source. Original universes, chosen fans/cofans, maps,
hypotheses and proof bodies are unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w uC vC uD vD uV vV uI uT
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OriginalSourceObjectTransport

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : Type w} (F : Cᵒᵖ ⥤ D)
  (O : C → D) (hO : O = fun X => F.obj (Opposite.op X))

/-- The actual family equality transports only the whole source object function. -/
def iso (X : C) : F.obj (Opposite.op X) ≅ O X :=
  eqToIso (congrFun hO X).symm

/-- Every original source map retains both actual endpoints under the whole family transport. -/
def pre {X Y : C} (f : X ⟶ Y) : O Y ⟶ O X :=
  (iso F O hO Y).inv ≫ F.map f.op ≫ (iso F O hO X).hom

/-- The entire source-map family is retained after the exact object-function equality. -/
theorem pre_heq {X Y : C} (f : X ⟶ Y) : HEq (pre F O hO f) (F.map f.op) := by
  cases hO
  simp only [pre, iso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  rfl

/-- Every original caller cofan retains a limiting mapping fan under whole endpoint transport. -/
def fan {X : J → C} (c : Cofan X) : Fan (fun j => O (X j)) :=
  Fan.mk (O c.pt) (fun j => pre F O hO (c.inj j))

/-- The complete mapping limit proof is transported while category data remain generic. -/
def fanIsLimit [PreservesLimitsOfSize.{w, w} F]
    {X : J → C} (c : Cofan X) (hc : IsColimit c) : IsLimit (fan F O hO c) := by
  cases hO
  have hFan : fan F (fun X => F.obj (Opposite.op X)) rfl c ≅
      CategoryTheory.OriginalDiscreteSourceMapping.fan F c :=
    Cone.ext (Iso.refl _) (fun j => by
      change (𝟙 _ ≫ F.map (c.inj j.as).op ≫ 𝟙 _) = 𝟙 _ ≫ F.map (c.inj j.as).op
      rw [Category.id_comp, Category.comp_id, Category.id_comp])
  exact IsLimit.ofIsoLimit (CategoryTheory.OriginalDiscreteSourceMapping.fanIsLimit F c hc)
    hFan.symm


/-- The actual product Iso has every original endpoint and source leg retained. -/
def productIso [PreservesLimitsOfSize.{w, w} F]
    {X : J → C} (c : Cofan X) (hc : IsColimit c) [HasProduct (fun j => O (X j))] :
    O c.pt ≅ ∏ᶜ (fun j => O (X j)) :=
  CategoryTheory.OriginalDiscreteSourceMapping.isoOfFan (fan F O hO c)
    (fanIsLimit F O hO c hc)

/-- Both directions of the actual product Iso retain all original source legs. -/
theorem productIso_hom_projection [PreservesLimitsOfSize.{w, w} F]
    {X : J → C} (c : Cofan X) (hc : IsColimit c) [HasProduct (fun j => O (X j))] (j : J) :
    (productIso F O hO c hc).hom ≫ Pi.π (fun j => O (X j)) j = pre F O hO (c.inj j) :=
  CategoryTheory.OriginalDiscreteSourceMapping.isoOfFan_hom_projection
    (fan F O hO c) (fanIsLimit F O hO c hc) j

/-- The inverse comparison keeps all original mapping projections. -/
theorem productIso_inv_projection [PreservesLimitsOfSize.{w, w} F]
    {X : J → C} (c : Cofan X) (hc : IsColimit c) [HasProduct (fun j => O (X j))] (j : J) :
    (productIso F O hO c hc).inv ≫ pre F O hO (c.inj j) = Pi.π (fun j => O (X j)) j :=
  CategoryTheory.OriginalDiscreteSourceMapping.isoOfFan_inv_projection
    (fan F O hO c) (fanIsLimit F O hO c hc) j

end CategoryTheory.OriginalSourceObjectTransport

namespace CategoryTheory.OriginalSourceObjectTransport

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : Cᵒᵖ ⥤ D) (O : C → D) (hO : O = fun X => F.obj (Opposite.op X))
  (P : ∀ {X Y : C}, (X ⟶ Y) → (O Y ⟶ O X))
  (hP : HEq (fun (X Y : C) (f : X ⟶ Y) => @P X Y f)
    (fun (X Y : C) (f : X ⟶ Y) => F.map f.op))

include hP in
/-- An exact whole source-map function equality gives every original transported pre-map. -/
theorem pre_eq {X Y : C} (f : X ⟶ Y) : pre F O hO f = P f := by
  cases hO
  have h := eq_of_heq hP
  have hf := congrFun (congrFun (congrFun h X) Y) f
  simpa only [pre, iso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id] using hf.symm

end CategoryTheory.OriginalSourceObjectTransport

namespace CategoryTheory.OriginalFunctionHEq

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (O O' : C → C → D)
  (P : ∀ X X' Y : C, (X' ⟶ X) → (O X Y ⟶ O X' Y))
  (Q : ∀ X X' Y : C, (X' ⟶ X) → (O' X Y ⟶ O' X' Y))
  (hO : O = O') (hP : HEq P Q)

include hO hP in
/-- The actual whole source-map algorithm retains its target and input order
when specialized from the complete dependent map-family equality. -/
theorem weightMapAtTarget (E : C) :
    HEq (fun (X Y : C) (f : X ⟶ Y) => P Y X E f)
      (fun (X Y : C) (f : X ⟶ Y) => Q Y X E f) := by
  cases hO
  cases eq_of_heq hP
  rfl

end CategoryTheory.OriginalFunctionHEq

namespace CategoryTheory
variable {C : Type uC} [Category.{vC} C]
/-- The full inverse Iso leg is derived from its actual forward leg equation. -/
theorem originalIso_inv_projection {X Y Z : C} (e : X ≅ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
    (h : e.hom ≫ p = q) : e.inv ≫ q = p :=
  (congrArg (fun f => e.inv ≫ f) h).symm.trans (e.inv_hom_id_assoc p)
end CategoryTheory
