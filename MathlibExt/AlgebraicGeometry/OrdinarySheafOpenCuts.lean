/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels

/-!
# Ordinary sheaf open cuts from actual local vanishing

The cut sections are the original sheaf sections that vanish in a
neighborhood of every point outside the chosen open. The native
sheafification of this prescribed presheaf is the ordinary extension
by zero of the restriction to that open. This supplies actual open
graph and half-line coefficient sheaves; it is not used as an
Ind-stalk or bordered restriction kernel.

Source: Kashiwara--Schapira, Sheaves on Manifolds, Section2.3;
D'Agnolo--Kashiwara1311.2374v2, Sections3.2--3.3 and4.1.
Native coefficient presheaves, submodules and sheafification are
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinarySheafOpenCuts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves

variable (k : Type) [Field k] (X : TopCat.{0})

/-- Restrict an original coefficient section to the original subopen. -/
def restrictSection (F : OrdinarySheaf k X) {U V : Opens X} (h : V ≤ U) :
    F.presheaf.obj (op U) →ₗ[k] F.presheaf.obj (op V) :=
  (F.presheaf.map (homOfLE h).op).hom

/-- The original presheaf restriction composition. -/
theorem restrictSection_comp (F : OrdinarySheaf k X) {U V W : Opens X}
    (h : V ≤ U) (j : W ≤ V) (s : F.presheaf.obj (op U)) :
    restrictSection k X F j (restrictSection k X F h s) =
      restrictSection k X F (j.trans h) s := by
  change (((F.presheaf.map (homOfLE h).op) ≫
    (F.presheaf.map (homOfLE j).op)).hom) s = _
  rw [← F.presheaf.map_comp]
  rfl

/-- Local vanishing outside the actual chosen open, on original coefficient sections. -/
def CutSection (F : OrdinarySheaf k X) (U V : Opens X) (s : F.presheaf.obj (op V)) : Prop :=
  ∀ (x : X), x ∈ V → x ∉ U →
    ∃ (W : Opens X) (h : W ≤ V), x ∈ W ∧ restrictSection k X F h s = 0

/-- The cut sections form an actual coefficient submodule. -/
def cutSections (F : OrdinarySheaf k X) (U V : Opens X) :
    Submodule k (F.presheaf.obj (op V)) where
  carrier := {s | CutSection k X F U V s}
  zero_mem' := by
    show CutSection k X F U V 0
    intro x hx _
    exact ⟨V, le_refl V, hx, (restrictSection k X F (le_refl V)).map_zero⟩
  add_mem' := by
    intro s t hs ht
    show CutSection k X F U V (s + t)
    intro x hx hxu
    obtain ⟨S, hS, hxS, hzS⟩ := hs x hx hxu
    obtain ⟨T, hT, hxT, hzT⟩ := ht x hx hxu
    refine ⟨S ⊓ T, inf_le_left.trans hS, ⟨hxS, hxT⟩, ?_⟩
    rw [LinearMap.map_add]
    have hs0 : restrictSection k X F ((inf_le_left : S ⊓ T ≤ S).trans hS) s = 0 := by
      rw [← restrictSection_comp k X F hS (inf_le_left : S ⊓ T ≤ S), hzS, map_zero]
    have ht0 : restrictSection k X F ((inf_le_left : S ⊓ T ≤ S).trans hS) t = 0 := by
      change restrictSection k X F ((inf_le_right : S ⊓ T ≤ T).trans hT) t = 0
      rw [← restrictSection_comp k X F hT (inf_le_right : S ⊓ T ≤ T), hzT, map_zero]
    rw [hs0, ht0, zero_add]
  smul_mem' := by
    intro a s hs
    show CutSection k X F U V (a • s)
    intro x hx hxu
    obtain ⟨W, hW, hxW, hzW⟩ := hs x hx hxu
    refine ⟨W, hW, hxW, ?_⟩
    rw [LinearMap.map_smul, hzW, smul_zero]

/-- Actual restriction preserves the cut section condition. -/
theorem cutSection_restrict (F : OrdinarySheaf k X) (U : Opens X) {V W : Opens X}
    (h : W ≤ V) {s : F.presheaf.obj (op V)} (hs : CutSection k X F U V s) :
    CutSection k X F U W (restrictSection k X F h s) := by
  intro x hx hxu
  obtain ⟨T, hT, hxT, hzT⟩ := hs x (h hx) hxu
  refine ⟨W ⊓ T, inf_le_left, ⟨hx, hxT⟩, ?_⟩
  rw [restrictSection_comp]
  change restrictSection k X F (inf_le_right.trans hT) s = 0
  rw [← restrictSection_comp k X F hT inf_le_right, hzT, map_zero]

/-- The original sheaf cut, as an actual coefficient presheaf. -/
def cutPresheaf (F : OrdinarySheaf k X) (U : Opens X) : (Opens X)ᵒᵖ ⥤ ModuleCat.{0} k where
  obj V := ModuleCat.of k (cutSections k X F U V.unop)
  map {V W} f := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨(F.presheaf.map f).hom s.val,
        cutSection_restrict k X F U f.unop.le s.property⟩
      map_add' s t := by apply Subtype.ext; exact (F.presheaf.map f).hom.map_add s.val t.val
      map_smul' a s := by apply Subtype.ext; exact (F.presheaf.map f).hom.map_smul a s.val }
  map_id V := by
    ext s
    change (F.presheaf.map (𝟙 V)).hom s.val = s.val
    rw [F.presheaf.map_id]
    rfl
  map_comp f g := by
    ext s
    change (F.presheaf.map (f ≫ g)).hom s.val =
      (F.presheaf.map g).hom ((F.presheaf.map f).hom s.val)
    rw [F.presheaf.map_comp]
    rfl

/-- Every original coefficient-sheaf map preserves actual local vanishing. -/
theorem cutSection_map {F G : OrdinarySheaf k X} (a : F ⟶ G) (U V : Opens X)
    {s : F.presheaf.obj (op V)} (hs : CutSection k X F U V s) :
    CutSection k X G U V ((a.hom.app (op V)).hom s) := by
  intro x hx hxu
  obtain ⟨W, hW, hxW, hzW⟩ := hs x hx hxu
  refine ⟨W, hW, hxW, ?_⟩
  have ha := congrArg (fun f ↦ f.hom s) (a.hom.naturality (homOfLE hW).op)
  change restrictSection k X G hW ((a.hom.app (op V)).hom s) = 0
  change (a.hom.app (op W)).hom (restrictSection k X F hW s) =
    restrictSection k X G hW ((a.hom.app (op V)).hom s) at ha
  rw [← ha, hzW, map_zero]

/-- All cut maps retain the original coefficient-sheaf maps on their original sections. -/
def cutPresheafFunctor (U : Opens X) : OrdinarySheaf k X ⥤ (Opens X)ᵒᵖ ⥤ ModuleCat.{0} k where
  obj F := cutPresheaf k X F U
  map a :=
    { app V := ModuleCat.ofHom
        { toFun := fun s ↦ ⟨(a.hom.app V).hom s.val, cutSection_map k X a U V.unop s.property⟩
          map_add' s t := by apply Subtype.ext; exact (a.hom.app V).hom.map_add s.val t.val
          map_smul' r s := by apply Subtype.ext; exact (a.hom.app V).hom.map_smul r s.val }
      naturality {V W} f := by
        ext s
        apply Subtype.ext
        exact congrArg (fun g ↦ g.hom s.val) (a.hom.naturality f) }
  map_id F := by ext V s; rfl
  map_comp a b := by ext V s; rfl

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

/-- The actual ordinary open cut is the native sheafification of these original local-vanishing sections. -/
def ordinaryOpenCut (U : Opens X) : OrdinarySheaf k X ⥤ OrdinarySheaf k X :=
  cutPresheafFunctor k X U ⋙ presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)

end MathlibExt.AlgebraicGeometry.OrdinarySheafOpenCuts
