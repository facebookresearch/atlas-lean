/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialFunctorFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.EqToHom

/-!
# Genuine natural comparisons for actual glued original vertex diagrams

The complete natural transformation is constructed from the actual stage
components. Stage overlap compatibility proves every whole component
comparison; an actual stage containing a map's target proves its whole
naturality square. No natural retract is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.InitialFunctorComparisonGlue

open Limits LowerSetColimits InitialFunctorFamilyGlue

variable {P I Q : Type w} [PartialOrder P] [Preorder Q]
  {C : Type u} [Category.{v} C]
  (S : I → LowerSet P) (F : ∀ i : I, S i ⥤ C)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (F i).obj ⟨p, hi⟩ = (F j).obj ⟨p, hj⟩)
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (F i).map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (F j).map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))
  (f : P →o Q) (Y : Q ⥤ C)
  (beta : ∀ i : I, F i ⟶ restriction (f.monotone.functor ⋙ Y) (S i))
  (hBeta : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (beta i).app ⟨p, hi⟩ ≍ (beta j).app ⟨p, hj⟩)

/-- The complete actual component is the original chosen stage component at the same label. -/
def component (p : P) : obj S F hCover p ⟶ Y.obj (f p) :=
  eqToHom (obj_eq S F hCover hObj (stage S hCover p) p (in_stage S hCover p)) ≫
    (beta (stage S hCover p)).app ⟨p, in_stage S hCover p⟩

include hBeta in
/-- Every actual global component keeps its original component of any containing stage. -/
theorem component_heq (i : I) (p : P) (hp : p ∈ S i) :
    component S F hCover hObj f Y beta p ≍ (beta i).app ⟨p, hp⟩ :=
  (eqToHom_comp_heq
    ((beta (stage S hCover p)).app ⟨p, in_stage S hCover p⟩)
    (obj_eq S F hCover hObj (stage S hCover p) p (in_stage S hCover p))).trans
      (hBeta (stage S hCover p) i p (in_stage S hCover p) hp)

include hBeta in
/-- The entire actual stage component square uses the actual original vertex equality. -/
theorem component_stage_eq (i : I) (p : P) (hp : p ∈ S i) :
    component S F hCover hObj f Y beta p =
      eqToHom (obj_eq S F hCover hObj i p hp) ≫ (beta i).app ⟨p, hp⟩ :=
  eq_of_heq ((component_heq S F hCover hObj f Y beta hBeta i p hp).trans
    (eqToHom_comp_heq ((beta i).app ⟨p, hp⟩) (obj_eq S F hCover hObj i p hp)).symm)

include hBeta in
/-- An actual original stage containing the last label proves every whole naturality square. -/
theorem component_naturality (p q : P) (h : p ⟶ q) :
    (functor S F hCover hObj hMap).map h ≫ component S F hCover hObj f Y beta q =
      component S F hCover hObj f Y beta p ≫ Y.map (f.monotone.functor.map h) := by
  let i := stage S hCover q
  have hq : q ∈ S i := in_stage S hCover q
  have hp : p ∈ S i := (S i).lower' (leOfHom h) hq
  let ep : obj S F hCover p ≅ (F i).obj ⟨p, hp⟩ :=
    eqToIso (obj_eq S F hCover hObj i p hp)
  let eq : obj S F hCover q ≅ (F i).obj ⟨q, hq⟩ :=
    eqToIso (obj_eq S F hCover hObj i q hq)
  let hm : (⟨p, hp⟩ : S i) ⟶ ⟨q, hq⟩ := homOfLE (leOfHom h)
  let bp : (F i).obj ⟨p, hp⟩ ⟶ Y.obj (f p) := (beta i).app ⟨p, hp⟩
  let bq : (F i).obj ⟨q, hq⟩ ⟶ Y.obj (f q) := (beta i).app ⟨q, hq⟩
  let zm : Y.obj (f p) ⟶ Y.obj (f q) := Y.map (f.monotone.functor.map h)
  have hf : (functor S F hCover hObj hMap).map h =
      ep.hom ≫ (F i).map hm ≫ eq.inv :=
    (conj_eqToHom_iff_heq _ _
      (obj_eq S F hCover hObj i p hp) (obj_eq S F hCover hObj i q hq)).2
      (map_stage_heq S F hCover hObj hMap i hp hq h)
  have hcp : component S F hCover hObj f Y beta p = ep.hom ≫ bp :=
    component_stage_eq S F hCover hObj f Y beta hBeta i p hp
  have hcq : component S F hCover hObj f Y beta q = eq.hom ≫ bq :=
    component_stage_eq S F hCover hObj f Y beta hBeta i q hq
  have hn : (F i).map hm ≫ bq = bp ≫ zm :=
    (beta i).naturality hm
  rw [hf, hcq, hcp]
  change (ep.hom ≫ (F i).map hm ≫ eq.inv) ≫ (eq.hom ≫ bq) = (ep.hom ≫ bp) ≫ zm
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun m => ep.hom ≫ m) hn

/-- The actual whole original vertex comparison is constructed with all naturality squares. -/
def comparison : functor S F hCover hObj hMap ⟶ f.monotone.functor ⋙ Y where
  app := component S F hCover hObj f Y beta
  naturality := component_naturality S F hCover hObj hMap f Y beta hBeta

end CategoryTheory.SmallObject.InitialFunctorComparisonGlue
