/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.EqToHom

/-!
# Genuine gluing of compatible actual initial-stage vertex diagrams

The original lower-stage functors and their actual overlap object/map
compatibility construct the whole vertex functor. Every global map is
transported from a real stage containing its target. The actual local
functor laws prove the whole identity/composition laws.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.InitialFunctorFamilyGlue

open Limits

variable {P I : Type w} [Preorder P] {C : Type u} [Category.{v} C]
  (S : I → LowerSet P) (F : ∀ i : I, S i ⥤ C)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  (hObj : ∀ (i j : I) (p : P) (hi : p ∈ S i) (hj : p ∈ S j),
    (F i).obj ⟨p, hi⟩ = (F j).obj ⟨p, hj⟩)

/-- The actual original stage chosen for an original label. -/
def stage (p : P) : I := (hCover p).choose

/-- The original label is in its actual selected stage. -/
theorem in_stage (p : P) : p ∈ S (stage S hCover p) := (hCover p).choose_spec

/-- The whole original vertex object is the actual selected stage's vertex object. -/
def obj (p : P) : C := (F (stage S hCover p)).obj ⟨p, in_stage S hCover p⟩

include hObj in
/-- Actual overlap compatibility identifies the selected object with each containing stage. -/
theorem obj_eq (i : I) (p : P) (hp : p ∈ S i) : obj S F hCover p = (F i).obj ⟨p, hp⟩ :=
  hObj (stage S hCover p) i p (in_stage S hCover p) hp

/-- The actual original stage map transported by its real original object equalities. -/
def stageMap (i : I) {p q : P} (hp : p ∈ S i) (hq : q ∈ S i) (h : p ≤ q) :
    obj S F hCover p ⟶ obj S F hCover q :=
  eqToHom (obj_eq S F hCover hObj i p hp) ≫
    (F i).map (homOfLE h : (⟨p, hp⟩ : S i) ⟶ ⟨q, hq⟩) ≫
    eqToHom (obj_eq S F hCover hObj i q hq).symm

/-- The whole stage-map expression is heterogeneously the same actual original stage map. -/
theorem stageMap_heq (i : I) {p q : P} (hp : p ∈ S i) (hq : q ∈ S i) (h : p ≤ q) :
    stageMap S F hCover hObj i hp hq h ≍
      (F i).map (homOfLE h : (⟨p, hp⟩ : S i) ⟶ ⟨q, hq⟩) := by
  unfold stageMap
  rw [← Category.assoc]
  let fi := (F i).map (homOfLE h : (⟨p, hp⟩ : S i) ⟶ ⟨q, hq⟩)
  exact (comp_eqToHom_heq
    (eqToHom (obj_eq S F hCover hObj i p hp) ≫ fi)
    (obj_eq S F hCover hObj i q hq).symm).trans
      (eqToHom_comp_heq fi (obj_eq S F hCover hObj i p hp))

variable
  (hMap : ∀ (i j : I) (p q : P) (hip : p ∈ S i) (hiq : q ∈ S i)
    (hjp : p ∈ S j) (hjq : q ∈ S j) (h : p ≤ q),
    (F i).map (homOfLE h : (⟨p, hip⟩ : S i) ⟶ ⟨q, hiq⟩) ≍
      (F j).map (homOfLE h : (⟨p, hjp⟩ : S j) ⟶ ⟨q, hjq⟩))

/-- The whole actual map comes from a real original lower stage containing its target. -/
def map {p q : P} (h : p ⟶ q) : obj S F hCover p ⟶ obj S F hCover q :=
  stageMap S F hCover hObj (stage S hCover q)
    ((S (stage S hCover q)).lower' (leOfHom h) (in_stage S hCover q))
    (in_stage S hCover q) (leOfHom h)

include hMap in
/-- Every whole original map is the same actual map of any stage containing its target. -/
theorem map_stage_heq (i : I) {p q : P} (hp : p ∈ S i) (hq : q ∈ S i) (h : p ⟶ q) :
    map S F hCover hObj h ≍
      (F i).map (homOfLE (leOfHom h) : (⟨p, hp⟩ : S i) ⟶ ⟨q, hq⟩) := by
  exact (stageMap_heq S F hCover hObj (stage S hCover q) _ _ _).trans
    (hMap (stage S hCover q) i p q _ _ hp hq (leOfHom h))

/-- Actual selected-stage functor identity proves the whole identity law. -/
theorem map_id (p : P) : map S F hCover hObj (𝟙 p) = 𝟙 (obj S F hCover p) := by
  change eqToHom _ ≫ (F (stage S hCover p)).map (𝟙 ⟨p, in_stage S hCover p⟩) ≫
    eqToHom _ = 𝟙 _
  rw [Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

include hMap in
/-- A real original stage containing the last label proves the whole composition law. -/
theorem map_comp {p q r : P} (h : p ⟶ q) (k : q ⟶ r) :
    map S F hCover hObj (h ≫ k) = map S F hCover hObj h ≫ map S F hCover hObj k := by
  let i := stage S hCover r
  have hr : r ∈ S i := in_stage S hCover r
  have hq : q ∈ S i := (S i).lower' (leOfHom k) hr
  have hp : p ∈ S i := (S i).lower' (leOfHom h) hq
  have hL := map_stage_heq S F hCover hObj hMap i (p := p) (q := r) hp hr (h ≫ k)
  have hh := map_stage_heq S F hCover hObj hMap i (p := p) (q := q) hp hq h
  have hk := map_stage_heq S F hCover hObj hMap i (p := q) (q := r) hq hr k
  have hR := heq_comp (obj_eq S F hCover hObj i p hp)
    (obj_eq S F hCover hObj i q hq) (obj_eq S F hCover hObj i r hr) hh hk
  have hLocal :
      (F i).map (homOfLE (leOfHom (h ≫ k : p ⟶ r)) : (⟨p, hp⟩ : S i) ⟶ ⟨r, hr⟩) =
        (F i).map (homOfLE (leOfHom h) : (⟨p, hp⟩ : S i) ⟶ ⟨q, hq⟩) ≫
        (F i).map (homOfLE (leOfHom k) : (⟨q, hq⟩ : S i) ⟶ ⟨r, hr⟩) := by
    exact (F i).map_comp _ _
  exact eq_of_heq ((hL.trans (heq_of_eq hLocal)).trans hR.symm)

/-- The actual whole original vertex functor is constructed from compatible real stage functors. -/
def functor : P ⥤ C where
  obj := obj S F hCover
  map := map S F hCover hObj
  map_id := map_id S F hCover hObj
  map_comp := map_comp S F hCover hObj hMap

end CategoryTheory.SmallObject.InitialFunctorFamilyGlue
