/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionOrder

/-!
# The actual one-cell extension diagram and original endpoint pushout

The original old vertices, all old maps, lower-colimit cofans and root are
retained. The new vertex uses the captured attaching map into its original
selected lower point. The whole endpoint is the actual pushout over the
original old endpoint, with every original cocone leg constructed explicitly.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.GoodCellExtensionDiagram

open Limits LowerSetColimits GoodCellExtensionOrder

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {P : Type w} [PartialOrder P] {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet P) (i : A) (a : (s i).left ⟶ (L.obj B).right)

/-- The actual new vertex under the unchanged original root. -/
abbrev newPoint : Under X :=
  Under.mk ((L.obj B).hom ≫ pushout.inl a (s i).hom)

/-- The selected original lower point maps to its actual new pushout vertex. -/
def newStep : L.obj B ⟶ newPoint T L B i a :=
  Under.homMk (pushout.inl a (s i).hom) rfl

/-- The original cell target keeps its actual local pushout inclusion. -/
abbrev newCell : (s i).right ⟶ (newPoint T L B i a).right := pushout.inr a (s i).hom

/-- The entire original cell square is the actual new-vertex pushout. -/
theorem newPoint_isPushout :
    IsPushout a (s i).hom (newStep T L B i a).right (newCell T L B i a) :=
  IsPushout.of_hasPushout a (s i).hom

/-- Every old vertex is unchanged, and the new cell uses the selected actual pushout. -/
def vertex (x : Index P) : Under X :=
  match x.val with
  | some p => T.vertex p
  | none => newPoint T L B i a

/-- The actual extension map uses only old maps and the original lower cofan. -/
def mapOfLe {x y : Index P} (h : extensionLe B x y) :
    vertex T L B i a x ⟶ vertex T L B i a y := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  cases x with
  | none =>
    cases y with
    | none => exact 𝟙 _
    | some y => exact False.elim h
  | some x =>
    cases y with
    | none => exact L.ι B ⟨x, h⟩ ≫ newStep T L B i a
    | some y => exact T.diagram.map (homOfLE h)

/-- The full old-cell map function retains every original old comparison. -/
theorem mapOfLe_old_old (p q : P) (h : p ≤ q) :
    mapOfLe T L B i a (x := Index.old p) (y := Index.old q) h =
      T.diagram.map (homOfLE h) := rfl

/-- The original selected lower cofan supplies every map into the new vertex. -/
theorem mapOfLe_old_new (p : P) (h : p ∈ B) :
    mapOfLe T L B i a (x := Index.old p) (y := Index.new) h =
      L.ι B ⟨p, h⟩ ≫ newStep T L B i a := rfl

/-- Every actual extension identity map is the identity on its same original vertex. -/
theorem mapOfLe_id (x : Index P) :
    mapOfLe T L B i a ((extensionOrder B).le_refl x) = 𝟙 (vertex T L B i a x) := by
  rcases x with ⟨x⟩
  cases x with
  | none => rfl
  | some x =>
    change T.diagram.map (𝟙 x) = 𝟙 _
    exact T.diagram.map_id x

/-- Actual original lower-cofan naturality proves composition for every extension map. -/
theorem mapOfLe_comp {x y z : Index P} (h : extensionLe B x y) (k : extensionLe B y z) :
    mapOfLe T L B i a ((extensionOrder B).le_trans x y z h k) =
      mapOfLe T L B i a h ≫ mapOfLe T L B i a k := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rcases z with ⟨z⟩
  cases x with
  | none =>
    cases y with
    | some y => exact False.elim h
    | none =>
      cases z with
      | some z => exact False.elim k
      | none => exact (Category.id_comp _).symm
  | some x =>
    cases y with
    | none =>
      cases z with
      | some z => exact False.elim k
      | none => exact (Category.comp_id _).symm
    | some y =>
      cases z with
      | some z =>
        change T.diagram.map (homOfLE (h.trans k)) =
          T.diagram.map (homOfLE h) ≫ T.diagram.map (homOfLE k)
        rw [← T.diagram.map_comp]
        rfl
      | none =>
        have hx : x ∈ B := B.lower' h k
        have hc : T.diagram.map (homOfLE h) ≫ L.ι B ⟨y, k⟩ = L.ι B ⟨x, hx⟩ :=
          (L.cocone B).w (homOfLE h : (⟨x, hx⟩ : B) ⟶ ⟨y, k⟩)
        change L.ι B ⟨x, hx⟩ ≫ newStep T L B i a =
          T.diagram.map (homOfLE h) ≫ (L.ι B ⟨y, k⟩ ≫ newStep T L B i a)
        rw [← Category.assoc, hc]

/-- The whole actual extended vertex diagram uses the constructed weaker order. -/
def diagram : letI := extensionOrder B
    Index P ⥤ Under X := by
  letI := extensionOrder B
  exact {
    obj := vertex T L B i a
    map := fun h => mapOfLe T L B i a (leOfHom h)
    map_id := mapOfLe_id T L B i a
    map_comp := fun h k => mapOfLe_comp T L B i a (leOfHom h) (leOfHom k) }

/-- The complete old vertex object function is retained literally. -/
theorem diagram_old_objects (p : P) :
    letI := extensionOrder B
    (diagram T L B i a).obj (Index.old p) = T.vertex p := rfl

/-- The new vertex is exactly its original selected lower-point pushout. -/
theorem diagram_new_object :
    letI := extensionOrder B
    (diagram T L B i a).obj Index.new = newPoint T L B i a := rfl

/-- The same original selected lower colimit maps to the original old endpoint. -/
def lowerToEndpoint : L.obj B ⟶ T.endpointObj :=
  L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom

omit [HasPushouts C] in
/-- Every original lower cofan leg retains its original old endpoint inclusion. -/
@[reassoc]
theorem lowerToEndpoint_fac (b : B) :
    L.ι B b ≫ lowerToEndpoint T L B = T.inclusion b.1 := by
  rw [lowerToEndpoint, L.ι_map_assoc, T.ι_endpointIso_hom]

/-- The original attaching source is mapped to the same original old endpoint. -/
abbrev globalAttaching : (s i).left ⟶ T.endpointObj.right :=
  a ≫ (lowerToEndpoint T L B).right

/-- The actual whole extension endpoint remains under the unchanged original root. -/
abbrev wholePoint : Under X :=
  Under.mk (T.hom ≫ pushout.inl (globalAttaching T L B i a) (s i).hom)

/-- The original old endpoint has its exact whole pushout inclusion. -/
def endpointStep : T.endpointObj ⟶ wholePoint T L B i a :=
  Under.homMk (pushout.inl (globalAttaching T L B i a) (s i).hom) rfl

/-- The original cell target has its actual inclusion into the whole endpoint pushout. -/
abbrev wholeCell : (s i).right ⟶ (wholePoint T L B i a).right :=
  pushout.inr (globalAttaching T L B i a) (s i).hom

/-- The local new vertex maps to the actual whole original endpoint pushout. -/
def newToWhole : newPoint T L B i a ⟶ wholePoint T L B i a :=
  Under.homMk
    (pushout.desc
      ((lowerToEndpoint T L B).right ≫ (endpointStep T L B i a).right)
      (wholeCell T L B i a) (by
        change a ≫ ((lowerToEndpoint T L B).right ≫
            pushout.inl (globalAttaching T L B i a) (s i).hom) =
          (s i).hom ≫ pushout.inr (globalAttaching T L B i a) (s i).hom
        rw [← Category.assoc]
        exact pushout.condition))
    (by
      change ((L.obj B).hom ≫ pushout.inl a (s i).hom) ≫ _ =
        T.hom ≫ pushout.inl (globalAttaching T L B i a) (s i).hom
      rw [Category.assoc, pushout.inl_desc, ← Category.assoc, Under.w]
      rfl)

/-- The actual local pushout source map retains its original whole endpoint equation. -/
theorem newToWhole_step :
    newStep T L B i a ≫ newToWhole T L B i a =
      lowerToEndpoint T L B ≫ endpointStep T L B i a := by
  apply Under.UnderMorphism.ext
  exact pushout.inl_desc _ _ _

/-- The actual original cell map is unchanged at the whole endpoint. -/
@[reassoc]
theorem newToWhole_cell :
    newCell T L B i a ≫ (newToWhole T L B i a).right = wholeCell T L B i a :=
  pushout.inr_desc _ _ _

/-- Every original vertex has its actual constructed endpoint cocone leg. -/
def endpointLeg (x : Index P) : vertex T L B i a x ⟶ wholePoint T L B i a := by
  rcases x with ⟨x⟩
  cases x with
  | some p => exact T.inclusion p ≫ endpointStep T L B i a
  | none => exact newToWhole T L B i a

/-- All actual original extension maps retain the complete endpoint cocone naturality. -/
theorem endpointLeg_naturality {x y : Index P} (h : extensionLe B x y) :
    mapOfLe T L B i a h ≫ endpointLeg T L B i a y = endpointLeg T L B i a x := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  cases x with
  | none =>
    cases y with
    | some y => exact False.elim h
    | none => exact Category.id_comp _
  | some x =>
    cases y with
    | some y =>
      change T.diagram.map (homOfLE h) ≫
        (T.inclusion y ≫ endpointStep T L B i a) = T.inclusion x ≫ endpointStep T L B i a
      rw [← Category.assoc, T.inclusion_naturality]
    | none =>
      change (L.ι B ⟨x, h⟩ ≫ newStep T L B i a) ≫ newToWhole T L B i a =
        T.inclusion x ≫ endpointStep T L B i a
      rw [Category.assoc, newToWhole_step, ← Category.assoc, lowerToEndpoint_fac]

/-- The entire original extended diagram has this actual whole endpoint cocone. -/
def endpointCocone : letI := extensionOrder B
    Cocone (diagram T L B i a) := by
  letI := extensionOrder B
  exact {
    pt := wholePoint T L B i a
    ι := {
      app := endpointLeg T L B i a
      naturality x y h := by
        change mapOfLe T L B i a (leOfHom h) ≫ endpointLeg T L B i a y =
          endpointLeg T L B i a x ≫ 𝟙 _
        rw [Category.comp_id]
        exact endpointLeg_naturality T L B i a (leOfHom h) } }

end CategoryTheory.SmallObject.GoodCellExtensionDiagram
