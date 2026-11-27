/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.CompactRootPushoutPresentation
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.RootedCellPushoutComparison

/-!
# Every map of one original root presentation

The stage maps are the actual maps of the same native pushout functor.
The complete mapped presentation keeps the original category, objects,
maps and cocone legs. An original pushout UP transports the endpoint
without selecting another diagram or replacing either coefficient leg.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uJ vJ u v

namespace CategoryTheory.SmallObject.OriginalPushoutRootPresentation

open Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {D X E : C} (u : D ⟶ X) (f : D ⟶ E)
  {J : Type uJ} [Category.{vJ} J] (p : ColimitPresentation J (Under.mk u))

/-- The same original stage, with the same original root arrow and f. -/
abbrev stage (j : J) : C := pushout (p.diag.obj j).hom f

/-- The original native root inclusion of this actual stage. -/
abbrev root (j : J) : (p.diag.obj j).right ⟶ stage u f p j :=
  pushout.inl (p.diag.obj j).hom f

/-- The same original f-target inclusion of this actual stage. -/
abbrev cellLeg (j : J) : E ⟶ stage u f p j :=
  pushout.inr (p.diag.obj j).hom f

/-- No new map is chosen: this is the actual original pushout-functor map. -/
def transition {j k : J} (h : j ⟶ k) : stage u f p j ⟶ stage u f p k :=
  ((Under.pushout f).map (p.diag.map h)).right

/-- The original root maps commute through that same actual transition. -/
theorem root_transition {j k : J} (h : j ⟶ k) :
    root u f p j ≫ transition u f p h = (p.diag.map h).right ≫ root u f p k := by
  change pushout.inl _ _ ≫
    pushout.desc ((p.diag.map h).right ≫ pushout.inl _ _) (pushout.inr _ _) _ = _
  exact pushout.inl_desc _ _ _

/-- Every transition retains the literal original generator-target inclusion. -/
theorem local_transition {j k : J} (h : j ⟶ k) :
    cellLeg u f p j ≫ transition u f p h = cellLeg u f p k := by
  change pushout.inr _ _ ≫
    pushout.desc ((p.diag.map h).right ≫ pushout.inl _ _) (pushout.inr _ _) _ = _
  exact pushout.inr_desc _ _ _

/-- The entire actual transition function retains the original functor map values. -/
theorem transition_function :
    (fun {j k : J} (h : j ⟶ k) => transition u f p h) =
      (fun {j k : J} (h : j ⟶ k) => ((Under.pushout f).map (p.diag.map h)).right) := rfl

/-- The same original stage maps retain identity. -/
theorem transition_id (j : J) : transition u f p (𝟙 j) = 𝟙 (stage u f p j) := by
  simp only [transition, p.diag.map_id, Functor.map_id]
  rfl

/-- The same original stage maps retain composition, for every original pair of arrows. -/
theorem transition_comp {j k l : J} (h : j ⟶ k) (q : k ⟶ l) :
    transition u f p h ≫ transition u f p q = transition u f p (h ≫ q) := by
  simp only [transition, p.diag.map_comp, Functor.map_comp]
  rfl

/-- The mapped original comparison is precisely the previously constructed root comparison. -/
theorem comparison_eq_rootComparison (j : J) :
    CompactRootPushoutPresentation.comparison u f p j =
      RootedCellPushoutComparison.rootComparison u f (p.diag.obj j).hom
        (p.ι.app j).right (Under.w (p.ι.app j)) := rfl

/-- The original small and whole pushout UPs give the actual stage-to-endpoint square. -/
theorem stageIsPushout (j : J) :
    IsPushout (p.ι.app j).right (root u f p j) (pushout.inl u f)
      (CompactRootPushoutPresentation.comparison u f p j) := by
  rw [comparison_eq_rootComparison]
  exact RootedCellPushoutComparison.rootIsPushout u f (p.diag.obj j).hom
    (p.ι.app j).right (Under.w (p.ι.app j))

section Connected

variable [IsConnected J]

/-- The original complete mapped diagram has exactly these actual transition values. -/
theorem presentation_map {j k : J} (h : j ⟶ k) :
    (CompactRootPushoutPresentation.presentation u f p).diag.map h =
      transition u f p h := rfl

/-- The original complete rooted diagram has the same actual right transition values. -/
theorem rootedPresentation_map {j k : J} (h : j ⟶ k) :
    ((CompactRootPushoutPresentation.rootedPresentation u f p).diag.map h).right =
      transition u f p h := rfl

/-- Original cocone naturality retains every original transition/comparison equation. -/
theorem transition_comparison {j k : J} (h : j ⟶ k) :
    transition u f p h ≫ CompactRootPushoutPresentation.comparison u f p k =
      CompactRootPushoutPresentation.comparison u f p j := by
  have hn := (CompactRootPushoutPresentation.presentation u f p).ι.naturality h
  change transition u f p h ≫
    (CompactRootPushoutPresentation.presentation u f p).ι.app k =
      (CompactRootPushoutPresentation.presentation u f p).ι.app j ≫
        (𝟙 (pushout u f)) at hn
  rw [CompactRootPushoutPresentation.presentation_leg,
    CompactRootPushoutPresentation.presentation_leg] at hn
  exact hn.trans (Category.comp_id _)

variable {Z : C} (n : X ⟶ Z) (c : E ⟶ Z) (H : IsPushout u f n c)

/-- The comparison to the actual original endpoint uses the Iso derived from its original UP. -/
def actualComparison (j : J) : stage u f p j ⟶ Z :=
  CompactRootPushoutPresentation.comparison u f p j ≫ H.isoPushout.inv

/-- The whole actual endpoint presentation keeps the same original chosen J and diagram. -/
def actualPresentation : ColimitPresentation J Z :=
  (CompactRootPushoutPresentation.presentation u f p).ofIso H.isoPushout.symm

omit [IsConnected J] in
/-- Every root leg retains the actual original root n. -/
theorem actualComparison_root (j : J) :
    root u f p j ≫ actualComparison u f p n c H j = (p.ι.app j).right ≫ n := by
  rw [actualComparison, ← Category.assoc, CompactRootPushoutPresentation.comparison_root,
    Category.assoc, H.inl_isoPushout_inv]

omit [IsConnected J] in
/-- Every f-target leg retains the actual original local map c. -/
theorem actualComparison_local (j : J) :
    cellLeg u f p j ≫ actualComparison u f p n c H j = c := by
  rw [actualComparison, ← Category.assoc, CompactRootPushoutPresentation.comparison_local,
    H.inr_isoPushout_inv]

/-- The actual original cofan leg has the same complete selected comparison value. -/
theorem actualPresentation_leg (j : J) :
    (actualPresentation u f p n c H).ι.app j = actualComparison u f p n c H j := by
  change (CompactRootPushoutPresentation.presentation u f p).ι.app j ≫
    H.isoPushout.inv = actualComparison u f p n c H j
  rw [CompactRootPushoutPresentation.presentation_leg]
  rfl

/-- The entire actual original endpoint diagram retains the same object function. -/
theorem actualPresentation_object_function :
    (fun j => (actualPresentation u f p n c H).diag.obj j) =
      (fun j => stage u f p j) := rfl

/-- The entire actual original endpoint diagram retains all original map functions. -/
theorem actualPresentation_map_function :
    (fun {j k : J} (h : j ⟶ k) => (actualPresentation u f p n c H).diag.map h) =
      (fun {j k : J} (h : j ⟶ k) => transition u f p h) := rfl

end Connected

end CategoryTheory.SmallObject.OriginalPushoutRootPresentation
