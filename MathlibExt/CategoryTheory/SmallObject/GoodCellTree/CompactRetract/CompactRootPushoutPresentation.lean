/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.CompactRootPresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Limits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeColimits

/-!
# The whole original root presentation mapped through actual pushout

The actual native pushout adjunction preserves the original root
presentation. Every root piece, original cell-side map and whole
comparison function is retained. The mapped endpoint is the same
original pushout, with its proved original universal property.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe uJ vJ u v

namespace CategoryTheory.SmallObject.CompactRootPushoutPresentation

open Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {D X Y : C} (u : D ⟶ X) (f : D ⟶ Y)
  {J : Type uJ} [Category.{vJ} J] [IsConnected J]
  (p : ColimitPresentation J (Under.mk u))

/-- The original root presentation is mapped through the actual pushout/right-object functor. -/
def presentation : ColimitPresentation J (pushout u f) :=
  p.map (Under.pushout f ⋙ Under.forget Y)

/-- Every actual mapped object is the pushout of the same original small root arrow and f. -/
theorem object_function :
    (fun j => (presentation u f p).diag.obj j) =
      (fun j => pushout (p.diag.obj j).hom f) := rfl

/-- Every actual mapped cofan leg is the original selected pushout comparison descender. -/
def comparison (j : J) : pushout (p.diag.obj j).hom f ⟶ pushout u f :=
  pushout.desc ((p.ι.app j).right ≫ pushout.inl u f) (pushout.inr u f) (by
    rw [← Category.assoc, Under.w]
    exact pushout.condition)

omit [IsConnected J] in
/-- Each complete original root-side comparison retains the actual original root-piece leg. -/
theorem comparison_root (j : J) :
    pushout.inl (p.diag.obj j).hom f ≫ comparison u f p j =
      (p.ι.app j).right ≫ pushout.inl u f :=
  pushout.inl_desc _ _ _

omit [IsConnected J] in
/-- Each complete original cell-side comparison retains the same original cell-stage function. -/
theorem comparison_local (j : J) :
    pushout.inr (p.diag.obj j).hom f ≫ comparison u f p j = pushout.inr u f :=
  pushout.inr_desc _ _ _

/-- The native mapped presentation has precisely the same complete original comparison function. -/
theorem presentation_leg (j : J) :
    (presentation u f p).ι.app j = comparison u f p j := by
  change ((Under.pushout f).map (p.ι.app j)).right ≫ 𝟙 _ = comparison u f p j
  rw [Category.comp_id]
  rfl

/-- The native root equation identifies the mapped point with the actual original rooted pushout. -/
def endpointIso :
    (Under.map f).obj ((Under.pushout f).obj (Under.mk u)) ≅
      (Under.map u).obj (Under.mk (pushout.inl u f)) :=
  Under.isoMk (Iso.refl _) (by
    change (f ≫ pushout.inr u f) ≫ 𝟙 _ = u ≫ pushout.inl u f
    rw [Category.comp_id]
    exact pushout.condition.symm)

/-- The same actual root presentation has its whole original rooted pushout colimit. -/
def rootedPresentation :
    ColimitPresentation J ((Under.map u).obj (Under.mk (pushout.inl u f))) :=
  (p.map (Under.pushout f ⋙ Under.map f)).ofIso (endpointIso u f)

/-- Every mapped root-piece map retains the same original compact-root comparison function. -/
theorem rooted_leg_right (j : J) :
    ((rootedPresentation u f p).ι.app j).right = comparison u f p j := by
  change (((Under.pushout f).map (p.ι.app j) ≫ 𝟙 _).right ≫ 𝟙 _) =
    comparison u f p j
  rw [Category.comp_id, Category.comp_id]
  rfl

/-- The entire original compact-root cofan right-function remains the same selected comparison. -/
theorem rooted_leg_right_function :
    (fun j => ((rootedPresentation u f p).ι.app j).right) =
      (fun j => comparison u f p j) := by
  funext j
  exact rooted_leg_right u f p j

end CategoryTheory.SmallObject.CompactRootPushoutPresentation
