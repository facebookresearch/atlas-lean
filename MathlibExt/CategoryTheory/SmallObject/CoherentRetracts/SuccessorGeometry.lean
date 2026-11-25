/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Source-fixed retracts and actual successor pushouts

The original Arrow retract is normalized by its actual source-projection
pushout. The same public normalization definitions are moved from the
compact-retract provider, with only the particular pushout as a hypothesis.
A second pushout along the original chosen splitting gives the next
splitting and both component squares. Pasting the two actual squares
preserves an arbitrary original morphism class's pushout membership.

This is the original coherent-successor geometry in Hovey,
*Model Categories*, Proposition 2.1.16, printed pp. 33–34.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SmallObject.ArrowRetractRootNormalization

open Limits

variable {C : Type u} [Category.{v} C]
  {A B X Y : C} {i : A ⟶ B} {g : X ⟶ Y} (R : RetractArrow g i)
  [HasPushout R.r.left i]

/-- The actual original source projection is the new native pushout input. -/
abbrev obj : C := pushout R.r.left i

/-- The new source is the actual original retract source X. -/
abbrev root : X ⟶ obj R := pushout.inl R.r.left i

/-- The comparison from the same original old target B. -/
abbrev oldTargetMap : B ⟶ obj R := pushout.inr R.r.left i

/-- The original retract square constructs the whole new projection. -/
def projection : obj R ⟶ Y :=
  pushout.desc g R.r.right R.r_w

/-- The original target inclusion followed by the same native comparison. -/
def inclusion : Y ⟶ obj R := R.i.right ≫ oldTargetMap R

/-- The actual original source arrow is recovered through the whole projection. -/
theorem root_projection : root R ≫ projection R = g :=
  pushout.inl_desc _ _ _

/-- The old-target route is the same original target projection. -/
theorem oldTargetMap_projection : oldTargetMap R ≫ projection R = R.r.right :=
  pushout.inr_desc _ _ _

/-- Both original squares and the original source retract prove the fixed-root equation. -/
theorem arrow_inclusion : g ≫ inclusion R = root R := by
  calc
    _ = (g ≫ R.i.right) ≫ oldTargetMap R := (Category.assoc _ _ _).symm
    _ = (R.i.left ≫ i) ≫ oldTargetMap R := by rw [R.i_w]
    _ = R.i.left ≫ (i ≫ oldTargetMap R) := Category.assoc _ _ _
    _ = R.i.left ≫ (R.r.left ≫ root R) := by rw [← pushout.condition]
    _ = (R.i.left ≫ R.r.left) ≫ root R := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [R.retract_left]
      change (𝟙 X) ≫ pushout.inl R.r.left i = pushout.inl R.r.left i
      exact Category.id_comp _

/-- The new split uses exactly the original target retract equation. -/
theorem inclusion_projection : inclusion R ≫ projection R = 𝟙 Y := by
  rw [inclusion, Category.assoc, oldTargetMap_projection, R.retract_right]

/-- The whole normalized Arrow retract has identity original source components. -/
def arrowRetract : RetractArrow g (root R) where
  i := Arrow.homMk (𝟙 X) (inclusion R) (by
    change (𝟙 X) ≫ root R = g ≫ inclusion R
    rw [Category.id_comp, arrow_inclusion])
  r := Arrow.homMk (𝟙 X) (projection R) (by
    change (𝟙 X) ≫ g = root R ≫ projection R
    rw [Category.id_comp, root_projection])
  retract := by
    apply Arrow.hom_ext
    · change (𝟙 X) ≫ (𝟙 X) = 𝟙 X
      rw [Category.id_comp]
    · change inclusion R ≫ projection R = 𝟙 Y
      exact inclusion_projection R

end CategoryTheory.SmallObject.ArrowRetractRootNormalization

namespace CategoryTheory.SmallObject.CoherentRetracts.SplitObject

variable {C : Type u} [Category.{v} C]

/-- The next splitting uses the literal original source transition and
the pushout of its selected cellular representative. The source retraction
identity already forces the source inclusion identity, so it need not be
supplied again. -/
def successorObject (X : SplitObject C) {X' Z : C}
    (f : X.source ⟶ X') (g : X.source ⟶ Z) (h : RetractArrow f g)
    (hr : h.r.left = 𝟙 X.source) [HasPushout g X.inclusion] : SplitObject C where
  source := X'
  target := pushout g X.inclusion
  inclusion := h.i.right ≫ pushout.inl g X.inclusion
  retraction := pushout.desc h.r.right (X.retraction ≫ f) (by
    have hgs : g ≫ h.r.right = f := by
      have hw := h.r_w
      change h.r.left ≫ f = g ≫ h.r.right at hw
      rw [hr] at hw
      exact hw.symm.trans (Category.id_comp f)
    rw [hgs, ← Category.assoc, X.splitting, Category.id_comp])
  splitting := by
    rw [Category.assoc, pushout.inl_desc]
    exact h.retract_right

/-- Both original component squares are preserved by the actual successor map. -/
def successorMap (X : SplitObject C) {X' Z : C}
    (f : X.source ⟶ X') (g : X.source ⟶ Z) (h : RetractArrow f g)
    (hr : h.r.left = 𝟙 X.source) [HasPushout g X.inclusion] :
    X ⟶ successorObject X f g h hr where
  left := f
  right := pushout.inr g X.inclusion
  inclusion_naturality := by
    have hi : h.i.left = 𝟙 X.source := by
      have hleft := h.retract_left
      change h.i.left ≫ h.r.left = 𝟙 X.source at hleft
      rw [hr] at hleft
      exact (Category.comp_id h.i.left).symm.trans hleft
    have hfj : f ≫ h.i.right = g := by
      have hw := h.i_w
      change h.i.left ≫ g = f ≫ h.i.right at hw
      rw [hi] at hw
      exact hw.symm.trans (Category.id_comp g)
    change X.inclusion ≫ pushout.inr g X.inclusion =
      f ≫ (h.i.right ≫ pushout.inl g X.inclusion)
    rw [← Category.assoc, hfj]
    exact pushout.condition.symm
  retraction_naturality := by
    change X.retraction ≫ f =
      pushout.inr g X.inclusion ≫ pushout.desc h.r.right (X.retraction ≫ f) _
    rw [pushout.inr_desc]

/-- The entire actual successor target map is a cobase change of the selected g. -/
theorem successorMap_right_mem (P : MorphismProperty C) (X : SplitObject C)
    {X' Z : C} (f : X.source ⟶ X') (g : X.source ⟶ Z) (h : RetractArrow f g)
    (hr : h.r.left = 𝟙 X.source) [HasPushout g X.inclusion] (hg : P g) :
    P.pushouts (successorMap X f g h hr).right :=
  P.pushouts_mk (IsPushout.of_hasPushout g X.inclusion).flip hg

end CategoryTheory.SmallObject.CoherentRetracts.SplitObject

namespace CategoryTheory.SmallObject.CoherentRetracts.SplitObject

variable {C : Type u} [Category.{v} C]

/-- The two actual successor squares paste into the original representative's cobase change. -/
theorem originalSuccessorPushout (X : SplitObject C) {X' A B : C}
    (f : X.source ⟶ X') (k : A ⟶ B) (R : RetractArrow f k)
    [HasPushout R.r.left k]
    [HasPushout (ArrowRetractRootNormalization.root R) X.inclusion] :
    IsPushout (R.r.left ≫ X.inclusion) k
      (successorMap X f (ArrowRetractRootNormalization.root R)
        (ArrowRetractRootNormalization.arrowRetract R) (by rfl)).right
      (ArrowRetractRootNormalization.oldTargetMap R ≫
        pushout.inl (ArrowRetractRootNormalization.root R) X.inclusion) :=
  (IsPushout.of_hasPushout R.r.left k).paste_horiz
    (IsPushout.of_hasPushout (ArrowRetractRootNormalization.root R) X.inclusion).flip

/-- The original representative's membership gives the actual successor's pushout membership. -/
theorem originalSuccessor_mem (P : MorphismProperty C) (X : SplitObject C) {X' A B : C}
    (f : X.source ⟶ X') (k : A ⟶ B) (R : RetractArrow f k)
    [HasPushout R.r.left k]
    [HasPushout (ArrowRetractRootNormalization.root R) X.inclusion] (hk : P k) :
    P.pushouts (successorMap X f (ArrowRetractRootNormalization.root R)
      (ArrowRetractRootNormalization.arrowRetract R) (by rfl)).right :=
  P.pushouts_mk (originalSuccessorPushout X f k R) hk

end CategoryTheory.SmallObject.CoherentRetracts.SplitObject
