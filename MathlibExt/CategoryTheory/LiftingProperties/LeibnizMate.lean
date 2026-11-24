/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Leibniz adjunctions from mate transformations

A natural transformation `α : F₀ ⟶ F₁` induces a functor on arrow categories
whose value at `u : A ⟶ B` is the pushout corner
`F₀ B ⨿_{F₀ A} F₁ A ⟶ F₁ B`. Dually, `β : G₁ ⟶ G₀` induces the pullback
corner `G₁ X ⟶ G₀ X ×_{G₀ Y} G₁ Y`. This is Mathlib's pullback
factor order; Joyal prints the canonically symmetric pullback with the two
factors reversed.

When `F₀ ⊣ G₀`, `F₁ ⊣ G₁`, and `β` is the conjugate mate of `α`, the two
corner functors are adjoint. The induced equivalence of commutative squares
restricts to an equivalence of diagonal fillers and therefore preserves and
reflects lifting properties. This is Joyal's Lemma D.1.15.

The implementation packages the two adjunctions once as an internal,
non-exposed walking-arrow parametrized adjunction. Its mate condition is
discharged by `CategoryTheory.conjugateEquiv`; the public API contains no
second notion of mates. Caller-supplied `PushoutObjObj` and `PullbackObjObj` packets are
supported alongside the canonical functorial corners.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

-- These local reducibility overrides are used only to compare Mathlib's two
-- presentations of the same chosen pushout and pullback corners. They do not
-- alter any exported declaration.
set_option allowUnsafeReducibility true in
attribute [local reducible]
  Limits.getColimitCocone Limits.getLimitCone
  Functor.leibnizPushout Functor.leibnizPullback
  Functor.PushoutObjObj.ofHasPushout Functor.PullbackObjObj.ofHasPullback

namespace Functor.LeibnizAdjunction

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's explicit square equivalence for a parametrized adjunction is the
Hom equivalence of its Leibniz adjunction. -/
lemma arrowHomEquiv_apply_eq_homEquiv
    (adj₂ : F ⊣₂ G) {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁)
    [HasPullbacks C₂] [HasPushouts C₃]
    {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)
    {X₃ Y₃ : C₃} (f₃ : X₃ ⟶ Y₃)
    (sq : Arrow.mk (Functor.PushoutObjObj.ofHasPushout F f₁ f₂).ι ⟶
      Arrow.mk f₃) :
    adj₂.arrowHomEquiv
        (Functor.PushoutObjObj.ofHasPushout F f₁ f₂)
        (Functor.PullbackObjObj.ofHasPullback G f₁ f₃) sq =
      (Functor.LeibnizAdjunction.adj F G adj₂ (Arrow.mk f₁)).homEquiv
        (Arrow.mk f₂) (Arrow.mk f₃) sq := by
  apply Arrow.hom_ext
  · dsimp [ParametrizedAdjunction.arrowHomEquiv, Adjunction.homEquiv]
    exact adj₂.homEquiv_naturality_three sq.left _
  · dsimp [ParametrizedAdjunction.arrowHomEquiv, Adjunction.homEquiv]
    apply pullback.hom_ext
    · simp [← ParametrizedAdjunction.homEquiv_naturality_three]
    · simp [← ParametrizedAdjunction.homEquiv_naturality_three]

end Functor.LeibnizAdjunction

namespace NatTrans

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ C}

/-- The pushout corner of a natural transformation, functorial in arrows.
At `u : A ⟶ B`, its underlying map is
`F₀ B ⨿_{F₀ A} F₁ A ⟶ F₁ B`. -/
noncomputable def leibnizPushout (α : F₀ ⟶ F₁) [HasPushouts D] :
    Arrow C ⥤ Arrow D :=
  (parallelPair α α).leibnizPushout.obj
    (Arrow.mk WalkingParallelPairHom.left)

@[simp]
lemma leibnizPushout_obj_left (α : F₀ ⟶ F₁) [HasPushouts D]
    (u : Arrow C) :
    ((leibnizPushout α).obj u).left =
      pushout (α.app u.left) (F₀.map u.hom) := rfl

@[simp]
lemma leibnizPushout_obj_right (α : F₀ ⟶ F₁) [HasPushouts D]
    (u : Arrow C) :
    ((leibnizPushout α).obj u).right = F₁.obj u.right := rfl

@[simp]
lemma leibnizPushout_obj_hom (α : F₀ ⟶ F₁) [HasPushouts D]
    (u : Arrow C) :
    ((leibnizPushout α).obj u).hom =
      pushout.desc (F₁.map u.hom) (α.app u.right) (by simp) := rfl

/-- The pullback corner of a natural transformation, functorial in arrows.
At `p : X ⟶ Y`, its underlying map is
`G₁ X ⟶ G₀ X ×_{G₀ Y} G₁ Y`. Joyal writes the canonically symmetric
pullback in the reverse factor order. -/
noncomputable def leibnizPullback (β : G₁ ⟶ G₀) [HasPullbacks C] :
    Arrow D ⥤ Arrow C :=
  (walkingParallelPairOp.leftOp ⋙ parallelPair β β).leibnizPullback.obj
    (op (Arrow.mk WalkingParallelPairHom.left))

@[simp]
lemma leibnizPullback_obj_left (β : G₁ ⟶ G₀) [HasPullbacks C]
    (p : Arrow D) :
    ((leibnizPullback β).obj p).left = G₁.obj p.left := rfl

@[simp]
lemma leibnizPullback_obj_right (β : G₁ ⟶ G₀) [HasPullbacks C]
    (p : Arrow D) :
    ((leibnizPullback β).obj p).right =
      pullback (G₀.map p.hom) (β.app p.right) := rfl

@[simp]
lemma leibnizPullback_obj_hom (β : G₁ ⟶ G₀) [HasPullbacks C]
    (p : Arrow D) :
    ((leibnizPullback β).obj p).hom =
      pullback.lift (β.app p.left) (G₁.map p.hom) (by simp) := rfl

end NatTrans

namespace Adjunction

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ C}

/-- Transposition across conjugate adjunctions commutes with the mate square. -/
lemma homEquiv_comp_conjugateEquiv
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {X : C} {Y : D} (f : F₁.obj X ⟶ Y) :
    adj₀.homEquiv X Y (α.app X ≫ f) =
      adj₁.homEquiv X Y f ≫ (conjugateEquiv adj₁ adj₀ α).app Y := by
  change adj₀.unit.app X ≫ G₀.map (α.app X ≫ f) =
    (adj₁.unit.app X ≫ G₁.map f) ≫
      (conjugateEquiv adj₁ adj₀ α).app Y
  rw [G₀.map_comp]
  conv_rhs =>
    rw [Category.assoc, (conjugateEquiv adj₁ adj₀ α).naturality f,
      ← Category.assoc]
  rw [unit_conjugateEquiv adj₁ adj₀ α]
  simp only [Category.assoc]

end Adjunction

namespace LeibnizMate.Internal

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ C}

/-- The walking-arrow parametrized adjunction underlying the Leibniz mate API. -/
@[no_expose]
noncomputable def parametrizedAdjunction
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁) :
    parallelPair α α ⊣₂
      walkingParallelPairOp.leftOp ⋙
        parallelPair (conjugateEquiv adj₁ adj₀ α)
          (conjugateEquiv adj₁ adj₀ α) :=
  ParametrizedAdjunction.mk'
    (fun j => WalkingParallelPair.casesOn j adj₀ adj₁)
    (by
      intro X Y f A B g
      cases f with
      | left => exact Adjunction.homEquiv_comp_conjugateEquiv adj₀ adj₁ α g
      | right => exact Adjunction.homEquiv_comp_conjugateEquiv adj₀ adj₁ α g
      | id X => cases X <;> simp)

end LeibnizMate.Internal

namespace Arrow

variable {C : Type u₁} [Category.{v₁} C]

/-- Postcomposition by an isomorphism of right-hand arrows preserves the
type of diagonal fillers of a commutative square. -/
def liftStructPostcompIsoEquiv {f g g' : Arrow C}
    (sq : f ⟶ g) (e : g ≅ g') :
    Arrow.LiftStruct sq ≃ Arrow.LiftStruct (sq ≫ e.hom) where
  toFun l :=
    { l := l.l ≫ e.hom.left
      fac_left := by
        rw [← Category.assoc, l.fac_left]
        rfl
      fac_right := by
        rw [Category.assoc, e.hom.w, ← Category.assoc, l.fac_right]
        rfl }
  invFun l :=
    { l := l.l ≫ e.inv.left
      fac_left := by
        rw [← Category.assoc, l.fac_left]
        change (sq.left ≫ e.hom.left) ≫ e.inv.left = sq.left
        simp
      fac_right := by
        rw [Category.assoc, e.inv.w, ← Category.assoc, l.fac_right]
        change (sq.right ≫ e.hom.right) ≫ e.inv.right = sq.right
        simp }
  left_inv l := by
    ext
    simp [Category.assoc]
  right_inv l := by
    ext
    simp [Category.assoc]

end Arrow

namespace Adjunction

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ C}

/-- The square equivalence for caller-supplied pushout and pullback corner
packets. This is the choice-independent form of Joyal's D.1.15. -/
noncomputable def leibnizMateArrowHomEquivOf
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p) :
    (Arrow.mk sqL.ι ⟶ Arrow.mk p) ≃
      (Arrow.mk u ⟶ Arrow.mk sqR.π) :=
  (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α).arrowHomEquiv
    sqL sqR

/-- The left component of the caller-supplied Leibniz mate square is the
`adj₁` transpose of the first pushout coprojection followed by the original
top map. -/
@[simp]
lemma leibnizMateArrowHomEquivOf_apply_left
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq).left =
      adj₁.homEquiv _ _ (sqL.inl ≫ sq.left) := by
  exact ParametrizedAdjunction.arrowHomEquiv_apply_left
    (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α)
    sqL sqR sq

/-- The first pullback component of the caller-supplied Leibniz mate square
is the `adj₀` transpose of the second pushout coprojection followed by the
original top map. -/
@[reassoc (attr := simp)]
lemma leibnizMateArrowHomEquivOf_apply_right_fst
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq).right ≫ sqR.fst =
      adj₀.homEquiv _ _ (sqL.inr ≫ sq.left) := by
  exact ParametrizedAdjunction.arrowHomEquiv_apply_right_fst
    (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α)
    sqL sqR sq

/-- The second pullback component of the caller-supplied Leibniz mate square
is the `adj₁` transpose of the original bottom map. -/
@[reassoc (attr := simp)]
lemma leibnizMateArrowHomEquivOf_apply_right_snd
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq).right ≫ sqR.snd =
      adj₁.homEquiv _ _ sq.right := by
  exact ParametrizedAdjunction.arrowHomEquiv_apply_right_snd
    (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α)
    sqL sqR sq

/-- The equivalence of diagonal fillers for caller-supplied corner packets. -/
noncomputable def leibnizMateLiftStructEquivOf
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {A B : C} {u : A ⟶ B} {X Y : D} {p : X ⟶ Y}
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p)
    (sq : Arrow.mk sqL.ι ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct
        (leibnizMateArrowHomEquivOf adj₀ adj₁ α u p sqL sqR sq) :=
  (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α).liftStructEquiv
    sqL sqR sq

/-- Lifting properties correspond for caller-supplied corner packets. -/
theorem leibnizMate_hasLiftingProperty_iff_of
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    {A B : C} {u : A ⟶ B} {X Y : D} {p : X ⟶ Y}
    (sqL : (parallelPair α α).PushoutObjObj
      WalkingParallelPairHom.left u)
    (sqR : (walkingParallelPairOp.leftOp ⋙
      parallelPair (conjugateEquiv adj₁ adj₀ α)
        (conjugateEquiv adj₁ adj₀ α)).PullbackObjObj
          WalkingParallelPairHom.left p) :
    HasLiftingProperty sqL.ι p ↔ HasLiftingProperty u sqR.π :=
  (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α).hasLiftingProperty_iff
    sqL sqR

/-- Conjugate natural transformations between two adjunctions induce an
adjunction between their pushout and pullback corner functors. -/
noncomputable def leibnizMateAdjunction
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    [HasPushouts D] [HasPullbacks C] :
    NatTrans.leibnizPushout α ⊣
      NatTrans.leibnizPullback (conjugateEquiv adj₁ adj₀ α) :=
  Functor.LeibnizAdjunction.adj _ _
    (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α)
    (Arrow.mk WalkingParallelPairHom.left)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural equivalence between commutative squares induced by conjugate
transformations between two adjunctions. -/
noncomputable def leibnizMateArrowHomEquiv
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    [HasPushouts D] [HasPullbacks C] (u : Arrow C) (p : Arrow D) :
    ((NatTrans.leibnizPushout α).obj u ⟶ p) ≃
      (u ⟶ (NatTrans.leibnizPullback
        (conjugateEquiv adj₁ adj₀ α)).obj p) :=
  (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u p

@[simp]
lemma leibnizMateArrowHomEquiv_eq_homEquiv
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    [HasPushouts D] [HasPullbacks C] (u : Arrow C) (p : Arrow D) :
    leibnizMateArrowHomEquiv adj₀ adj₁ α u p =
      (leibnizMateAdjunction adj₀ adj₁ α).homEquiv u p := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The caller-supplied square equivalence at the canonical corner packets is
pointwise equal to the Hom equivalence of `leibnizMateAdjunction`. -/
@[simp]
lemma leibnizMateArrowHomEquivOf_canonical_apply
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    [HasPushouts D] [HasPullbacks C]
    {A B : C} (u : A ⟶ B) {X Y : D} (p : X ⟶ Y)
    (sq : Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (parallelPair α α) WalkingParallelPairHom.left u).ι ⟶ Arrow.mk p) :
    leibnizMateArrowHomEquivOf adj₀ adj₁ α u p
        (Functor.PushoutObjObj.ofHasPushout
          (parallelPair α α) WalkingParallelPairHom.left u)
        (Functor.PullbackObjObj.ofHasPullback
          (walkingParallelPairOp.leftOp ⋙
            parallelPair (conjugateEquiv adj₁ adj₀ α)
              (conjugateEquiv adj₁ adj₀ α))
          WalkingParallelPairHom.left p) sq =
      leibnizMateArrowHomEquiv adj₀ adj₁ α (Arrow.mk u) (Arrow.mk p) sq :=
  Functor.LeibnizAdjunction.arrowHomEquiv_apply_eq_homEquiv
    (LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α)
      WalkingParallelPairHom.left u p sq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between diagonal fillers induced by the Leibniz mate
square equivalence. -/
noncomputable def leibnizMateLiftStructEquiv
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    [HasPushouts D] [HasPullbacks C] {u : Arrow C} {p : Arrow D}
    (sq : (NatTrans.leibnizPushout α).obj u ⟶ p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct
        (leibnizMateArrowHomEquiv adj₀ adj₁ α u p sq) :=
  by
    let F : WalkingParallelPair ⥤ C ⥤ D := parallelPair α α
    let G : WalkingParallelPairᵒᵖ ⥤ D ⥤ C :=
      walkingParallelPairOp.leftOp ⋙
        parallelPair (conjugateEquiv adj₁ adj₀ α)
          (conjugateEquiv adj₁ adj₀ α)
    let adj₂ : F ⊣₂ G :=
      LeibnizMate.Internal.parametrizedAdjunction adj₀ adj₁ α
    let sqL := Functor.PushoutObjObj.ofHasPushout
      F WalkingParallelPairHom.left u.hom
    let sqR := Functor.PullbackObjObj.ofHasPullback
      G WalkingParallelPairHom.left p.hom
    change Arrow.mk sqL.ι ⟶ Arrow.mk p.hom at sq
    let e := adj₂.liftStructEquiv sqL sqR sq
    have hsq : adj₂.arrowHomEquiv sqL sqR sq =
        leibnizMateArrowHomEquiv adj₀ adj₁ α u p sq := by
      change adj₂.arrowHomEquiv sqL sqR sq =
        ((Functor.LeibnizAdjunction.adj F G adj₂
          (Arrow.mk WalkingParallelPairHom.left)).homEquiv
            (Arrow.mk u.hom) (Arrow.mk p.hom)) sq
      exact Functor.LeibnizAdjunction.arrowHomEquiv_apply_eq_homEquiv
        adj₂ WalkingParallelPairHom.left u.hom p.hom sq
    exact e.trans (Equiv.cast (congrArg Arrow.LiftStruct hsq))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Leibniz mate construction preserves and reflects the lifting
property. -/
theorem leibnizMate_hasLiftingProperty_iff
    (adj₀ : F₀ ⊣ G₀) (adj₁ : F₁ ⊣ G₁) (α : F₀ ⟶ F₁)
    [HasPushouts D] [HasPullbacks C] (u : Arrow C) (p : Arrow D) :
    HasLiftingProperty (NatTrans.leibnizPushout α |>.obj u |>.hom) p.hom ↔
      HasLiftingProperty u.hom
        (NatTrans.leibnizPullback (conjugateEquiv adj₁ adj₀ α) |>.obj p |>.hom) :=
  by
    simp only [Arrow.hasLiftingProperty_iff]
    constructor
    · intro h sq
      obtain ⟨sq', rfl⟩ :=
        (leibnizMateArrowHomEquiv adj₀ adj₁ α u p).surjective sq
      exact ⟨leibnizMateLiftStructEquiv adj₀ adj₁ α sq'
        (h sq').some⟩
    · intro h sq
      exact ⟨(leibnizMateLiftStructEquiv adj₀ adj₁ α sq).symm
        (h _).some⟩

end Adjunction

end CategoryTheory
