/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Order.WithBot

/-!
# Complete a transfinite diagram at its original endpoint

The actual original diagram, maps, bottom isomorphism, continuous limit cocones
and endpoint universal property are retained on the shape with an added top.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v

section GenericCompletionDiagramResearchCanonicalPromotion

open CategoryTheory Limits MorphismProperty Opposite

namespace CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion

variable {C : Type u} [Category.{v} C]
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape O f)

/-- The added top is the actual original endpoint; every old object is unchanged. -/
def obj (a : WithTop O) : C := a.recTopCoe Y c.F.obj

/-- The completed diagram uses the actual original maps and original endpoint cocone legs. -/
def map (a b : WithTop O) (hab : a ≤ b) : obj c a ⟶ obj c b :=
  match a, b with
  | none, none => 𝟙 Y
  | none, some b => False.elim (WithTop.not_top_le_coe b hab)
  | some a, none => c.incl.app a
  | some a, some b => c.F.map (homOfLE (show a ≤ b from WithTop.coe_le_coe.mp hab))

theorem map_id (a : WithTop O) : map c a a le_rfl = 𝟙 (obj c a) := by
  cases a
  · rfl
  · exact c.F.map_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem map_comp (a b e : WithTop O) (hab : a ≤ b) (hbe : b ≤ e) :
    map c a b hab ≫ map c b e hbe = map c a e (hab.trans hbe) := by
  cases a with
  | top =>
    cases b with
    | top =>
      cases e with
      | top => exact Category.id_comp _
      | coe e => exact False.elim (WithTop.not_top_le_coe e hbe)
    | coe b => exact False.elim (WithTop.not_top_le_coe b hab)
  | coe a =>
    cases b with
    | top =>
      cases e with
      | top => exact Category.comp_id _
      | coe e => exact False.elim (WithTop.not_top_le_coe e hbe)
    | coe b =>
      cases e with
      | top =>
        change c.F.map (homOfLE (WithTop.coe_le_coe.mp hab)) ≫ c.incl.app b = c.incl.app a
        exact (Cocone.mk Y c.incl).w (homOfLE (WithTop.coe_le_coe.mp hab))
      | coe e =>
        change c.F.map _ ≫ c.F.map _ = c.F.map _
        rw [← c.F.map_comp]
        congr 1

/-- The exact original diagram completed at its own actual endpoint. -/
def diagram : WithTop O ⥤ C where
  obj := obj c
  map {a b} g := map c a b (leOfHom g)
  map_id a := map_id c a
  map_comp g k := (map_comp c _ _ _ (leOfHom g) (leOfHom k)).symm

theorem diagram_obj_coe (a : O) : (diagram c).obj (a : WithTop O) = c.F.obj a := rfl

theorem diagram_obj_top : (diagram c).obj ⊤ = Y := rfl

theorem diagram_map_coe {a b : O} (hab : a ≤ b) :
    (diagram c).map (homOfLE (WithTop.coe_le_coe.mpr hab)) = c.F.map (homOfLE hab) := rfl

theorem diagram_map_top (a : O) :
    (diagram c).map (homOfLE (le_top : (a : WithTop O) ≤ ⊤)) = c.incl.app a := rfl

/-- The old original root isomorphism is literal at the completed bottom. -/
def botIso : (diagram c).obj ⊥ ≅ X := c.isoBot

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The old original whole endpoint cocone, with identity at the actual added endpoint. -/
def endpointCocone : Cocone (diagram c) where
  pt := Y
  ι :=
    { app a := map c a ⊤ le_top
      naturality a b g := by
        change map c a b (leOfHom g) ≫ map c b ⊤ le_top = map c a ⊤ le_top ≫ 𝟙 Y
        exact (map_comp c a b ⊤ (leOfHom g) le_top).trans (Category.comp_id _).symm }

theorem endpointCocone_coe (a : O) : (endpointCocone c).ι.app (a : WithTop O) = c.incl.app a := rfl

theorem endpointCocone_top : (endpointCocone c).ι.app ⊤ = 𝟙 Y := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual added endpoint is terminal in the completed diagram. -/
def endpointIsColimit : IsColimit (endpointCocone c) where
  desc s := s.ι.app ⊤
  fac s a := by
    change map c a ⊤ le_top ≫ s.ι.app ⊤ = s.ι.app a
    exact s.w (homOfLE le_top)
  uniq s m hm := by
    have hmt := hm ⊤
    change 𝟙 Y ≫ m = s.ι.app ⊤ at hmt
    rw [Category.id_comp] at hmt
    exact hmt

/-- The actual original shape is precisely the strict prefix of the added top. -/
def topPrefixEquiv : O ≃o Set.Iio (⊤ : WithTop O) where
  toFun a := ⟨(a : WithTop O), WithTop.coe_lt_top a⟩
  invFun a := a.1.untop (ne_of_lt a.2)
  left_inv a := rfl
  right_inv a := by
    rcases a with ⟨a, ha⟩
    cases a
    · exact False.elim (lt_irrefl _ (show (⊤ : WithTop O) < ⊤ from ha))
    · rfl
  map_rel_iff' := WithTop.coe_le_coe

/-- Each original strict stage prefix is literal in the completed diagram. -/
def coePrefixEquiv (a : O) : Set.Iio a ≃o Set.Iio (a : WithTop O) where
  toFun b := ⟨(b.1 : WithTop O), WithTop.coe_lt_coe.mpr b.2⟩
  invFun b := by
    rcases b with ⟨b, hb⟩
    cases b with
    | top => exact False.elim (WithTop.not_top_lt (a : WithTop O) (show (⊤ : WithTop O) <
      a from hb))
    | coe b => exact ⟨b, WithTop.coe_lt_coe.mp (show (b : WithTop O) < a from hb)⟩
  left_inv b := rfl
  right_inv b := by
    rcases b with ⟨b, hb⟩
    cases b
    · exact False.elim (WithTop.not_top_lt (a : WithTop O) (show (⊤ : WithTop O) < a from hb))
    · rfl
  map_rel_iff' := WithTop.coe_le_coe

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Original limit cocones and the actual original endpoint cocone give completed continuity. -/
theorem continuous : (diagram c).IsWellOrderContinuous where
  nonempty_isColimit a ha := by
    cases a with
    | top =>
      apply Nonempty.intro
      apply IsColimit.ofWhiskerEquivalence (topPrefixEquiv (O := O)).equivalence
      exact c.isColimit
    | coe a =>
      apply Nonempty.intro
      apply IsColimit.ofWhiskerEquivalence (coePrefixEquiv (O := O) a).equivalence
      exact c.F.isColimitOfIsWellOrderContinuous a (WithTop.isSuccLimit_coe_iff.mp ha)

/-- The original endpoint leg at an actual original maximal stage is genuinely invertible. -/
theorem originalMaxEndpoint_isIso (a : O) (ha : IsMax a) : IsIso (c.incl.app a) := by
  apply c.isColimit.isIso_ι_app_of_isTerminal
  refine IsTerminal.ofUniqueHom (fun b => homOfLE (by
    obtain h | h := le_total b a
    · exact h
    · exact ha h)) (fun _ _ => Subsingleton.elim _ _)

/-- The completed transfinite composition retains the same original arrow and root. -/
def shape : TransfiniteCompositionOfShape (WithTop O) f where
  F := diagram c
  isoBot := botIso c
  isWellOrderContinuous := continuous c
  incl := (endpointCocone c).ι
  isColimit := endpointIsColimit c
  fac := c.fac

theorem shape_functor : (shape c).F = diagram c := rfl

theorem shape_isoBot : (shape c).isoBot = c.isoBot := rfl

theorem shape_incl_coe (a : O) : (shape c).incl.app (a : WithTop O) = c.incl.app a := rfl

theorem shape_incl_top : (shape c).incl.app ⊤ = 𝟙 Y := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The top-prefix colimit is the actual unchanged original endpoint colimit. -/
def topPrefixIsColimit : IsColimit ((Set.principalSegIio (⊤ : WithTop O)).cocone (diagram c)) := by
  apply IsColimit.ofWhiskerEquivalence (topPrefixEquiv (O := O)).equivalence
  exact c.isColimit

end CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion

end GenericCompletionDiagramResearchCanonicalPromotion
