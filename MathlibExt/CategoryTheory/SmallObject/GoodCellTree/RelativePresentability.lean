/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.UnderColimits
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Relative presentability of original bounded cell slices

The induction uses the original predecessor colimit and original cell
pushout at every occurrence. Bounded chosen lower pieces are presentable
under the same arbitrary root. The root is not assumed presentable.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u

namespace CategoryTheory.SmallObject.RelativeCellPresentability

open CategoryTheory.Limits LowerSetColimits UnderColimits

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- The same actual pushout of three presentable source objects is presentable. -/
theorem ofPushout {A B U V : C} {a : A ⟶ U} {s : A ⟶ B}
    {p : U ⟶ V} {b : B ⟶ V} (hs : IsPushout a s p b)
    [IsCardinalPresentable A κ] [IsCardinalPresentable B κ]
    [IsCardinalPresentable U κ] : IsCardinalPresentable V κ := by
  have (i : WalkingSpan) : IsCardinalPresentable ((span a s).obj i) κ := by
    cases i with
    | none => exact ‹IsCardinalPresentable A κ›
    | some i =>
      cases i with
      | left => exact ‹IsCardinalPresentable U κ›
      | right => exact ‹IsCardinalPresentable B κ›
  exact isCardinalPresentable_of_isColimit hs.cocone hs.isColimit κ
    (hasCardinalLT_of_finite (Arrow WalkingSpan) κ (Fact.out : κ.IsRegular).aleph0_le)

variable [HasBinaryCoproducts C]
  {P : Type w} [PartialOrder P] {α : Type t} {s : α → Arrow C} {X : C}

/-- Every original good-tree vertex is presentable relative to the same arbitrary root. -/
theorem vertex (T : CellTree s X (P := P)) (h : T.IsGood κ) (a : P) :
    IsCardinalPresentable (T.vertex a) κ := by
  let : LocallySmall.{w} (Under X) := locallySmall_of_faithful (Under.forget X)
  refine T.wellFounded.induction
    (C := fun b : P => IsCardinalPresentable (T.vertex b) κ) a ?_
  intro a ih
  have (b : LowerSet.Iio a) :
      IsCardinalPresentable ((restriction T.diagram (LowerSet.Iio a)).obj b) κ :=
    ih b.1 b.2
  have hPred : IsCardinalPresentable (T.predecessorObj a) κ :=
    isCardinalPresentable_of_isColimit (T.predecessor a).cocone
      (T.predecessor a).isColimit κ (CellTree.IsGood.predecessor_arrow_lt T h a)
  let : IsCardinalPresentable (T.predecessorObj a) κ := hPred
  let : IsCardinalPresentable (s (T.label a)).left κ := h.presentable_source a
  let : IsCardinalPresentable (s (T.label a)).right κ := h.presentable_target a
  let : IsCardinalPresentable ((Under.costar X).obj (s (T.label a)).left) κ :=
    costarPresentable κ (s (T.label a)).left
  let : IsCardinalPresentable ((Under.costar X).obj (s (T.label a)).right) κ :=
    costarPresentable κ (s (T.label a)).right
  exact ofPushout κ (treeFreePushout T a)

/-- Any actual bounded lower colimit is presentable under the original root. -/
theorem lower (T : CellTree s X (P := P)) (h : T.IsGood κ)
    (B : LowerSet P) (c : ColimitCocone (restriction T.diagram B))
    (hB : HasCardinalLT (B : Set P) κ) :
    IsCardinalPresentable c.cocone.pt κ := by
  let : LocallySmall.{w} (Under X) := locallySmall_of_faithful (Under.forget X)
  have (a : B) : IsCardinalPresentable ((restriction T.diagram B).obj a) κ :=
    vertex κ T h a.1
  exact isCardinalPresentable_of_isColimit c.cocone c.isColimit κ
    ((hasCardinalLT_arrow_iff_of_isThin (B : Set P) κ
      (Fact.out : κ.IsRegular).aleph0_le).2 hB)

/-- The recorded whole endpoint is presentable under the stated total-label bound. -/
theorem endpoint (T : CellTree s X (P := P)) (h : T.IsGood κ)
    (hP : HasCardinalLT P κ) : IsCardinalPresentable T.endpointObj κ := by
  let : LocallySmall.{w} (Under X) := locallySmall_of_faithful (Under.forget X)
  have (a : P) : IsCardinalPresentable (T.diagram.obj a) κ := vertex κ T h a
  exact isCardinalPresentable_of_isColimit T.endpoint.cocone T.endpoint.isColimit κ
    ((hasCardinalLT_arrow_iff_of_isThin P κ
      (Fact.out : κ.IsRegular).aleph0_le).2 hP)

/-- Every given all-lower family keeps its original object and colimit dictionary. -/
theorem selectedLower (T : CellTree s X (P := P)) (h : T.IsGood κ)
    (L : LowerSetColimitData T.diagram) (B : LowerSet P)
    (hB : HasCardinalLT (B : Set P) κ) :
    IsCardinalPresentable (L.obj B) κ :=
  lower κ T h B ⟨L.cocone B, L.isColimit B⟩ hB

/-- The convenience lower family uses exactly the same existing original cocones. -/
theorem lowerData [HasColimitsOfSize.{w, w} C]
    (T : CellTree s X (P := P)) (h : T.IsGood κ) (B : LowerSet P)
    (hB : HasCardinalLT (B : Set P) κ) :
    IsCardinalPresentable (T.lowerData.obj B) κ :=
  selectedLower κ T h T.lowerData B hB

end CategoryTheory.SmallObject.RelativeCellPresentability
