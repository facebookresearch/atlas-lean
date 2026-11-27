/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeRelativeCells

/-! # Whole original native occurrence, root, square and function owner -/

@[expose] public section

noncomputable section

universe w t v u

namespace MathlibExtTest.CategoryTheory.SmallObject.NativeRelativeCells

open _root_.CategoryTheory _root_.CategoryTheory.Limits HomotopicalAlgebra
open _root_.CategoryTheory.SmallObject.NativeRelativeCells

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : Type t} {s : α → Arrow C} {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : J) (i : α) => (s i).hom) f)

theorem originalOccurrenceOrder (a b : c.Cells) :
    a ≤ b ↔ a = b ∨ a.j < b.j := occurrence_le_iff c a b

theorem originalStrictOrder (a b : c.Cells) : a < b ↔ a.j < b.j := occurrence_lt_iff c a b

theorem simultaneousCellsRemainIncomparable {a b : c.Cells}
    (hstage : a.j = b.j) (hne : a ≠ b) : ¬ a ≤ b := by
  intro h
  rcases (occurrence_le_iff c a b).1 h with h | h
  · exact hne h
  · exact (lt_irrefl a.j) (hstage ▸ h)

theorem originalOccurrenceWellFounded : WellFounded ((· < ·) : c.Cells → c.Cells → Prop) :=
  occurrence_wellFounded c

theorem everyEarlierNativeCell (a : c.Cells) :
    LowerSet.Iio a = before c a.j := predecessor_eq_before c a

theorem originalRootFunction :
    (fun j : J => (rootNatTrans c).app j) =
      (fun j : J => c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : J) ≤ j))) := rfl

theorem wholeNativeStageFunctor : stageDiagram c ⋙ Under.forget X = c.F := rfl

theorem originalRootCompatibility {j k : J} (h : j ≤ k) :
    rootMap c j ≫ c.F.map (homOfLE h) = rootMap c k := rootMap_map c h

theorem originalEndpointRoot (j : J) : rootMap c j ≫ c.incl.app j = f := rootMap_incl c j

theorem originalEndpointPoint : (nativeEndpointCocone c).pt = Under.mk f := rfl

/-- The original native endpoint UP is genuine data, retained under its same root. -/
def originalEndpointUP : IsColimit (nativeEndpointCocone c) := nativeEndpointIsColimit c

theorem originalIndividualSquare (a : c.Cells) :
    nativeAttaching c a ≫ c.F.map (homOfLE (Order.le_succ a.j)) =
      (s a.i).hom ≫ nativeCell c a := native_square c a

variable [HasPushouts C]

theorem originalVertexRoot (a : c.Cells) :
    (vertex c a).hom = rootMap c a.j ≫
      pushout.inl (nativeAttaching c a) (s a.i).hom := rfl

theorem everyNativeStageLeg (a : c.Cells) (j : J) (h : Order.succ a.j ≤ j) :
    stageToVertex c a ≫ vertexToStage c a j h =
      stageMap c ((Order.le_succ a.j).trans h) := stageToVertex_toStage c a j h

theorem everyNativeCellLeg (a : c.Cells) (j : J) (h : Order.succ a.j ≤ j) :
    vertexCell c a ≫ (vertexToStage c a j h).right =
      (c.attachCells a.j a.hj).cell a.k ≫ c.F.map (homOfLE h) :=
  vertexCell_toStage c a j h

theorem allNativeComparisonComposites (a : c.Cells) (j k : J)
    (haj : Order.succ a.j ≤ j) (hjk : j ≤ k) :
    vertexToStage c a j haj ≫ stageMap c hjk = vertexToStage c a k (haj.trans hjk) :=
  vertexToStage_comp c a j k haj hjk

theorem wholeOccurrenceMapFunction :
    (fun (a b : c.Cells) (h : a ≤ b) => (diagram c).map (homOfLE h)) =
      (fun (a b : c.Cells) (h : a ≤ b) => vertexMap c h) := rfl

theorem wholeOccurrenceIdentity (a : c.Cells) :
    (diagram c).map (𝟙 a) = 𝟙 (vertex c a) := (diagram c).map_id a

theorem wholeOccurrenceComposition {a b d : c.Cells} (h : a ⟶ b) (k : b ⟶ d) :
    (diagram c).map (h ≫ k) = (diagram c).map h ≫ (diagram c).map k :=
  (diagram c).map_comp h k

theorem allEarlierOccurrenceNaturality {a b : c.Cells} (h : a ≤ b) (j : J) (hb : b.j < j) :
    vertexMap c h ≫ vertexToStage c b j (Order.succ_le_of_lt hb) =
      vertexToStage c a j
        (Order.succ_le_of_lt ((occurrence_stage_monotone c h).trans_lt hb)) :=
  vertexMap_toStage c h j hb

theorem wholeOriginalCellInclusionFunction :
    (fun a : c.Cells => vertexCell c a ≫ (vertexIncl c a).right) =
      (fun a : c.Cells => a.ι) := by
  funext a
  exact vertexCell_incl c a

theorem wholeOriginalRootInclusion (a : c.Cells) :
    (vertex c a).hom ≫ (vertexIncl c a).right = f := Under.w (vertexIncl c a)

theorem completeOriginalEndpointNaturality {a b : c.Cells} (h : a ⟶ b) :
    (diagram c).map h ≫ (endpointCocone c).ι.app b = (endpointCocone c).ι.app a :=
  (endpointCocone c).w h

end MathlibExtTest.CategoryTheory.SmallObject.NativeRelativeCells
