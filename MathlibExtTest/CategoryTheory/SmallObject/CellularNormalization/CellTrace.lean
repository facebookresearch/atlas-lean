/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.CellTrace

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w w' ν u v t

open CategoryTheory Limits HomotopicalAlgebra
open CategoryTheory.SmallObject.CellularNormalization

namespace OriginalCellTraceClient

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
  {α : J → Type t} {A B : ∀ j, α j → C} (g : ∀ j i, A j i ⟶ B j i)
  {X Y : C} {f : X ⟶ Y} (outer : TransfiniteCompositionOfShape J f)
  (c : ∀ j, RelativeCellComplex.{ν} (fun _ : K j => g j)
    (outer.F.map (homOfLE (Order.le_succ j))))
  (emptySource : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (emptyTarget : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)))
  (hSource : IsColimit emptySource) (hTarget : IsColimit emptyTarget)

local instance clientFlatWF : WellFoundedLT (Index K) := lexWellFounded
/-- The original flattened successor order used by the occurrence and endpoint clients. -/
local instance clientFlatSucc : SuccOrder (Index K) := flatSuccOrder

/-- The actual normalization of the supplied original histories and their empty cofans. -/
abbrev actualNormalized := normalizeRelativeCells g outer c emptySource emptyTarget hSource hTarget

/-- The literal original occurrence selected by the canonical normalized-cell trace. -/
def actualOriginalOccurrence
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells) :
    UsedCells g outer.F c :=
  CellTrace.originalCell g outer c emptySource emptyTarget hSource hTarget a

theorem original_outer_index
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (actualOriginalOccurrence g outer c emptySource emptyTarget hSource hTarget a).1 =
      (ofLex a.j).1 :=
  CellTrace.originalCell_outerIndex g outer c emptySource emptyTarget hSource hTarget a

theorem original_inner_stage
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (actualOriginalOccurrence g outer c emptySource emptyTarget hSource hTarget a).2.j =
      (ofLex a.j).2 :=
  CellTrace.originalCell_innerStage g outer c emptySource emptyTarget hSource hTarget a

theorem original_generating_label
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (actualOriginalOccurrence g outer c emptySource emptyTarget hSource hTarget a).2.i = a.i :=
  CellTrace.originalCell_label g outer c emptySource emptyTarget hSource hTarget a

theorem genuine_inner_stage
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells) :
    ¬ IsMax (ofLex a.j).2 :=
  CellTrace.normalizedCell_inner_notMax g outer c emptySource emptyTarget hSource hTarget a

theorem original_endpoint_map
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells) :
    a.ι = eqToHom (congrArg (B (ofLex a.j).1)
      (original_generating_label g outer c emptySource emptyTarget hSource hTarget a)).symm ≫
      (actualOriginalOccurrence g outer c emptySource emptyTarget hSource hTarget a).2.ι ≫
        outer.incl.app (Order.succ (ofLex a.j).1) :=
  CellTrace.originalCell_endpoint g outer c emptySource emptyTarget hSource hTarget a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem original_endpoint_after_map
    (a : (actualNormalized g outer c emptySource emptyTarget hSource hTarget).Cells)
    {Z : C} (h : Y ⟶ Z) :
    a.ι ≫ h = eqToHom (congrArg (B (ofLex a.j).1)
      (original_generating_label g outer c emptySource emptyTarget hSource hTarget a)).symm ≫
      (actualOriginalOccurrence g outer c emptySource emptyTarget hSource hTarget a).2.ι ≫
        outer.incl.app (Order.succ (ofLex a.j).1) ≫ h := by
  simpa only [Category.assoc] using congrArg (fun q => q ≫ h)
    (original_endpoint_map g outer c emptySource emptyTarget hSource hTarget a)

theorem greatest_inner_has_no_occurrence (j : J) (k : K j)
    (ha : ¬ IsMax (vertex j k)) (hk : IsMax k) :
    ((actualNormalized g outer c emptySource emptyTarget hSource hTarget).attachCells
      (vertex j k) ha).ι = PEmpty.{ν + 1} :=
  CellTrace.normalizedAttachment_empty g outer c emptySource emptyTarget hSource hTarget j k ha hk

theorem same_original_source_arrow :
    (actualNormalized g outer c emptySource emptyTarget hSource hTarget).isoBot.inv ≫
      (actualNormalized g outer c emptySource emptyTarget hSource hTarget).incl.app ⊥ = f :=
  (actualNormalized g outer c emptySource emptyTarget hSource hTarget).fac

end OriginalCellTraceClient
