/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Attachments

/-!
# Actual original cell traces through variable cellular normalization

Every normalized cell comes from one genuine original inner cell.
The original outer index, inner stage, generator label and endpoint
inclusion are retained through the canonical attachment equality.
Greatest-inner joins contribute their actual empty occurrence type.

The object, Hom, outer-order, inner-order, cell and generator-label
universes remain independent. Both original empty cofans and their colimit cocones are supplied.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w w' ν u v t

open CategoryTheory Limits HomotopicalAlgebra
open CategoryTheory.SmallObject.CellularNormalization

namespace CategoryTheory.SmallObject.CellularNormalization.CellTrace

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

local instance originalFlatWF : WellFoundedLT (Index K) := lexWellFounded
/-- The canonical successor order on the flattened original variable histories. -/
local instance originalFlatSucc : SuccOrder (Index K) := flatSuccOrder

/-- The canonical normalization of the actual original variable-generator histories. -/
abbrev normalizedComplex : RelativeCellComplex.{ν} (flatCellMap (K := K) g) f :=
  normalizeRelativeCells g outer c emptySource emptyTarget hSource hTarget

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- At every genuine inner successor, the normalized attachment is the canonical
transport of the same original attachment. -/
theorem normalizedAttachment_inner (j : J) (k : K j)
    (ha : ¬ IsMax (vertex j k)) (hk : ¬ IsMax k) :
    (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).attachCells
      (vertex j k) ha = innerAttachment g outer c j k hk := by
  classical
  dsimp only [normalizedComplex, normalizeRelativeCells, vertex, toLex, Equiv.refl,
    Lex, Equiv.coe_fn_mk, id]
  rw [dite_eq_right hk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical greatest-inner join has the actual empty occurrence type. -/
theorem normalizedAttachment_empty (j : J) (k : K j)
    (ha : ¬ IsMax (vertex j k)) (hk : IsMax k) :
    ((normalizedComplex g outer c emptySource emptyTarget hSource hTarget).attachCells
      (vertex j k) ha).ι = PEmpty.{ν + 1} := by
  classical
  dsimp only [normalizedComplex, normalizeRelativeCells, vertex, toLex, Equiv.refl,
    Lex, Equiv.coe_fn_mk, id]
  rw [dite_eq_left hk]
  rfl

/-- Every actual normalized cell has a genuine nonmaximal original inner stage. -/
theorem normalizedCell_inner_notMax
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    ¬ IsMax (ofLex a.j).2 := by
  rcases a with ⟨⟨j, k⟩, ha, z⟩
  intro hk
  exact (cast (normalizedAttachment_empty g outer c emptySource emptyTarget hSource hTarget
    j k ha hk) z).elim

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The target component of the canonical step isomorphism recovers the actual
original inner and outer endpoint maps. -/
theorem innerStepArrowIso_endpoint (j : J) (k : K j) (hk : ¬ IsMax k) :
    (innerStepArrowIso g outer c j k hk).hom.right ≫
      (normalizedPresentation outer (innerPresentations g outer c)).incl.app
        (Order.succ (vertex j k)) =
      (c j).incl.app (Order.succ k) ≫ outer.incl.app (Order.succ j) := by
  let e := (flat_succ_inner (K := K) j k hk).symm
  calc
    (innerStepArrowIso g outer c j k hk).hom.right ≫
        (normalizedPresentation outer (innerPresentations g outer c)).incl.app
          (Order.succ (vertex j k)) =
      (diagram outer.F (innerPresentations g outer c)).map (eqToHom e) ≫
        (endpoint outer.F (innerPresentations g outer c) outer.incl).app
          (Order.succ (vertex j k)) := by
            simp only [innerStepArrowIso, Iso.trans_hom, Arrow.comp_right,
              eqToIso.hom, Arrow.eqToHom_right, eqToHom_refl,
              diagramArrowIso, Arrow.isoMk_hom_right, Functor.mapIso_hom,
              Category.id_comp, normalizedPresentation]
    _ = (endpoint outer.F (innerPresentations g outer c) outer.incl).app
          (vertex j (Order.succ k)) := by
            exact ((endpoint outer.F (innerPresentations g outer c) outer.incl).naturality
              (eqToHom e)).trans (Category.comp_id _)
    _ = (c j).incl.app (Order.succ k) ≫ outer.incl.app (Order.succ j) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every canonical transported inner cell keeps the same original endpoint composite. -/
theorem innerAttachment_cell_endpoint (j : J) (k : K j) (hk : ¬ IsMax k)
    (z : ((c j).attachCells k hk).ι) :
    (innerAttachment g outer c j k hk).cell z ≫
      (normalizedPresentation outer (innerPresentations g outer c)).incl.app
        (Order.succ (vertex j k)) =
      ((c j).attachCells k hk).cell z ≫ (c j).incl.app (Order.succ k) ≫
        outer.incl.app (Order.succ j) := by
  dsimp only [AttachCells.cell, innerAttachment, AttachCells.ofArrowIso]
  simp only [Category.assoc]
  exact congrArg (fun q => ((c j).attachCells k hk).cofan₂.inj z ≫
    ((c j).attachCells k hk).g₂ ≫ q) (innerStepArrowIso_endpoint g outer c j k hk)

omit [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] in
/-- Equality of actual attachments transports the exact occurrence label. -/
private theorem attachment_label_transport {X' Y' : C} {f' : X' ⟶ Y'} (j : J)
    (T U : AttachCells.{ν} (g j) f') (h : T = U) (z : T.ι) :
    U.π (cast (congrArg (fun q => q.ι) h) z) = T.π z := by
  cases h
  rfl

omit [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] in
/-- Equality of actual attachments transports the same original codomain cell map. -/
private theorem attachment_cell_transport {X' Y' : C} {f' : X' ⟶ Y'} (j : J)
    (T U : AttachCells.{ν} (g j) f') (h : T = U) (z : T.ι) :
    T.cell z = eqToHom (congrArg (B j) (attachment_label_transport g j T U h z)).symm ≫
      U.cell (cast (congrArg (fun q => q.ι) h) z) := by
  cases h
  exact (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The exact original occurrence is obtained by transporting its index through
only the canonical normalized attachment equality. No empty join contributes a cell. -/
def originalCell
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    UsedCells g outer.F c :=
  ⟨(ofLex a.j).1,
    { j := (ofLex a.j).2
      hj := normalizedCell_inner_notMax g outer c emptySource emptyTarget hSource hTarget a
      k := cast (congrArg (fun q => q.ι)
        (normalizedAttachment_inner g outer c emptySource emptyTarget hSource hTarget
          (ofLex a.j).1 (ofLex a.j).2 a.hj
          (normalizedCell_inner_notMax g outer c emptySource emptyTarget hSource hTarget a))) a.k }⟩

/-- The normalized occurrence retains its literal original outer index. -/
theorem originalCell_outerIndex
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (originalCell g outer c emptySource emptyTarget hSource hTarget a).1 = (ofLex a.j).1 := rfl

/-- The normalized occurrence retains its literal original inner stage. -/
theorem originalCell_innerStage
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (originalCell g outer c emptySource emptyTarget hSource hTarget a).2.j = (ofLex a.j).2 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual original occurrence index changes only by the exact attachment-type equality. -/
theorem originalCell_occurrence
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (originalCell g outer c emptySource emptyTarget hSource hTarget a).2.k =
      cast (congrArg (fun q => q.ι)
        (normalizedAttachment_inner g outer c emptySource emptyTarget hSource hTarget
          (ofLex a.j).1 (ofLex a.j).2 a.hj
          (normalizedCell_inner_notMax g outer c emptySource emptyTarget hSource hTarget a))) a.k :=
            rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every actual normalized occurrence retains its full original generating label. -/
theorem originalCell_label
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    (originalCell g outer c emptySource emptyTarget hSource hTarget a).2.i = a.i := by
  exact attachment_label_transport g (ofLex a.j).1 _ _
    (normalizedAttachment_inner g outer c emptySource emptyTarget hSource hTarget
      (ofLex a.j).1 (ofLex a.j).2 a.hj
      (normalizedCell_inner_notMax g outer c emptySource emptyTarget hSource hTarget a)) a.k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every actual normalized occurrence has the unchanged original inner/outer
endpoint composite, with only the typed transport of its preserved label. -/
theorem originalCell_endpoint
    (a : (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).Cells) :
    a.ι = eqToHom (congrArg (B (ofLex a.j).1)
      (originalCell_label g outer c emptySource emptyTarget hSource hTarget a)).symm ≫
      (originalCell g outer c emptySource emptyTarget hSource hTarget a).2.ι ≫
        outer.incl.app (Order.succ (ofLex a.j).1) := by
  let hk := normalizedCell_inner_notMax g outer c emptySource emptyTarget hSource hTarget a
  let T :=
    (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).attachCells a.j a.hj
  let U := innerAttachment g outer c (ofLex a.j).1 (ofLex a.j).2 hk
  let hTU : T = U := normalizedAttachment_inner g outer c emptySource emptyTarget hSource hTarget
    (ofLex a.j).1 (ofLex a.j).2 a.hj hk
  let z' : ((c (ofLex a.j).1).attachCells (ofLex a.j).2 hk).ι :=
    cast (congrArg (fun q => q.ι) hTU) a.k
  let e := originalCell_label g outer c emptySource emptyTarget hSource hTarget a
  have hcell : T.cell a.k = eqToHom (congrArg (B (ofLex a.j).1) e).symm ≫ U.cell z' :=
    attachment_cell_transport g (ofLex a.j).1 T U hTU a.k
  have hinner : U.cell z' ≫
      (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).incl.app
          (Order.succ a.j) =
      (originalCell g outer c emptySource emptyTarget hSource hTarget a).2.ι ≫
        outer.incl.app (Order.succ (ofLex a.j).1) := by
    change (innerAttachment g outer c (ofLex a.j).1 (ofLex a.j).2 hk).cell z' ≫
      (normalizedPresentation outer (innerPresentations g outer c)).incl.app
        (Order.succ (vertex (ofLex a.j).1 (ofLex a.j).2)) =
      (((c (ofLex a.j).1).attachCells (ofLex a.j).2 hk).cell z' ≫
        (c (ofLex a.j).1).incl.app (Order.succ (ofLex a.j).2)) ≫
          outer.incl.app (Order.succ (ofLex a.j).1)
    exact (innerAttachment_cell_endpoint g outer c (ofLex a.j).1 (ofLex a.j).2 hk z').trans
      (Category.assoc _ _ _).symm
  change T.cell a.k ≫
    (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).incl.app (Order.succ a.j)
        = _
  calc
    T.cell a.k ≫
        (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).incl.app
            (Order.succ a.j) =
      (eqToHom (congrArg (B (ofLex a.j).1) e).symm ≫ U.cell z') ≫
        (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).incl.app
            (Order.succ a.j) :=
          congrArg (fun q => q ≫
            (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).incl.app
                (Order.succ a.j)) hcell
    _ = eqToHom (congrArg (B (ofLex a.j).1) e).symm ≫
        (U.cell z' ≫
          (normalizedComplex g outer c emptySource emptyTarget hSource hTarget).incl.app
              (Order.succ a.j)) :=
            Category.assoc _ _ _
    _ = eqToHom (congrArg (B (ofLex a.j).1) e).symm ≫
        (originalCell g outer c emptySource emptyTarget hSource hTarget a).2.ι ≫
          outer.incl.app (Order.succ (ofLex a.j).1) := by
      exact congrArg (fun q => eqToHom (congrArg (B (ofLex a.j).1) e).symm ≫ q) hinner

end CategoryTheory.SmallObject.CellularNormalization.CellTrace
