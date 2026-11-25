/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.OrderBounds
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Actual original lower-subtree presentations

The label carrier is the literal original lower subtype. Every original
vertex, attaching map, generator cell and predecessor colimit is retained.
Its endpoint is the original chosen lower-colimit object under the same root.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.CellTreeLowerRestriction

open Limits LowerSetColimits

variable {P : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {alpha : Type t} {s : alpha → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet P)

/-- The exact original predecessor-label equivalence at an original lower-subtype label. -/
def predecessorOrderIso (a : B) : LowerSet.Iio a ≃o LowerSet.Iio a.1 where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z := ⟨⟨z.1, B.lower z.2.le a.2⟩, z.2⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl
  map_rel_iff' := by intro z z'; rfl

/-- The whole original vertex diagram on the literal original lower label subtype. -/
abbrev diagram : B ⥤ Under X := restriction T.diagram B

/-- Its actual whole original object function is unchanged. -/
theorem diagram_obj_function :
    (fun a : B => (diagram T B).obj a) = (fun a : B => T.diagram.obj a.1) := rfl

/-- Its entire original Hom function is the same original comparison at those original labels. -/
theorem diagram_map_function :
    (fun (a b : B) (f : a ⟶ b) => (diagram T B).map f) =
      (fun (a b : B) (f : a ⟶ b) => T.diagram.map (homOfLE (leOfHom f))) := rfl

/-- Original strict-predecessor diagrams agree through the same identity-on-label equivalence. -/
theorem predecessorDiagram :
    ∀ a : B, (predecessorOrderIso B a).equivalence.functor ⋙
      restriction T.diagram (LowerSet.Iio a.1) =
        restriction (diagram T B) (LowerSet.Iio a) := by
  intro a
  rfl

/-- The original predecessor cocone keeps its actual point and original vertex-leg function. -/
abbrev predecessor (a : B) :
    ColimitCocone (restriction (diagram T B) (LowerSet.Iio a)) where
  cocone :=
    { pt := T.predecessorObj a.1
      ι :=
        { app z := (T.predecessor a.1).cocone.ι.app ((predecessorOrderIso B a) z)
          naturality z z' f := by
            change T.diagram.map (homOfLE (leOfHom f)) ≫
              (T.predecessor a.1).cocone.ι.app ((predecessorOrderIso B a) z') =
              (T.predecessor a.1).cocone.ι.app ((predecessorOrderIso B a) z) ≫ 𝟙 _
            rw [Category.comp_id]
            exact (T.predecessor a.1).cocone.w
              ((predecessorOrderIso B a).equivalence.functor.map f) } }
  isColimit := by
    change IsColimit
      ((T.predecessor a.1).cocone.whisker (predecessorOrderIso B a).equivalence.functor)
    exact (T.predecessor a.1).isColimit.whiskerEquivalence
      (predecessorOrderIso B a).equivalence

/-- The actual original predecessor object is literal, not a newly selected replacement. -/
theorem predecessor_obj_function :
    (fun a : B => (predecessor T B a).cocone.pt) =
      (fun a : B => T.predecessorObj a.1) := rfl

/-- Every original predecessor leg is unchanged under the native label equivalence. -/
theorem predecessor_leg_function (a : B) :
    (fun z : LowerSet.Iio a => (predecessor T B a).cocone.ι.app z) =
      (fun z : LowerSet.Iio a => (T.predecessor a.1).cocone.ι.app
        ((predecessorOrderIso B a) z)) := rfl

/-- Both original colimit universal properties give the same predecessor-to-vertex map. -/
theorem predecessorMap (a : B) :
    cellTreePredecessorMap (diagram T B) a (predecessor T B a) =
      T.predecessorMap a.1 := by
  apply (T.predecessor a.1).isColimit.hom_ext
  intro z
  obtain ⟨z', rfl⟩ := (predecessorOrderIso B a).surjective z
  have h := cellTreePredecessorMap_fac (diagram T B) a (predecessor T B a) z'
  change (T.predecessor a.1).cocone.ι.app ((predecessorOrderIso B a) z') ≫
    cellTreePredecessorMap (diagram T B) a (predecessor T B a) =
      T.diagram.map (homOfLE z'.2.le) at h
  exact h.trans (T.predecessorMap_fac a.1 ((predecessorOrderIso B a) z')).symm

/-- The full lower tree retains every original vertex, label, cell and endpoint choice. -/
def tree : CellTree s X (P := B) where
  wellFounded := InvImage.wf (fun a : B => a.1) T.wellFounded
  diagram := diagram T B
  label a := T.label a.1
  predecessor a := predecessor T B a
  attaching a := T.attaching a.1
  cell a := T.cell a.1
  isPushout a := by
    rw [predecessorMap]
    exact T.isPushout a.1
  endpoint := ⟨L.cocone B, L.isColimit B⟩

/-- The original generator-label function is retained on the whole literal lower carrier. -/
theorem tree_label_function :
    (tree T L B).label = (fun a : B => T.label a.1) := rfl

/-- The entire original cell-target function is retained on its actual original dependent types. -/
theorem tree_cell_function :
    (fun a : B => (tree T L B).cell a) = (fun a : B => T.cell a.1) := rfl

/-- The whole original lower endpoint is precisely the same selected L object under X. -/
theorem tree_endpoint : (tree T L B).endpointObj = L.obj B := rfl

/-- The exact original lower root function is unchanged. -/
theorem tree_root : (tree T L B).hom = (L.obj B).hom := rfl

/-- Every original lower endpoint vertex leg remains its actual original selected cocone leg. -/
theorem tree_inclusion_function :
    (fun a : B => (tree T L B).inclusion a) = (fun a : B => L.ι B a) := rfl

variable (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Goodness restricts using the same original endpoint witnesses and true predecessor injection. -/
theorem tree_good (good : T.IsGood chi) : (tree T L B).IsGood chi where
  presentable_source a := good.presentable_source a.1
  presentable_target a := good.presentable_target a.1
  predecessor_lt a := (good.predecessor_lt a.1).of_injective
    (fun z : Set.Iio a => (⟨z.1.1, z.2⟩ : Set.Iio a.1))
    (by
      intro z z' h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : Set.Iio a.1 => x.1) h)

end CategoryTheory.SmallObject.CellTreeLowerRestriction
