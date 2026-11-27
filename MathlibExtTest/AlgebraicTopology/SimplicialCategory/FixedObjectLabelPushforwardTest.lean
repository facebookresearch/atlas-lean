/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardAdjunction

/-! # Original paths survive a proper collapse of enriched object labels

A free noninvertible arrow has two different original objects. Collapsing
both labels produces a loop. Its square is distinct from the loop: an
actual free-loop interpreter distinguishes their lengths. Every scalar
degree is checked, together with both complete-map inverse laws.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial
open CategoryTheory.SimplicialEnrichment CategoryTheory.SimplicialQuiver
open CategoryTheory.SimplicialEnrichment.FixedObjects

namespace FixedObjectLabelPushforwardTest

abbrev ArrowLabels := ULift.{u} Bool
abbrev LoopLabels := PUnit.{u + 1}

def start : ArrowLabels.{u} := ⟨false⟩
def finish : ArrowLabels.{u} := ⟨true⟩
def point : LoopLabels.{u} := PUnit.unit

def collapse : ArrowLabels.{u} → LoopLabels.{u} := fun _ => point

def arrowQuiver : Data ArrowLabels.{u} where
  Hom s t := (Functor.const SimplexCategoryᵒᵖ).obj
    {_c : PUnit.{u + 1} // s.down = false ∧ t.down = true}

def loopQuiver : Data LoopLabels.{u} where
  Hom _ _ := (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}

def arrow : FixedObjects ArrowLabels.{u} := ⟨free arrowQuiver, rfl⟩
def loop : FixedObjects LoopLabels.{u} := ⟨free loopQuiver, rfl⟩

def originalGenerator (q : SimplexCategoryᵒᵖ) :
    (hom arrow.{u} start finish).obj q :=
  (generator arrowQuiver start finish).app q ⟨PUnit.unit, rfl, rfl⟩

def loopGenerator (q : SimplexCategoryᵒᵖ) : (hom loop.{u} point point).obj q :=
  (generator loopQuiver point point).app q PUnit.unit

def interpreter : Interpretation arrowQuiver.{u} loop.val where
  obj _ := point
  map _ _ := {
    app q := ↾fun _ => loopGenerator q
    naturality q r f := by ext c; rfl }

def toLoop : arrow.{u} ⟶ LabelRestriction.object collapse loop := by
  letI : EnrichedCategory SSet.{u} ArrowLabels := freeEnrichment arrowQuiver
  exact ofHomMaps (fun s t => interpreter.evalHom s t)
    (fun s => interpreter.extend.map_id s)
    (fun s t r => interpreter.extend.map_comp s t r)

theorem toLoop_generator (q : SimplexCategoryᵒᵖ) :
    (homMap toLoop.{u} start finish).app q (originalGenerator q) = loopGenerator q := by
  have hm : homMap toLoop start finish = interpreter.evalHom start finish := by
    unfold toLoop
    exact homMap_ofHomMaps _ _ _ start finish
  exact (congrArg (fun m : hom arrow start finish ⟶ hom loop point point =>
    m.app q (originalGenerator q)) hm).trans
      (congrArg (fun m => m.app q ⟨PUnit.unit, rfl, rfl⟩)
        (interpreter.generator_eval start finish))

def pushedArrow : FixedObjects LoopLabels.{u} := LabelPushforward.object collapse arrow

def retainedLoop (q : SimplexCategoryᵒᵖ) : (hom pushedArrow.{u} point point).obj q :=
  (LabelPushforward.unitHom collapse arrow start finish).app q (originalGenerator q)

def retainedSquare (q : SimplexCategoryᵒᵖ) : (hom pushedArrow.{u} point point).obj q :=
  (compositionMap pushedArrow point point point).app q (retainedLoop q, retainedLoop q)

def readback : pushedArrow.{u} ⟶ loop := LabelPushforward.desc collapse arrow toLoop

theorem readback_loop (q : SimplexCategoryᵒᵖ) :
    (homMap readback.{u} point point).app q (retainedLoop q) = loopGenerator q := by
  have h := congrArg (fun F : arrow ⟶ LabelRestriction.object collapse loop =>
    (homMap F start finish).app q (originalGenerator q))
      (LabelPushforward.unit_desc collapse arrow toLoop)
  rw [homMap_comp, LabelPushforward.homMap_unit, LabelRestriction.homMap_map] at h
  exact h.trans (toLoop_generator q)

theorem readback_square (q : SimplexCategoryᵒᵖ) :
    (homMap readback.{u} point point).app q (retainedSquare q) =
      (compositionMap loop point point point).app q (loopGenerator q, loopGenerator q) := by
  have h := congrArg (fun m => m.app q (retainedLoop q, retainedLoop q))
    (compositionMap_homMap readback point point point)
  change (homMap readback point point).app q (retainedSquare q) =
    (compositionMap loop point point point).app q
      ((homMap readback point point).app q (retainedLoop q),
        (homMap readback point point).app q (retainedLoop q)) at h
  rw [readback_loop] at h
  exact h

theorem loop_length (q : SimplexCategoryᵒᵖ) :
    pathLength loopQuiver.{u} q ((homMap readback point point).app q (retainedLoop q)) = 1 := by
  rw [readback_loop]
  rfl

theorem square_length (q : SimplexCategoryᵒᵖ) :
    pathLength loopQuiver.{u} q ((homMap readback point point).app q (retainedSquare q)) = 2 := by
  rw [readback_square]
  rfl

/-- Collapsing the two objects does not add the unsupported source equation `f² = f`. -/
theorem loop_ne_square (q : SimplexCategoryᵒᵖ) : retainedLoop.{u} q ≠ retainedSquare q := by
  intro h
  have hh := congrArg (fun p =>
    pathLength loopQuiver q ((homMap readback point point).app q p)) h
  rw [loop_length, square_length] at hh
  exact (by decide : (1 : ℕ) ≠ 2) hh

/-- The collapse is proper at the original object level. -/
example : start.{u} ≠ finish ∧ collapse start = collapse finish := by
  constructor
  · intro h
    have := congrArg ULift.down h
    exact Bool.false_ne_true this
  · rfl

/-- Both whole-map inverse equations retain the actual original noninvertible arrow. -/
example :
    (LabelPushforward.homEquiv collapse arrow loop) readback = toLoop ∧
      (LabelPushforward.homEquiv collapse arrow loop).symm toLoop = readback := by
  constructor
  · exact LabelPushforward.unit_desc collapse arrow toLoop
  · rfl

/-- The nontrivial loop distinction is also checked in a raised value universe. -/
example : retainedLoop.{u + 1} (op ⦋2⦌) ≠ retainedSquare (op ⦋2⦌) :=
  loop_ne_square _

/-- Every unused target object is still an actual original label of the empty-source pushforward. -/
example (O : Type u) (C : FixedObjects PEmpty.{u + 1})
    (a : PEmpty.{u + 1} → O) (x : O) :
    vertex (LabelPushforward.object a C) x = x := rfl

/-- A proper extra target label is retained independently of the collapsed original objects. -/
example : vertex (LabelPushforward.object (fun _ : ArrowLabels.{u} => start) arrow) finish = finish := rfl

end FixedObjectLabelPushforwardTest
