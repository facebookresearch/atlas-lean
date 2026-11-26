/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallColimits
import MathlibExtTest.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardTest
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Actual changing-object coequalizers retain original enriched functors

Two genuinely different point maps select the original ends of a free
noninvertible arrow. Their actual carrier coequalizer identifies those
objects. Its universal map reads back the complete original collapse
functor into the free-loop target, including every original Hom simplex.
The construction is checked at an arbitrary and a raised value universe.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open CategoryTheory.SimplicialEnrichment CategoryTheory.SimplicialQuiver
open FixedObjectLabelPushforwardTest

namespace CarrierColimitTest

def pointQuiver : Data LoopLabels.{u} where
  Hom _ _ := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}

def pointCarrier : Carrier.{u} := free pointQuiver

def pointInterpretation (x : arrow.{u}.val) : Interpretation pointQuiver arrow.val where
  obj _ := x
  map _ _ := {
    app _ := ↾fun p => PEmpty.elim p
    naturality _ _ _ := by ext p; exact PEmpty.elim p }

def atObject (x : arrow.{u}.val) : pointCarrier ⟶ arrow.val :=
  (pointInterpretation x).extend

def left : pointCarrier.{u} ⟶ arrow.val := atObject start
def right : pointCarrier.{u} ⟶ arrow.val := atObject finish

def collapseWhole : arrow.{u}.val ⟶ loop.val :=
  toLoop.val ≫ CarrierReindexing.toTarget loop.val collapse

/-- The two actual point functors have genuinely distinct original object maps. -/
theorem point_maps_distinct : left.{u}.obj point ≠ right.{u}.obj point := by
  intro h
  exact Bool.false_ne_true (congrArg ULift.down h)

/-- The same original collapse functor satisfies the whole enriched coequalizer condition. -/
theorem agreement : left.{u} ≫ collapseWhole = right.{u} ≫ collapseWhole := by
  apply (interpretationEquiv pointQuiver (C := loop.val)).injective
  change Interpretation.mk (C := loop.val) (fun _ => (point : loop.val))
      (fun x y => generator pointQuiver x y ≫ (left ≫ collapseWhole).map x y) =
    Interpretation.mk (C := loop.val) (fun _ => (point : loop.val))
      (fun x y => generator pointQuiver x y ≫ (right ≫ collapseWhole).map x y)
  apply congrArg (Interpretation.mk (C := loop.val) (fun _ => (point : loop.val)))
  funext x y
  ext q p
  exact PEmpty.elim p

/-- The actual changing-object coequalizer identifies the two supplied original object images. -/
theorem identified :
    (coequalizer.π left.{u} right.{u}).obj start.{u} =
      (coequalizer.π left.{u} right.{u}).obj finish.{u} :=
  congrArg (fun H : pointCarrier.{u} ⟶ coequalizer left.{u} right.{u} => H.obj point)
    (coequalizer.condition left.{u} right.{u})

def readback : coequalizer left.{u} right.{u} ⟶ loop.val :=
  coequalizer.desc collapseWhole agreement

/-- The whole original collapse functor is retained, including its complete noninvertible Hom map. -/
example : coequalizer.π left.{u} right.{u} ≫ readback = collapseWhole := by
  simp [readback]

/-- The object identification is also genuinely available in a raised scalar and object universe. -/
example : (coequalizer.π left.{u + 1} right.{u + 1}).obj start.{u + 1} =
    (coequalizer.π left.{u + 1} right.{u + 1}).obj finish.{u + 1} := identified

/-- The actual constructed colimits also supply the empty diagram without changing the value universe. -/
example : HasInitial Carrier.{u} := inferInstance

end CarrierColimitTest
