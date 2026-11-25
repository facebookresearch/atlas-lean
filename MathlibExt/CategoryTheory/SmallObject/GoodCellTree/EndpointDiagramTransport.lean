/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# The original diagram on the same whole cell-tree endpoints

Original component endpoint isomorphisms conjugate the given target
diagram actions. Every original root, object, arrow and endpoint function
is retained. No bounded slice, compactness or new action is a premise.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u vD uD

namespace CategoryTheory.SmallObject.EndpointDiagramTransport

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)

/-- Every original whole endpoint remains under its own original source. -/
abbrev endpoint (d : D) : Under (F.obj d) := (theta.component d).tree.endpointObj

/-- The actual original G action through the two given original endpoint functions. -/
def action {d e : D} (g : d ⟶ e) : (endpoint theta d).right ⟶ (endpoint theta e).right :=
  (theta.component d).endpointIso.hom.right ≫ G.map g ≫
    (theta.component e).endpointIso.inv.right

/-- Its root law uses the original naturality and both original endpoint comparisons. -/
@[reassoc]
theorem action_root {d e : D} (g : d ⟶ e) :
    (theta.component d).tree.hom ≫ action theta g =
      F.map g ≫ (theta.component e).tree.hom := by
  dsimp only [action]
  rw [← Category.assoc, ← Category.assoc, (theta.component d).hom_endpointIso_hom,
    ← f.naturality g, Category.assoc, (theta.component e).hom_endpointIso_inv]

/-- The given endpoint comparison at each object, from the target value to the endpoint. -/
abbrev componentIso (d : D) : G.obj d ≅ (endpoint theta d).right :=
  ((Under.forget (F.obj d)).mapIso (theta.component d).endpointIso).symm

/-- On the original endpoint objects, the target diagram's maps are the given actions. -/
theorem copyObj_map {d e : D} (g : d ⟶ e) :
    (G.copyObj (fun d ↦ (endpoint theta d).right) (componentIso theta)).map g =
      action theta g := rfl

/-- The actual original root functions form their whole natural transformation. -/
def root : F ⟶ G.copyObj (fun d ↦ (endpoint theta d).right) (componentIso theta) where
  app d := (theta.component d).tree.hom
  naturality _ _ g := (action_root theta g).symm

@[simp]
theorem root_app (d : D) : (root theta).app d = (theta.component d).tree.hom := rfl

/-- The entire original root component function is retained. -/
theorem root_function :
    (fun d => (root theta).app d) = (fun d => (theta.component d).tree.hom) := rfl

/-- The whole exact original factorization uses the actual original endpoint functions. -/
theorem root_comparison :
    root theta ≫ (G.isoCopyObj (fun d ↦ (endpoint theta d).right) (componentIso theta)).inv =
      f := by
  apply NatTrans.ext
  funext d
  exact (theta.component d).hom_endpointIso_hom

/-- The actual original inverse comparison recovers the same root transformation. -/
theorem original_inverse_root :
    f ≫ (G.isoCopyObj (fun d ↦ (endpoint theta d).right) (componentIso theta)).hom =
      root theta := by
  apply NatTrans.ext
  funext d
  exact (theta.component d).hom_endpointIso_inv

section Lower

variable (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)

/-- The original chosen lower-to-whole map uses precisely the original L and gamma. -/
def lowerLeg (d : D) (B : LowerSet (P d)) : (L d).obj B ⟶ endpoint theta d :=
  (L d).map (le_top : B ≤ ⊤) ≫ ((theta.component d).tree.endpointIso (L d)).hom

/-- The same chosen lower root followed by its original whole leg gives the original root. -/
@[reassoc]
theorem lowerLeg_root (d : D) (B : LowerSet (P d)) :
    ((L d).obj B).hom ≫ (lowerLeg theta L d B).right = (theta.component d).tree.hom :=
  Under.w (lowerLeg theta L d B)

/-- The full original lower-to-target leg retains both endpoint comparison functions. -/
theorem lowerLeg_to_original (d : D) (B : LowerSet (P d)) :
    (lowerLeg theta L d B).right ≫
        (G.isoCopyObj (fun d ↦ (endpoint theta d).right) (componentIso theta)).inv.app d =
      ((L d).map (le_top : B ≤ ⊤) ≫
        ((theta.component d).tree.endpointIso (L d)).hom ≫
          (theta.component d).endpointIso.hom).right := by
  simp only [lowerLeg, Functor.isoCopyObj_inv_app, Iso.symm_inv, Functor.mapIso_hom,
    Under.forget_map, Under.comp_right, Category.assoc]

/-- Compose a GIVEN original action with the original lower inclusion into its whole endpoint. -/
def lowerAction {d e : D} (g : d ⟶ e) (B : LowerSet (P d)) :
    ((L d).obj B).right ⟶ (endpoint theta e).right :=
  (lowerLeg theta L d B).right ≫ action theta g

/-- This actual lower-source map has the original arbitrary-root compatibility equation. -/
@[reassoc]
theorem lowerAction_root {d e : D} (g : d ⟶ e) (B : LowerSet (P d)) :
    ((L d).obj B).hom ≫ lowerAction theta L g B =
      F.map g ≫ (theta.component e).tree.hom := by
  rw [lowerAction, ← Category.assoc, lowerLeg_root, action_root]

/-- Every original lower-source action keeps exactly the original G map and two Isos. -/
theorem lowerAction_function :
    (fun (d e : D) (g : d ⟶ e) (B : LowerSet (P d)) => lowerAction theta L g B) =
      (fun (d e : D) (g : d ⟶ e) (B : LowerSet (P d)) =>
        (lowerLeg theta L d B).right ≫ (theta.component d).endpointIso.hom.right ≫
          G.map g ≫ (theta.component e).endpointIso.inv.right) := by
  funext d e g B
  rfl

end Lower

end CategoryTheory.SmallObject.EndpointDiagramTransport
