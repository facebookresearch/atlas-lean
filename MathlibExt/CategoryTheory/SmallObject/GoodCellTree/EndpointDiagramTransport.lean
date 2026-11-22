/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

theorem action_id (d : D) : action theta (𝟙 d) = 𝟙 (endpoint theta d).right := by
  change (theta.component d).endpointIso.hom.right ≫ G.map (𝟙 d) ≫
    (theta.component d).endpointIso.inv.right = 𝟙 (endpoint theta d).right
  rw [show G.map (𝟙 d) = 𝟙 (Under.mk (f.app d)).right by
    simpa only [Under.mk_right] using G.map_id d]
  rw [Category.id_comp, Under.hom_right_inv_right]

theorem action_comp {d e q : D} (g : d ⟶ e) (h : e ⟶ q) :
    action theta (g ≫ h) = action theta g ≫ action theta h := by
  simp only [action, G.map_comp, Category.assoc, Under.inv_right_hom_right_assoc]

/-- The original endpoint objects and actual conjugated actions form one whole diagram. -/
def toFunctor : D ⥤ C where
  obj d := (endpoint theta d).right
  map g := action theta g
  map_id d := action_id theta d
  map_comp g h := action_comp theta g h

@[simp]
theorem toFunctor_obj (d : D) : (toFunctor theta).obj d = (endpoint theta d).right := rfl

@[simp]
theorem toFunctor_map {d e : D} (g : d ⟶ e) :
    (toFunctor theta).map g = action theta g := rfl

/-- The complete dependent original map function, retaining every original Hom value. -/
theorem map_function :
    (fun (d e : D) (g : d ⟶ e) => (toFunctor theta).map g) =
      (fun (d e : D) (g : d ⟶ e) =>
        (theta.component d).endpointIso.hom.right ≫ G.map g ≫
          (theta.component e).endpointIso.inv.right) := rfl

/-- The same given component Isos form the actual whole comparison to the original G. -/
def comparison : toFunctor theta ≅ G :=
  NatIso.ofComponents
    (fun d => (Under.forget (F.obj d)).mapIso (theta.component d).endpointIso)
    (fun g => by
      change action theta g ≫ (theta.component _).endpointIso.hom.right =
        (theta.component _).endpointIso.hom.right ≫ G.map g
      simp only [action, Category.assoc, Under.inv_right_hom_right, Under.mk_right,
        Category.comp_id])

@[simp]
theorem comparison_hom_app (d : D) :
    (comparison theta).hom.app d = (theta.component d).endpointIso.hom.right := rfl

@[simp]
theorem comparison_inv_app (d : D) :
    (comparison theta).inv.app d = (theta.component d).endpointIso.inv.right := rfl

/-- The whole original forward component function of the same given comparison. -/
theorem comparison_hom_function :
    (fun d => (comparison theta).hom.app d) =
      (fun d => (theta.component d).endpointIso.hom.right) := rfl

/-- The whole original inverse component function of the same given comparison. -/
theorem comparison_inv_function :
    (fun d => (comparison theta).inv.app d) =
      (fun d => (theta.component d).endpointIso.inv.right) := rfl

/-- The actual original root functions form their whole natural transformation. -/
def root : F ⟶ toFunctor theta where
  app d := (theta.component d).tree.hom
  naturality _ _ g := (action_root theta g).symm

@[simp]
theorem root_app (d : D) : (root theta).app d = (theta.component d).tree.hom := rfl

/-- The entire original root component function is retained. -/
theorem root_function :
    (fun d => (root theta).app d) = (fun d => (theta.component d).tree.hom) := rfl

/-- The whole exact original factorization uses the actual original endpoint functions. -/
theorem root_comparison : root theta ≫ (comparison theta).hom = f := by
  apply NatTrans.ext
  funext d
  exact (theta.component d).hom_endpointIso_hom

/-- The actual original inverse comparison recovers the same root transformation. -/
theorem original_inverse_root : f ≫ (comparison theta).inv = root theta := by
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
    (lowerLeg theta L d B).right ≫ (comparison theta).hom.app d =
      ((L d).map (le_top : B ≤ ⊤) ≫
        ((theta.component d).tree.endpointIso (L d)).hom ≫
          (theta.component d).endpointIso.hom).right := by
  simp only [lowerLeg, comparison_hom_app, Under.comp_right, Category.assoc]

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
