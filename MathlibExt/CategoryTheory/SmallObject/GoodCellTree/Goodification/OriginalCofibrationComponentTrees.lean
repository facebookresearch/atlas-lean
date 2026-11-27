/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Codex
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCofibrationGoodTree

/-!
# Constructed original component trees in the common compact scalar family

The actual compact scalar subtype keeps each original Arrow value literally.
Relabelling a produced tree changes only its family witness. Every vertex,
map, predecessor cocone, cell leg, chosen lower colimit and endpoint remains
the same. The original coefficient model constructs these trees for every
component of an actual objectwise cofibration at one common selected rank.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  HomotopicalAlgebra.FunctorInjective

namespace CategoryTheory.SmallObject.OriginalCofibrationGoodTree

section CommonScalarFamily

variable (C : Type uC) [Category.{vC} C] [CategoryWithCofibrations C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- The common family consists of the actual original compact scalar cofibration Arrows. -/
abbrev compactScalarArrows :
    {a : Arrow C // compactBaseCofibrationArrows C chi a} → Arrow C := Subtype.val

end CommonScalarFamily

section ProducedTree

variable {C : Type uC} [Category.{vC} C] [CategoryWithCofibrations C]
  {chi : Cardinal.{w}} [Fact chi.IsRegular] {X Y : C} {f : X ⟶ Y}
  (H : Data chi f)

/-- Each produced birth retains its literal original Arrow and actual compactness witnesses. -/
abbrev Data.scalarLabel (p : H.index) :
    {a : Arrow C // compactBaseCofibrationArrows C chi a} := ⟨H.cells p, H.cell_mem p⟩

/-- Put the actual produced tree in the common scalar family, retaining every tree field. -/
def Data.scalarTree :
    letI := H.order
    CellTree (compactScalarArrows C chi) X (P := H.index) := by
  letI := H.order
  exact
    { wellFounded := H.tree.wellFounded
      diagram := H.tree.diagram
      label p := H.scalarLabel (H.tree.label p)
      predecessor := H.tree.predecessor
      attaching := H.tree.attaching
      cell := H.tree.cell
      isPushout := H.tree.isPushout
      endpoint := H.tree.endpoint }

/-- The complete original vertex diagram and all its morphisms are unchanged. -/
theorem Data.scalarTree_diagram :
    letI := H.order
    H.scalarTree.diagram = H.tree.diagram := rfl

/-- The full original predecessor cocone function and all its universal properties are unchanged. -/
theorem Data.scalarTree_predecessor :
    letI := H.order
    H.scalarTree.predecessor = H.tree.predecessor := rfl

/-- The complete original attaching-map function is retained literally. -/
theorem Data.scalarTree_attaching :
    letI := H.order
    H.scalarTree.attaching = H.tree.attaching := rfl

/-- The complete original cell-target function is retained literally. -/
theorem Data.scalarTree_cell :
    letI := H.order
    H.scalarTree.cell = H.tree.cell := rfl

/-- The whole original endpoint cocone and its colimit UP are retained literally. -/
theorem Data.scalarTree_endpoint :
    letI := H.order
    H.scalarTree.endpoint = H.tree.endpoint := rfl

/-- Every actual original endpoint vertex leg is retained literally. -/
theorem Data.scalarTree_inclusion :
    letI := H.order
    H.scalarTree.inclusion = H.tree.inclusion := rfl

/-- Each common scalar label has the same literal original compact Arrow value. -/
theorem Data.scalarTree_label_value (p : H.index) :
    letI := H.order
    compactScalarArrows C chi (H.scalarTree.label p) = H.cells p := by
  let _ := H.order
  change H.cells (H.tree.label p) = H.cells p
  rw [congrFun H.label_eq p]
  rfl

/-- The common-family tree keeps the actual chosen lower cocones from its producer. -/
abbrev Data.scalarLowerData :
    letI := H.order
    LowerSetColimitData H.scalarTree.diagram := H.lowerData

/-- All original compact-cell and individual predecessor bounds survive the literal relabelling. -/
theorem Data.scalarTree_good :
    letI := H.order
    H.scalarTree.IsGood chi := by
  let _ := H.order
  exact
    { presentable_source := fun p => H.good.presentable_source p
      presentable_target := fun p => H.good.presentable_target p
      predecessor_lt := fun p => H.good.predecessor_lt p }

/-- The common-family tree is a full original-source presentation of the same actual f. -/
abbrev Data.scalarPresentation :
    letI := H.order
    CellTree.Presentation (s := compactScalarArrows C chi) (P := H.index) f := by
  letI := H.order
  exact ⟨H.scalarTree, eqToIso H.endpoint_eq⟩

/-- The common-family presentation's forward endpoint map recovers the same original f. -/
theorem Data.scalarPresentation_root :
    letI := H.order
    H.scalarTree.hom ≫ H.scalarPresentation.endpointIso.hom.right = f :=
  Under.w (eqToIso H.endpoint_eq).hom

/-- Its actual inverse endpoint map preserves the same original source arrow too. -/
theorem Data.scalarPresentation_inverse_root :
    letI := H.order
    f ≫ H.scalarPresentation.endpointIso.inv.right = H.scalarTree.hom :=
  Under.w (eqToIso H.endpoint_eq).inv

/-- Every actual used common-family label has original scalar membership and compact ends. -/
theorem Data.scalarTree_cell_mem (p : H.index) :
    letI := H.order
    compactBaseCofibrationArrows C chi
      (compactScalarArrows C chi (H.scalarTree.label p)) := by
  let _ := H.order
  exact (H.scalarTree.label p).property

end ProducedTree

end CategoryTheory.SmallObject.OriginalCofibrationGoodTree

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory.SmallObject CategoryTheory.SmallObject.OriginalCofibrationGoodTree

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] {S : Type w} [SmallCategory S] (s : D ≌ S)
  (b : BoundedConstruction d kappaLP s)
  {F G : D ⥤ C} (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a))

/-- The original model constructs each actual component tree at the SAME selected rank. -/
def originalComponentData (a : D) : Data b.cardinal (f.app a) :=
  sameProfileOriginalCofibrationGoodTree d kappaLP s b (f.app a) (hf a)

/-- Every original component has its actual constructed working-universe vertex carrier. -/
abbrev originalComponentLabels : D → Type w :=
  fun a => (originalComponentData d kappaLP s b f hf a).index

/-- All actual component good orders are outputs of the same original construction. -/
abbrev originalComponentOrders : ∀ a : D,
    PartialOrder (originalComponentLabels d kappaLP s b f hf a) :=
  fun a => (originalComponentData d kappaLP s b f hf a).order

/-- The ACTUAL original pointwise cofibration has its constructed common-family component trees. -/
def originalComponentPresentation :
    letI := originalComponentOrders d kappaLP s b f hf
    PointwiseCellTreePresentation (s := compactScalarArrows C b.cardinal) f
      (originalComponentLabels d kappaLP s b f hf) := by
  letI := originalComponentOrders d kappaLP s b f hf
  exact { component a := (originalComponentData d kappaLP s b f hf a).scalarPresentation }

/-- The original action APIs receive the exact chosen lower cocones of every produced component. -/
abbrev originalComponentLowerData :
    letI := originalComponentOrders d kappaLP s b f hf
    ∀ a : D, LowerSetColimitData
      ((originalComponentPresentation d kappaLP s b f hf).component a).tree.diagram := by
  letI := originalComponentOrders d kappaLP s b f hf
  exact fun a => (originalComponentData d kappaLP s b f hf a).scalarLowerData

/-- Every constructed original component is genuinely good at the SAME actual selected rank. -/
theorem originalComponentGood :
    letI := originalComponentOrders d kappaLP s b f hf
    ∀ a : D, ((originalComponentPresentation d kappaLP s b f hf).component a).tree.IsGood
      b.cardinal := by
  let _ := originalComponentOrders d kappaLP s b f hf
  exact fun a => (originalComponentData d kappaLP s b f hf a).scalarTree_good

/-- Every actual component endpoint remains its original target under its original source. -/
theorem originalComponentEndpoint :
    letI := originalComponentOrders d kappaLP s b f hf
    ∀ a : D, ((originalComponentPresentation d kappaLP s b f hf).component a).tree.endpointObj =
      Under.mk (f.app a) := by
  let _ := originalComponentOrders d kappaLP s b f hf
  exact fun a => (originalComponentData d kappaLP s b f hf a).endpoint_eq

/-- All original component source arrows are recovered by their actual endpoint comparisons. -/
theorem originalComponentRoot :
    letI := originalComponentOrders d kappaLP s b f hf
    ∀ a : D, ((originalComponentPresentation d kappaLP s b f hf).component a).tree.hom ≫
      ((originalComponentPresentation d kappaLP s b f hf).component a).endpointIso.hom.right =
      f.app a := by
  let _ := originalComponentOrders d kappaLP s b f hf
  let theta := originalComponentPresentation d kappaLP s b f hf
  exact fun a => (theta.component a).hom_endpointIso_hom

end HomotopicalAlgebra.FunctorInjective
