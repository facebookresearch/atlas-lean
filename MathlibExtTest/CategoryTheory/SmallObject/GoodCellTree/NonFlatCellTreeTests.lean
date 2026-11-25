/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RelativePresentability
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeWeakSaturation
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# A non-flat two-vertex good cell tree in `Type`

The vertex order is `false < true` on `Bool` and the root is `X = PUnit`. Vertex `false`
attaches the cell `PEmpty → PUnit` to the root. Vertex `true` attaches the fold
`Fin 2 → PUnit` along a map hitting both the root point and the point of the first cell, so
its strict-predecessor diagram is nonempty and its predecessor colimit is the first vertex.

The clients check:
* `CellTree.IsGood ℵ₀` for this tree;
* κ-presentability of the endpoint under the root, via `RelativeCellPresentability.endpoint`;
* membership of the endpoint arrow `X → Y₀ → Y₁` in the class `(ofHoms cells).rlp.llp`,
  via `CellTreeWeakSaturation.hom_mem`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject LowerSetColimits
open CategoryTheory.ConcreteCategory

set_option autoImplicit false

noncomputable section

@[expose] public section

namespace MathlibExtTest.CategoryTheory.SmallObject.NonFlatCellTree

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The one-point root. -/
abbrev X : Type := PUnit.{1}

/-- The 0-cell `PEmpty → PUnit`. -/
def g0 : PEmpty.{1} ⟶ PUnit.{1} := ↾fun e => e.elim

/-- The two attaching cells: the 0-cell at `false` and the fold `Fin 2 → PUnit` at `true`. -/
def cellArrow : Bool → Arrow Type
  | false => Arrow.mk g0
  | true => Arrow.mk GoodCellTreeDataExamples.fold

/-- The attaching map of the first cell. -/
def a0 : PEmpty.{1} ⟶ X := ↾fun e => e.elim

/-- The first vertex: the pushout attaching the 0-cell to the root. -/
abbrev Y0 : Type := pushout a0 g0

/-- The root inclusion into the first vertex. -/
def f0 : X ⟶ Y0 := pushout.inl a0 g0

/-- The new point of the first vertex. -/
def b0 : PUnit.{1} ⟶ Y0 := pushout.inr a0 g0

/-- The attaching map of the second cell: `0 ↦` root point, `1 ↦` the first cell's point. -/
def a1 : Fin 2 ⟶ Y0 := ↾fun i => if i = 0 then f0 PUnit.unit else b0 PUnit.unit

/-- The second vertex: the pushout attaching the fold along `a1`. -/
abbrev Y1 : Type := pushout a1 GoodCellTreeDataExamples.fold

/-- The inclusion of the first vertex into the second. -/
def f1 : Y0 ⟶ Y1 := pushout.inl a1 GoodCellTreeDataExamples.fold

/-- The cell-target map of the second vertex. -/
def b1 : PUnit.{1} ⟶ Y1 := pushout.inr a1 GoodCellTreeDataExamples.fold

/-- The two vertices under the root. -/
def V : Bool → Under X
  | false => Under.mk f0
  | true => Under.mk (f0 ≫ f1)

/-- The vertex comparison `V false ⟶ V true`. -/
def u : V false ⟶ V true := Under.homMk f1 rfl

/-- The vertex maps along the order of `Bool`. -/
def vmap : (b c : Bool) → b ≤ c → (V b ⟶ V c)
  | false, false, _ => 𝟙 _
  | false, true, _ => u
  | true, true, _ => 𝟙 _
  | true, false, h => absurd h (by decide)

/-- The two-vertex diagram under the root. -/
def diagram : Bool ⥤ Under X where
  obj := V
  map {b c} h := vmap b c (leOfHom h)
  map_id b := by cases b <;> rfl
  map_comp {b c d} h k := by
    cases b <;> cases c <;> cases d <;> simp [vmap] <;>
      first | exact absurd (leOfHom h) (by decide) | exact absurd (leOfHom k) (by decide)

instance : IsEmpty (LowerSet.Iio false) := ⟨fun q => by
  rcases q with ⟨q, hq⟩
  change q < false at hq
  cases q <;> exact absurd hq (by decide)⟩

/-- The unique strict predecessor of `true`. -/
def topPred : LowerSet.Iio true := ⟨false, (show false < true by decide)⟩

/-- `false` is terminal among the strict predecessors of `true`. -/
def topPredTerminal : IsTerminal topPred :=
  IsTerminal.ofUniqueHom (fun q => homOfLE (by
      rcases q with ⟨q, hq⟩
      change q < true at hq
      change q ≤ false
      cases q <;> simp_all))
    (fun _ _ => Subsingleton.elim _ _)

/-- The predecessor colimits: initial at `false`, the first vertex at `true`. -/
def predecessor : (b : Bool) → ColimitCocone (restriction diagram (LowerSet.Iio b))
  | false =>
    { cocone :=
        { pt := Under.mk (𝟙 X)
          ι := { app := fun q => isEmptyElim q, naturality := fun q => isEmptyElim q } }
      isColimit :=
        { desc := fun c => Under.mkIdInitial.to c.pt
          fac := fun _ q => isEmptyElim q
          uniq := fun c m _ => Under.mkIdInitial.hom_ext m (Under.mkIdInitial.to c.pt) } }
  | true =>
    { cocone := coconeOfDiagramTerminal topPredTerminal _
      isColimit := colimitOfDiagramTerminal topPredTerminal _ }

example : (cellArrow false).left = PEmpty.{1} := rfl
example : (predecessor false).cocone.pt = Under.mk (𝟙 X) := rfl
example : (predecessor true).cocone.pt = V false := rfl

/-- `true` is terminal in `Bool`. -/
def boolTop : IsTerminal (true : Bool) :=
  IsTerminal.ofUniqueHom (fun b => homOfLE (Bool.le_true b)) (fun _ _ => Subsingleton.elim _ _)

/-- The attaching maps into the predecessor colimits. -/
def attaching : (b : Bool) → (cellArrow b).left ⟶ (predecessor b).cocone.pt.right
  | false => a0
  | true => a1

/-- The cell-target maps into the vertices. -/
def cell : (b : Bool) → (cellArrow b).right ⟶ (diagram.obj b).right
  | false => b0
  | true => b1

/-- The predecessor map at `false` is the root inclusion `f0`. -/
theorem predMap_false :
    (cellTreePredecessorMap diagram false (predecessor false)).right = f0 := by
  have hp : cellTreePredecessorMap diagram false (predecessor false) =
      Under.mkIdInitial.to (diagram.obj false) := Under.mkIdInitial.hom_ext _ _
  rw [hp, Under.mkIdInitial_to_right]
  rfl

/-- The predecessor map at `true` is the vertex inclusion `f1`. -/
theorem predMap_true :
    (cellTreePredecessorMap diagram true (predecessor true)).right = f1 := rfl

/-- The non-flat two-vertex cell tree, with genuine pushout squares at both vertices. -/
def tree : CellTree cellArrow X (P := Bool) where
  wellFounded := wellFounded_lt
  diagram := diagram
  label := id
  predecessor := predecessor
  attaching := attaching
  cell := cell
  isPushout b := by
    cases b
    · rw [predMap_false]; exact IsPushout.of_hasPushout a0 g0
    · rw [predMap_true]; exact IsPushout.of_hasPushout a1 GoodCellTreeDataExamples.fold
  endpoint := ⟨coconeOfDiagramTerminal boolTop diagram, colimitOfDiagramTerminal boolTop diagram⟩

/-- The second vertex has a nonempty strict-predecessor diagram. -/
example : Nonempty (LowerSet.Iio (true : Bool)) := ⟨topPred⟩

/-- The endpoint arrow is the two-step composite `X → Y0 → Y1`. -/
example : tree.hom = f0 ≫ f1 := rfl

instance : IsCardinalPresentable PEmpty.{1} Cardinal.aleph0.{0} :=
  (hasCardinalLT_of_finite PEmpty.{1} Cardinal.aleph0.{0} le_rfl).isCardinalPresentable

/-- The tree is good at `ℵ₀`. -/
theorem tree_good : tree.IsGood Cardinal.aleph0.{0} where
  presentable_source b := by
    cases b
    · change IsCardinalPresentable PEmpty.{1} _; infer_instance
    · change IsCardinalPresentable (Fin 2) _; exact GoodCellTreeDataExamples.finTwoPresentable
  presentable_target b := by
    cases b <;> exact GoodCellTreeDataExamples.punitPresentable
  predecessor_lt b := hasCardinalLT_of_finite _ _ le_rfl

/-- The endpoint is `ℵ₀`-presentable under the root. -/
theorem endpoint_presentable : IsCardinalPresentable tree.endpointObj Cardinal.aleph0.{0} :=
  RelativeCellPresentability.endpoint Cardinal.aleph0.{0} tree tree_good
    (hasCardinalLT_of_finite Bool _ le_rfl)

/-- The left lifting class of the right lifting class of the two cells. -/
abbrev W : MorphismProperty Type :=
  (MorphismProperty.ofHoms (fun b => (cellArrow b).hom) : MorphismProperty Type).rlp.llp

/-- The endpoint arrow lies in `W`. -/
theorem hom_mem_W : W tree.hom :=
  CellTreeWeakSaturation.hom_mem W tree tree.lowerData
    (fun b => MorphismProperty.le_llp_rlp _ _ (MorphismProperty.ofHoms.mk b))

/-- The same membership, stated for the two-step composite. -/
example : W (f0 ≫ f1) := hom_mem_W

#print axioms tree_good
#print axioms endpoint_presentable
#print axioms hom_mem_W

end MathlibExtTest.CategoryTheory.SmallObject.NonFlatCellTree

end
