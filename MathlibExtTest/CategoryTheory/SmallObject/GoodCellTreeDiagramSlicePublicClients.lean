/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExtensions
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExhaustion
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData
import Mathlib.Tactic.Linter.Lint

/-!
# Public clients of relative cell trees and action-preserving diagram slices

The clients compose actual slice inclusion arrows, extend a prescribed bounded
family while retaining its root and target transformations, and descend an
arbitrary cocone from the original endpoint. The relative-tree cases include
an empty increment over a selected quotient endpoint and the original
non-monomorphic fold cell. The union clients use both actual pushout legs to
characterize the unique action, with all original index arrows retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section
universe w t uD vD uC vC uI

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  BoundedLowerSupport DiagramActionCapture DiagramActionRefinement
  DiagramSliceExtensions DiagramSliceExhaustion

namespace GoodCellTreeDiagramSlicePublicClients

section RelativeTrees

variable {P : Type w} [PartialOrder P] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)

example (B E : LowerSet P) (hBE : B ≤ E) :
    ∃ U : CellTree.Presentation (s := s) (P := CellTreeIncrement.Label B E) (L.map hBE).right,
      U.tree.label = fun a => T.label a.1 :=
  ⟨{ tree := CellTreeIncrement.tree T L B E hBE, endpointIso := Iso.refl _ },
    CellTreeIncrement.tree_label_function T L B E hBE⟩

example (B : LowerSet P) : IsEmpty (CellTreeIncrement.Label B B) :=
  ⟨fun a => a.2.2 a.2.1⟩

example (B : LowerSet P) :
    (CellTreeIncrement.tree T L B B le_rfl).hom = 𝟙 (L.obj B).right :=
  (CellTreeIncrement.tree_hom T L B B le_rfl).trans
    (congrArg Under.Hom.right (L.map_id B))

end RelativeTrees

section ActualQuotient

open GoodCellTreeDataExamples

/-- A nonempty literal increment retains the original non-monomorphic fold generator. -/
def quotientIncrement : CellTree foldFamily.{t} (quotientTree.{t}.lowerData.obj ⊥).right
    (P := CellTreeIncrement.Label (⊥ : LowerSet OneVertex) ⊤) :=
  CellTreeIncrement.tree quotientTree.{t} quotientTree.{t}.lowerData ⊥ ⊤ bot_le

example : ∃ a : CellTreeIncrement.Label (⊥ : LowerSet OneVertex) ⊤,
    quotientIncrement.{t}.label a = originalLabel.{t} ∧
      ¬ Mono (foldFamily.{t} (quotientIncrement.{t}.label a)).hom := by
  let a : CellTreeIncrement.Label (⊥ : LowerSet OneVertex) ⊤ :=
    ⟨default, by trivial, fun h => LowerSet.notMem_bot h⟩
  exact ⟨a, rfl, fold_not_mono⟩

/-- The empty increment is rooted at the actual selected full quotient object. -/
def emptyAtQuotient : CellTree foldFamily.{t} (quotientTree.{t}.lowerData.obj ⊤).right
    (P := CellTreeIncrement.Label (⊤ : LowerSet OneVertex) ⊤) :=
  CellTreeIncrement.tree quotientTree.{t} quotientTree.{t}.lowerData ⊤ ⊤ le_rfl

example : emptyAtQuotient.{t}.hom = 𝟙 (quotientTree.{t}.lowerData.obj ⊤).right :=
  (CellTreeIncrement.tree_hom quotientTree.{t} quotientTree.{t}.lowerData ⊤ ⊤ le_rfl).trans
    (congrArg Under.Hom.right (quotientTree.{t}.lowerData.map_id ⊤))

end ActualQuotient

section Slices

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

example : Category.{0} (Slice theta L chi) := inferInstance

example : Quiver.IsThin (Slice theta L chi) := inferInstance

example {A B E : Slice theta L chi} (p : A ⟶ B) (q : B ⟶ E) :
    A.root theta L chi ≫ (p ≫ q).toNatTrans ≫ E.target theta L chi = f := by
  rw [← Category.assoc, (p ≫ q).root]
  exact E.factor theta L chi

example {A B E : Slice theta L chi} (p : A ⟶ B) (q : B ⟶ E)
    {d e : D} (g : d ⟶ e) :
    (p ≫ q).toNatTrans.app d ≫ E.map g = A.map g ≫ (p ≫ q).toNatTrans.app e :=
  ((p ≫ q).toNatTrans.naturality g).symm

example {A B : Slice theta L chi} (p : A ⟶ B) (d : D) :
    ∃ U : CellTree.Presentation (s := s)
      (P := CellTree.Increment (A.supports d).1 (B.supports d).1)
      (((Slice.diagram (theta := theta) (L := L) (chi := chi)).map p).app d),
        U.tree.label = fun a => (theta.component d).tree.label a.1 :=
  ⟨{ tree := inclusionTree theta L chi p d, endpointIso := Iso.refl _ }, rfl⟩

section Constructors

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)
  (hUncountable : Cardinal.aleph0 < chi)

include hArrow good hUncountable in
example {I : Type uI} (hI : HasCardinalLT I chi) (A : I → Slice theta L chi)
    (seed : Supports (P := P) chi) :
    ∃ E : Slice theta L chi, (∀ d, seed d ≤ E.supports d) ∧
      ∃ p : ∀ i, A i ⟶ E,
        (∀ i, (A i).root theta L chi ≫ (p i).toNatTrans = E.root theta L chi) ∧
        (∀ i, (p i).toNatTrans ≫ E.target theta L chi = (A i).target theta L chi) := by
  let E := extension theta L chi hArrow good hI A hUncountable seed
  let p := extensionInclusion theta L chi hArrow good hI A hUncountable seed
  exact ⟨E, seed_le_extension theta L chi hArrow good hI A hUncountable seed,
    p, fun i => (p i).root, fun i => (p i).target⟩

include hArrow good hUncountable in
example (c : Cocone (Slice.underDiagram (theta := theta) (L := L) (chi := chi))) :
    ∃! m : Under.mk f ⟶ c.pt,
      ∀ A : Slice theta L chi,
        (Slice.endpointCocone (theta := theta) (L := L) (chi := chi)).ι.app A ≫ m =
          c.ι.app A := by
  let h := DiagramSliceExhaustion.isColimit theta L chi hArrow good hUncountable
  exact ⟨h.desc c, h.fac c, fun m hm => h.uniq c m hm⟩

include hArrow good hUncountable in
example (d : D) :
    (⨆ A : Slice theta L chi, (A.supports d).1) = (⊤ : LowerSet (P d)) :=
  labels_exhausted theta L chi hArrow good hUncountable d

end Constructors

section UnionActions

variable (A B : OriginalSlice theta L)
  (t : ∀ {d e : D} (_g : d ⟶ e),
    ((L d).obj (A.supports d ⊓ B.supports d)).right ⟶
      ((L e).obj (A.supports e ⊓ B.supports e)).right)
  (htA : ∀ {d e : D} (g : d ⟶ e),
    ((L d).map (inf_le_left : A.supports d ⊓ B.supports d ≤ A.supports d)).right ≫
        A.map g = t g ≫
      ((L e).map (inf_le_left : A.supports e ⊓ B.supports e ≤ A.supports e)).right)
  (htB : ∀ {d e : D} (g : d ⟶ e),
    ((L d).map (inf_le_right : A.supports d ⊓ B.supports d ≤ B.supports d)).right ≫
        B.map g = t g ≫
      ((L e).map (inf_le_right : A.supports e ⊓ B.supports e ≤ B.supports e)).right)

example : (unionSlice theta L A B t htA htB).root ≫
    (unionSlice theta L A B t htA htB).target = f :=
  (unionSlice theta L A B t htA htB).factor

example {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    (unionSlice theta L A B t htA htB).toFunctor.map (g ≫ h) =
      (unionSlice theta L A B t htA htB).map g ≫
        (unionSlice theta L A B t htA htB).map h :=
  (unionSlice theta L A B t htA htB).toFunctor.map_comp g h

example {d e : D} (g : d ⟶ e)
    (k : ((L d).obj (A.supports d ⊔ B.supports d)).right ⟶
      ((L e).obj (A.supports e ⊔ B.supports e)).right)
    (hkA : ((L d).map (le_sup_left : A.supports d ≤ A.supports d ⊔ B.supports d)).right ≫ k =
      A.map g ≫ ((L e).map (le_sup_left : A.supports e ≤ A.supports e ⊔ B.supports e)).right)
    (hkB : ((L d).map (le_sup_right : B.supports d ≤ A.supports d ⊔ B.supports d)).right ≫ k =
      B.map g ≫ ((L e).map (le_sup_right : B.supports e ≤ A.supports e ⊔ B.supports e)).right) :
    k = (unionSlice theta L A B t htA htB).map g := by
  apply (unionCoefficientIsPushout theta L A B d).hom_ext
  · exact hkA.trans (unionAction_left theta L A B t htA htB g).symm
  · exact hkB.trans (unionAction_right theta L A B t htA htB g).symm

example : (leftUnionInclusion theta L A B t htA htB).toNatTrans ≫
    (unionSlice theta L A B t htA htB).target = A.target := by
  apply NatTrans.ext
  funext d
  exact inclusion_leg theta L d le_sup_left

example : (rightUnionInclusion theta L A B t htA htB).toNatTrans ≫
    (unionSlice theta L A B t htA htB).target = B.target := by
  apply NatTrans.ext
  funext d
  exact inclusion_leg theta L d le_sup_right

end UnionActions

end Slices

end GoodCellTreeDiagramSlicePublicClients

#lint in MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramSlicePublicClients

#lint only unusedArguments in MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramSlicePublicClients

#lint only unusedArguments in MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement

#lint only unusedArguments in MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExtensions

#lint only unusedArguments in MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExhaustion
