/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionPredecessors

/-!
# The actual labelled one-cell good-order extension tree

The complete tree is constructed from the original old tree, its selected
lower point and the new cell's actual attaching map. Every predecessor UP,
pushout and whole endpoint UP has already been constructed. Goodness uses
only old local goodness and the captured lower bound, never an old total bound.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.GoodCellExtensionTree

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram
  GoodCellExtensionColimits GoodCellExtensionPredecessors

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {P : Type w} [PartialOrder P] {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet P) (i : A) (a : (s i).left ⟶ (L.obj B).right)

/-- The whole old predecessor descender equals the original selected old descender. -/
theorem oldPredecessorMap_eq (p : P) :
    letI := extensionOrder B
    cellTreePredecessorMap (diagram T L B i a) (Index.old p)
      (oldPredecessorData T L B i a p) = T.predecessorMap p := by
  let : PartialOrder (Index P) := extensionOrder B
  let newMap : T.predecessorObj p ⟶ T.vertex p :=
    cellTreePredecessorMap (diagram T L B i a) (Index.old p)
      (oldPredecessorData T L B i a p)
  change newMap = T.predecessorMap p
  apply (T.predecessor p).isColimit.hom_ext
  intro b
  have hNew : (T.predecessor p).cocone.ι.app b ≫ newMap =
      T.diagram.map (homOfLE b.2.le) :=
    (oldPredecessorData T L B i a p).isColimit.fac
      (cellTreePredecessorCocone (diagram T L B i a) (Index.old p))
      (oldPredecessorsIso B p b)
  exact hNew.trans (T.predecessorMap_fac p b).symm

/-- The complete new predecessor descender is the actual selected lower-to-pushout map. -/
theorem newPredecessorMap_eq :
    letI := extensionOrder B
    cellTreePredecessorMap (diagram T L B i a) Index.new
      (newPredecessorData T L B i a) = newStep T L B i a := by
  let : PartialOrder (Index P) := extensionOrder B
  apply (L.isColimit B).hom_ext
  intro b
  exact (newPredecessorData T L B i a).isColimit.fac
    (cellTreePredecessorCocone (diagram T L B i a) Index.new)
    (newPredecessorsIso B b)

/-- Every old cell keeps its actual original label, and the new cell keeps its given label. -/
def label (x : Index P) : A :=
  match x.val with
  | some p => T.label p
  | none => i

/-- All actual predecessor colimit choices are the already constructed original cocones. -/
def predecessor :
    letI := extensionOrder B
    ∀ x : Index P, ColimitCocone (restriction (diagram T L B i a) (LowerSet.Iio x)) := by
  letI := extensionOrder B
  rintro ⟨x⟩
  cases x with
  | some p => exact oldPredecessorData T L B i a p
  | none => exact newPredecessorData T L B i a

/-- Every attaching map retains either its original old value or the actual captured new value. -/
def attaching :
    letI := extensionOrder B
    ∀ x : Index P, (s (label T i x)).left ⟶ (predecessor T L B i a x).cocone.pt.right := by
  letI := extensionOrder B
  rintro ⟨x⟩
  cases x with
  | some p => exact T.attaching p
  | none => exact a

/-- The whole cell-target map function keeps the original old maps and the new pushout map. -/
def cell :
    letI := extensionOrder B
    ∀ x : Index P, (s (label T i x)).right ⟶ ((diagram T L B i a).obj x).right := by
  letI := extensionOrder B
  rintro ⟨x⟩
  cases x with
  | some p => exact T.cell p
  | none => exact newCell T L B i a

/-- The complete labelled extension tree is constructed with all actual predecessor/endpoint UPs. -/
def extensionTree :
    letI := extensionOrder B
    CellTree s X (P := Index P) := by
  letI := extensionOrder B
  refine {
    wellFounded := extension_wellFounded B T.wellFounded
    diagram := diagram T L B i a
    label := label T i
    predecessor := predecessor T L B i a
    attaching := attaching T L B i a
    cell := cell T L B i a
    isPushout := ?_
    endpoint := ⟨endpointCocone T L B i a, wholeEndpointIsColimit T L B i a⟩ }
  rintro ⟨x⟩
  cases x with
  | some p =>
    change IsPushout (T.attaching p) (s (T.label p)).hom
      (cellTreePredecessorMap (diagram T L B i a) (Index.old p)
        (oldPredecessorData T L B i a p)).right (T.cell p)
    rw [oldPredecessorMap_eq]
    exact T.isPushout p
  | none =>
    change IsPushout a (s i).hom
      (cellTreePredecessorMap (diagram T L B i a) Index.new
        (newPredecessorData T L B i a)).right (newCell T L B i a)
    rw [newPredecessorMap_eq]
    exact newPoint_isPushout T L B i a

/-- The complete original root-to-endpoint map is the actual old endpoint pushout map. -/
theorem extensionTree_root :
    letI := extensionOrder B
    (extensionTree T L B i a).hom =
      T.hom ≫ pushout.inl (globalAttaching T L B i a) (s i).hom := rfl

/-- Every original old vertex is retained literally in the constructed tree. -/
theorem extensionTree_old_vertex (p : P) :
    letI := extensionOrder B
    (extensionTree T L B i a).vertex (Index.old p) = T.vertex p := rfl

/-- The new tree vertex is precisely the actual selected lower pushout. -/
theorem extensionTree_new_vertex :
    letI := extensionOrder B
    (extensionTree T L B i a).vertex Index.new = newPoint T L B i a := rfl

/-- Local old goodness and the actual captured lower bound prove full extension goodness. -/
theorem extensionTree_good (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (good : T.IsGood chi) (hB : HasCardinalLT B chi)
    [IsCardinalPresentable (s i).left chi] [IsCardinalPresentable (s i).right chi] :
    letI := extensionOrder B
    (extensionTree T L B i a).IsGood chi := by
  let : PartialOrder (Index P) := extensionOrder B
  refine {
    presentable_source := ?_
    presentable_target := ?_
    predecessor_lt := ?_ }
  · rintro ⟨x⟩
    cases x with
    | some p => exact good.presentable_source p
    | none => exact ‹IsCardinalPresentable (s i).left chi›
  · rintro ⟨x⟩
    cases x with
    | some p => exact good.presentable_target p
    | none => exact ‹IsCardinalPresentable (s i).right chi›
  · rintro ⟨x⟩
    cases x with
    | some p =>
      exact (good.predecessor_lt p).of_injective
        (oldPredecessorsIso B p).symm (oldPredecessorsIso B p).symm.injective
    | none =>
      exact hB.of_injective (newPredecessorsIso B).symm (newPredecessorsIso B).symm.injective

end CategoryTheory.SmallObject.GoodCellExtensionTree
