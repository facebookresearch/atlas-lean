/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeBoundedLowerPresentation
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# Compact-root construction cases

Apply the public producer to the empty tree, a nonmonomorphic successor cell
over the noncompact Nat root, and the actual countably infinite fold-cell
diagram. The last case checks its whole endpoint colimit and root change at
aleph one, including the original lower and endpoint comparison maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  CompactRootBaseChange LowerSetColimits

namespace CompactRootBaseChangeTests

section EmptyAndSuccessor

attribute [local instance] Cardinal.fact_isRegular_aleph0

open GoodCellTreeDataExamples

private def successorCompact : CompactRootPresentation Cardinal.aleph0.{0} quotientTree.{t} :=
  compactRootPresentation Cardinal.aleph0.{0} quotientTree.{t}
    (hasCardinalLT_of_finite OneVertex Cardinal.aleph0.{0} le_rfl)
    quotientTreeGood.{t}.presentable_source quotientTreeGood.{t}.presentable_target

private def emptyCompact : CompactRootPresentation Cardinal.aleph0.{0} emptyTree.{t} :=
  compactRootPresentation Cardinal.aleph0.{0} emptyTree.{t}
    (hasCardinalLT_of_finite NoVertices Cardinal.aleph0.{0} le_rfl)
    emptyTreeGood.{t}.presentable_source emptyTreeGood.{t}.presentable_target

example : ¬ IsCardinalPresentable ℕ Cardinal.aleph0.{0} := root_not_presentable

example : ¬ Mono fold := fold_not_mono

example : successorCompact.{t}.tree.label = quotientTree.{t}.label :=
  successorCompact.{t}.label_eq

example : IsCardinalPresentable successorCompact.{t}.root Cardinal.aleph0.{0} :=
  successorCompact.{t}.root_presentable

example (a : OneVertex) :
    IsCardinalPresentable (successorCompact.{t}.tree.predecessorObj a).right
      Cardinal.aleph0.{0} :=
  successorCompact.{t}.predecessor_presentable a

example (B : LowerSet OneVertex) :
    IsCardinalPresentable (successorCompact.{t}.lower.obj B).right Cardinal.aleph0.{0} :=
  successorCompact.{t}.lower_presentable B

private def predecessorIso (a : OneVertex) :
    quotientTree.{t}.predecessorObj a ≅ Under.mk (𝟙 ℕ) := eqToIso rfl

private def attachingNat (a : OneVertex) : Fin 2 ⟶ ℕ :=
  successorCompact.{t}.tree.attaching a ≫
    pushout.inl (successorCompact.{t}.tree.predecessorObj a).hom
      successorCompact.{t}.rootMap ≫
    (successorCompact.{t}.predecessorComparison a).hom.right ≫ (predecessorIso.{t} a).hom.right

private theorem attachingNat_eq (a : OneVertex) : attachingNat.{t} a = attachNat := by
  let g := successorCompact.{t}.tree.attaching a
  let u := pushout.inl (successorCompact.{t}.tree.predecessorObj a).hom
    successorCompact.{t}.rootMap
  let e := (successorCompact.{t}.predecessorComparison a).hom.right
  let z := (predecessorIso.{t} a).hom.right
  have hField := congrFun successorCompact.{t}.attaching_function a
  change g ≫ u ≫ e = 𝟙 (Fin 2) ≫ quotientTree.{t}.attaching a at hField
  have h := hField.trans (Category.id_comp _)
  have hPost := congrArg (fun m : Fin 2 ⟶ (quotientTree.{t}.predecessorObj a).right => m ≫ z) h
  have hAssoc : (g ≫ u ≫ e) ≫ z = g ≫ u ≫ e ≫ z :=
    (Category.assoc g (u ≫ e) z).trans
      (congrArg (fun m => g ≫ m) (Category.assoc u e z))
  have hNative : quotientTree.{t}.attaching a ≫ z = attachNat := rfl
  change g ≫ u ≫ e ≫ z = attachNat
  exact hAssoc.symm.trans (hPost.trans hNative)

example (a : OneVertex) : attachingNat.{t} a (0 : Fin 2) = 0 :=
  congrArg (fun f : Fin 2 ⟶ ℕ => f (0 : Fin 2)) (attachingNat_eq.{t} a)

example (a : OneVertex) : attachingNat.{t} a (1 : Fin 2) = 1 :=
  congrArg (fun f : Fin 2 ⟶ ℕ => f (1 : Fin 2)) (attachingNat_eq.{t} a)

example (n : ℕ) :
    (pushout.inr successorCompact.{t}.tree.hom successorCompact.{t}.rootMap ≫
      successorCompact.{t}.endpointComparison.hom.right) n = quotientArrow n :=
  ConcreteCategory.congr_hom (Under.w successorCompact.{t}.endpointComparison.hom) n

example (n : ℕ) :
    (quotientArrow ≫ successorCompact.{t}.endpointComparison.inv.right) n =
      pushout.inr successorCompact.{t}.tree.hom successorCompact.{t}.rootMap n := by
  have h := ConcreteCategory.congr_hom (Under.w successorCompact.{t}.endpointComparison.inv) n
  exact h

example : IsPushout successorCompact.{t}.tree.hom successorCompact.{t}.rootMap
    (pushout.inl successorCompact.{t}.tree.hom successorCompact.{t}.rootMap ≫
      successorCompact.{t}.endpointComparison.hom.right) quotientArrow :=
  successorCompact.{t}.endpoint_isPushout

example : IsCardinalPresentable emptyCompact.{t}.root Cardinal.aleph0.{0} :=
  emptyCompact.{t}.root_presentable

example : IsCardinalPresentable emptyCompact.{t}.tree.endpointObj.right Cardinal.aleph0.{0} :=
  emptyCompact.{t}.endpoint_presentable

example : emptyCompact.{t}.lower.obj ⊥ ≅ Under.mk (𝟙 emptyCompact.{t}.root) :=
  emptyCompact.{t}.tree.emptyLowerIso emptyCompact.{t}.lower

example (n : ℕ) :
    (pushout.inr emptyCompact.{t}.tree.hom emptyCompact.{t}.rootMap ≫
      emptyCompact.{t}.endpointComparison.hom.right) n = n :=
  ConcreteCategory.congr_hom (Under.w emptyCompact.{t}.endpointComparison.hom) n

end EmptyAndSuccessor

section InfiniteColimit

private instance regularAlephOne : Fact (Cardinal.aleph.{0} 1).IsRegular :=
  ⟨Cardinal.isRegular_aleph_one⟩

private def indexEquiv : BoundedLowerPresentationExamples.Index ≃ ℕ where
  toFun a := a.val
  invFun n := ⟨n⟩
  left_inv a := by cases a; rfl
  right_inv _ := rfl

private theorem countableIndex :
    HasCardinalLT BoundedLowerPresentationExamples.Index (Cardinal.aleph.{0} 1) := by
  apply (hasCardinalLT_iff_of_equiv indexEquiv (Cardinal.aleph.{0} 1)).2
  apply (hasCardinalLT_iff_cardinal_mk_lt ℕ (Cardinal.aleph.{0} 1)).2
  simp

private def infiniteCompact :
    CompactRootPresentation (Cardinal.aleph.{0} 1) BoundedLowerPresentationExamples.tree.{t} :=
  compactRootPresentation (Cardinal.aleph.{0} 1) BoundedLowerPresentationExamples.tree.{t}
    countableIndex
    (fun _ => (hasCardinalLT_of_finite (Fin 2) (Cardinal.aleph.{0} 1)
      Cardinal.aleph0_lt_aleph_one.le).isCardinalPresentable)
    (fun _ => (hasCardinalLT_of_finite PUnit.{1} (Cardinal.aleph.{0} 1)
      Cardinal.aleph0_lt_aleph_one.le).isCardinalPresentable)

example : infiniteCompact.{t}.tree.label = BoundedLowerPresentationExamples.tree.{t}.label :=
  infiniteCompact.{t}.label_eq

example : IsCardinalPresentable infiniteCompact.{t}.tree.endpointObj.right (Cardinal.aleph.{0} 1) :=
  infiniteCompact.{t}.endpoint_presentable

example (B : LowerSet BoundedLowerPresentationExamples.Index) :
    IsCardinalPresentable (infiniteCompact.{t}.lower.obj B).right (Cardinal.aleph.{0} 1) :=
  infiniteCompact.{t}.lower_presentable B

private abbrev infiniteAdjoined : ColimitCocone
    (UnderColimits.adjoinedDiagram (Y := infiniteCompact.{t}.tree.diagram)) :=
  UnderColimits.adjoinedColimit infiniteCompact.{t}.tree.endpoint

example : infiniteAdjoined.{t}.cocone.ι.app WithInitial.star = infiniteCompact.{t}.tree.hom :=
  UnderColimits.adjoined_star infiniteCompact.{t}.tree.endpoint.cocone

example (a : BoundedLowerPresentationExamples.Index) :
    infiniteAdjoined.{t}.cocone.ι.app (WithInitial.of a) =
      (infiniteCompact.{t}.tree.inclusion a).right :=
  UnderColimits.adjoined_vertex infiniteCompact.{t}.tree.endpoint.cocone a

example :
    (Under.pushout infiniteCompact.{t}.rootMap).mapIso
      (infiniteCompact.{t}.tree.endpointIso infiniteCompact.{t}.lower) ≪≫
      infiniteCompact.{t}.endpointComparison =
    (infiniteCompact.{t}.lowerComparison BoundedLowerPresentationExamples.tree.{t}.lowerData).app
      ⊤ ≪≫ BoundedLowerPresentationExamples.tree.{t}.endpointIso
        BoundedLowerPresentationExamples.tree.{t}.lowerData :=
  infiniteCompact.{t}.lower_endpoint_iso BoundedLowerPresentationExamples.tree.{t}.lowerData

example (a : BoundedLowerPresentationExamples.Index) :
    (Under.pushout infiniteCompact.{t}.rootMap).map (infiniteCompact.{t}.tree.inclusion a) ≫
      infiniteCompact.{t}.endpointComparison.hom =
    infiniteCompact.{t}.comparison.hom.app a ≫ BoundedLowerPresentationExamples.tree.{t}.inclusion a :=
  infiniteCompact.{t}.endpoint_leg a

example (B D : LowerSet BoundedLowerPresentationExamples.Index) (h : B ≤ D) :
    (Under.pushout infiniteCompact.{t}.rootMap).map (infiniteCompact.{t}.lower.map h) ≫
      (infiniteCompact.{t}.lowerComparison BoundedLowerPresentationExamples.tree.{t}.lowerData).hom.app
        D =
    (infiniteCompact.{t}.lowerComparison BoundedLowerPresentationExamples.tree.{t}.lowerData).hom.app
      B ≫ BoundedLowerPresentationExamples.tree.{t}.lowerData.map h :=
  (infiniteCompact.{t}.lowerComparison BoundedLowerPresentationExamples.tree.{t}.lowerData).hom.naturality
    (homOfLE h)

example (n : ℕ) :
    (pushout.inr infiniteCompact.{t}.tree.hom infiniteCompact.{t}.rootMap ≫
      infiniteCompact.{t}.endpointComparison.hom.right) n = PUnit.unit :=
  ConcreteCategory.congr_hom (Under.w infiniteCompact.{t}.endpointComparison.hom) n

end InfiniteColimit

end CompactRootBaseChangeTests
