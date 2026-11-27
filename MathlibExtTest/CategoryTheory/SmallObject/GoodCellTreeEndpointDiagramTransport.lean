/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.EndpointDiagramTransport
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData

import Mathlib.Tactic.NormNum

/-!
# Original endpoint diagram transport with nonthin actions and a large root

Both original parallel root actions are retained. The original one-fold
quotient over Nat is compared to its actual lifted coefficient, with both
original inverse functions. Infinite and empty source diagrams retain
their whole component functions and every original transformation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  EndpointDiagramTransport

namespace EndpointDiagramTransportExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original Nat involution changes precisely the two folded original values. -/
def rootSwap : ℕ ⟶ ℕ := ↾fun n => if n = 0 then 1 else if n = 1 then 0 else n

/-- The original quotient identifies those two root values, so the swap fixes its raw quotient. -/
theorem rootSwap_quotient : rootSwap ≫ GoodCellTreeDataExamples.quotientArrow =
    GoodCellTreeDataExamples.quotientArrow := by
  apply ConcreteCategory.ext_apply
  intro n
  change GoodCellTreeDataExamples.quotientArrow (if n = 0 then 1 else if n = 1 then 0 else n) =
    GoodCellTreeDataExamples.quotientArrow n
  by_cases h0 : n = 0
  · subst n
    change GoodCellTreeDataExamples.quotientArrow 1 = GoodCellTreeDataExamples.quotientArrow 0
    exact GoodCellTreeDataExamples.quotientArrow_identifies.symm
  · by_cases h1 : n = 1
    · subst n
      simpa using GoodCellTreeDataExamples.quotientArrow_identifies
    · simp only [ite_eq_right h0, ite_eq_right h1]

/-- Both original nonthin parallel root actions, under the same infinite root. -/
def originalSource : WalkingParallelPair ⥤ Type where
  obj _ := ℕ
  map g := by
    cases g with
    | left => exact 𝟙 ℕ
    | right => exact rootSwap
    | id _ => exact 𝟙 ℕ
  map_id _ := rfl
  map_comp g h := by cases g <;> cases h <;> rfl

/-- The original target keeps its actual chosen pushout quotient type. -/
abbrev originalTarget : WalkingParallelPair ⥤ Type :=
  (Functor.const WalkingParallelPair).obj
    (pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold)

/-- Its original root quotient is natural for both original parallel actions. -/
def originalTransformation : originalSource ⟶ originalTarget where
  app _ := GoodCellTreeDataExamples.quotientArrow
  naturality _ _ g := by
    cases g with
    | left =>
      change (𝟙 ℕ) ≫ GoodCellTreeDataExamples.quotientArrow =
        GoodCellTreeDataExamples.quotientArrow ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    | right =>
      change rootSwap ≫ GoodCellTreeDataExamples.quotientArrow =
        GoodCellTreeDataExamples.quotientArrow ≫ 𝟙 _
      rw [Category.comp_id]
      exact rootSwap_quotient
    | id _ =>
      change (𝟙 ℕ) ≫ GoodCellTreeDataExamples.quotientArrow =
        GoodCellTreeDataExamples.quotientArrow ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]

/-- Every original component retains the same one-fold root tree and actual endpoint. -/
def originalTrees : PointwiseCellTreePresentation GoodCellTreeDataExamples.foldFamily
    originalTransformation (fun _ => GoodCellTreeDataExamples.OneVertex) where
  component _ :=
    { tree := GoodCellTreeDataExamples.quotientTree.{t}, endpointIso := Iso.refl _ }

/-- The actual original quotient and its lifted coefficient have these exact inverse functions. -/
def liftedQuotientIso :
    pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold ≅
      ULift.{0} (pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold) where
  hom := ↾ULift.up
  inv := ↾ULift.down
  hom_inv_id := by
    apply ConcreteCategory.ext_apply
    intro x
    rfl
  inv_hom_id := by
    apply ConcreteCategory.ext_apply
    intro x
    cases x
    rfl

/-- Lift the same actual target coefficient at each original object. -/
abbrev liftedTarget : WalkingParallelPair ⥤ Type :=
  (Functor.const WalkingParallelPair).obj
    (ULift.{0} (pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold))

/-- The actual original lifted target comparison, natural on every original arrow. -/
def liftTargetComparison : originalTarget ≅ liftedTarget :=
  NatIso.ofComponents (fun _ => liftedQuotientIso) (by intro d e g; simp)

/-- The same original quotient followed by the actual lift transformation. -/
def liftedTransformation : originalSource ⟶ liftedTarget :=
  originalTransformation ≫ liftTargetComparison.hom

/-- The given original endpoint comparison has the actual lifted forward and inverse functions. -/
def liftedTrees : PointwiseCellTreePresentation GoodCellTreeDataExamples.foldFamily
    liftedTransformation (fun _ => GoodCellTreeDataExamples.OneVertex) where
  component _ :=
    { tree := GoodCellTreeDataExamples.quotientTree.{t}
      endpointIso := Under.isoMk liftedQuotientIso (by rfl) }

/-- The lifted target diagram, copied onto the actual endpoint objects of the lifted trees. -/
abbrev liftedEndpointDiagram : WalkingParallelPair ⥤ Type :=
  liftedTarget.copyObj (fun d ↦ (endpoint liftedTrees.{t} d).right) (componentIso liftedTrees.{t})

/-- Mathlib's comparison of the lifted target with that copy. -/
abbrev liftedComparison : liftedTarget ≅ liftedEndpointDiagram.{t} :=
  liftedTarget.isoCopyObj _ (componentIso liftedTrees.{t})

theorem originalActionsDifferent :
    originalSource.map WalkingParallelPairHom.left ≠
      originalSource.map WalkingParallelPairHom.right := by
  intro h
  have he := ConcreteCategory.congr_hom h (0 : ℕ)
  change (0 : ℕ) = rootSwap 0 at he
  simp [rootSwap] at he

theorem originalRootNotPresentable : ¬ IsCardinalPresentable ℕ Cardinal.aleph0.{0} :=
  GoodCellTreeDataExamples.root_not_presentable

/-- Every original whole endpoint remains the actual unlifted original quotient. -/
theorem originalEndpointObjects (d : WalkingParallelPair) :
    liftedEndpointDiagram.{t}.obj d =
      (GoodCellTreeDataExamples.quotientTree.{t}.endpointObj).right := by
  cases d <;> rfl

/-- Retain the original forward lift FUNCTION on both actual source objects. -/
theorem originalForwardFunction :
    (fun d : WalkingParallelPair => liftedComparison.{t}.inv.app d) =
      (fun _ : WalkingParallelPair => liftedQuotientIso.hom) := by
  funext d
  cases d <;> rfl

/-- Retain the actual original inverse lift FUNCTION on both actual source objects. -/
theorem originalInverseFunction :
    (fun d : WalkingParallelPair => liftedComparison.{t}.hom.app d) =
      (fun _ : WalkingParallelPair => liftedQuotientIso.inv) := by
  funext d
  cases d <;> rfl

/-- The complete original map function uses precisely both actual endpoint functions and G. -/
theorem originalWholeActionFunction :
    (fun (d e : WalkingParallelPair) (g : d ⟶ e) => liftedEndpointDiagram.{t}.map g) =
      (fun (d e : WalkingParallelPair) (g : d ⟶ e) =>
        (liftedTrees.{t}.component d).endpointIso.hom.right ≫ liftedTarget.map g ≫
          (liftedTrees.{t}.component e).endpointIso.inv.right) := rfl

/-- Both original parallel root equations hold for the same actual transported endpoint actions. -/
theorem originalParallelRootSquares :
    (root liftedTrees.{t}).app .zero ≫ liftedEndpointDiagram.{t}.map WalkingParallelPairHom.left =
        originalSource.map WalkingParallelPairHom.left ≫ (root liftedTrees.{t}).app .one ∧
      (root liftedTrees.{t}).app .zero ≫ liftedEndpointDiagram.{t}.map
          WalkingParallelPairHom.right =
        originalSource.map WalkingParallelPairHom.right ≫ (root liftedTrees.{t}).app .one :=
  ⟨action_root liftedTrees.{t} WalkingParallelPairHom.left,
    action_root liftedTrees.{t} WalkingParallelPairHom.right⟩

/-- The original target squares use the actual same forward endpoint functions. -/
theorem originalParallelTargetSquares :
    liftedEndpointDiagram.{t}.map WalkingParallelPairHom.left ≫
        liftedComparison.{t}.inv.app .one =
      liftedComparison.{t}.inv.app .zero ≫ liftedTarget.map WalkingParallelPairHom.left ∧
    liftedEndpointDiagram.{t}.map WalkingParallelPairHom.right ≫
        liftedComparison.{t}.inv.app .one =
      liftedComparison.{t}.inv.app .zero ≫ liftedTarget.map WalkingParallelPairHom.right :=
  ⟨liftedComparison.{t}.inv.naturality _,
    liftedComparison.{t}.inv.naturality _⟩

theorem originalStrictFactor :
    root liftedTrees.{t} ≫ liftedComparison.{t}.inv = liftedTransformation :=
  root_comparison liftedTrees.{t}

theorem originalInverseFactor :
    liftedTransformation ≫ liftedComparison.{t}.hom = root liftedTrees.{t} :=
  original_inverse_root liftedTrees.{t}

/-- The infinite original index retains each original Nat object value. -/
abbrev InfiniteIndex := Discrete ℕ

/-- The whole original constant Nat-root diagram on the actual infinite index. -/
abbrev infiniteSource : InfiniteIndex ⥤ Type := (Functor.const InfiniteIndex).obj ℕ

/-- The original infinite target diagram keeps the same actual chosen quotient. -/
abbrev infiniteTarget : InfiniteIndex ⥤ Type :=
  (Functor.const InfiniteIndex).obj
    (pushout GoodCellTreeDataExamples.attachNat GoodCellTreeDataExamples.fold)

/-- Every original infinite transformation component is the same original quotient arrow. -/
def infiniteTransformation : infiniteSource ⟶ infiniteTarget where
  app _ := GoodCellTreeDataExamples.quotientArrow

/-- The original whole infinite family retains its actual one-fold trees and endpoint Isos. -/
def infiniteTrees : PointwiseCellTreePresentation GoodCellTreeDataExamples.foldFamily
    infiniteTransformation (fun _ => GoodCellTreeDataExamples.OneVertex) where
  component _ :=
    { tree := GoodCellTreeDataExamples.quotientTree.{t}, endpointIso := Iso.refl _ }

/-- The ENTIRE infinite root-component FUNCTION is the original quotient function. -/
theorem infiniteOriginalRootFunction :
    (fun d : InfiniteIndex => (root infiniteTrees.{t}).app d) =
      (fun _ : InfiniteIndex => GoodCellTreeDataExamples.quotientArrow) := rfl

theorem infiniteOriginalFactor :
    root infiniteTrees.{t} ≫
        (infiniteTarget.isoCopyObj _ (componentIso infiniteTrees.{t})).inv =
      infiniteTransformation :=
  root_comparison infiniteTrees.{t}

theorem infiniteOriginalLabel (d : InfiniteIndex) (a : GoodCellTreeDataExamples.OneVertex) :
    (infiniteTrees.{t}.component d).tree.label a =
      (GoodCellTreeDataExamples.originalLabel : ULift.{t} PUnit.{1}) := rfl

/-- The actual original empty source index. -/
abbrev EmptyIndex := Discrete Empty

/-- The original empty diagram retains the specified Nat coefficient. -/
abbrev emptySource : EmptyIndex ⥤ Type := (Functor.const EmptyIndex).obj ℕ

/-- The original empty target diagram retains its specified PUnit coefficient. -/
abbrev emptyTarget : EmptyIndex ⥤ Type := (Functor.const EmptyIndex).obj PUnit.{1}

/-- The actual original transformation on the empty source category. -/
def emptyTransformation : emptySource ⟶ emptyTarget where
  app d := isEmptyElim d.as

/-- The actual empty component-tree family is chosen on that same original empty index. -/
def emptyTrees : PointwiseCellTreePresentation GoodCellTreeDataExamples.foldFamily
    emptyTransformation (fun _ => GoodCellTreeDataExamples.NoVertices) where
  component d := isEmptyElim d.as

/-- The same actual empty source category has its entire original exact factor equation. -/
theorem emptyOriginalFactor :
    root emptyTrees.{t} ≫ (emptyTarget.isoCopyObj _ (componentIso emptyTrees.{t})).inv =
      emptyTransformation :=
  root_comparison emptyTrees.{t}

end EndpointDiagramTransportExamples
