/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RelativePresentability
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

import Mathlib.Tactic.NormNum

/-!
# Original arbitrary-root relative-presentability clients

The same fold tree over ℕ has presentable under-root vertices and bounded
slices while ℕ itself is not presentable. Its original raw cell pushout is
transposed without changing any raw map. Native root-adjoined colimits retain
actual empty and disconnected diagrams.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject UnderColimits

namespace RelativeCellPresentabilityExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original root remains nonpresentable at the same chosen cardinal. -/
theorem originalRootNotPresentable :
    ¬ IsCardinalPresentable ℕ Cardinal.aleph0.{0} :=
  GoodCellTreeDataExamples.root_not_presentable

/-- The same original forgetful functor is accessible at the same cardinal. -/
theorem originalForgetAccessible :
    (Under.forget ℕ).IsCardinalAccessible Cardinal.aleph0.{0} := inferInstance

/-- The same original free finite cell source is presentable relative to ℕ. -/
theorem originalFreeSourcePresentable :
    IsCardinalPresentable ((Under.costar ℕ).obj (Fin 2)) Cardinal.aleph0.{0} :=
  costarPresentable Cardinal.aleph0.{0} (Fin 2)

/-- The actual original tree vertex is presentable under its nonpresentable root. -/
theorem originalVertexPresentable (p : GoodCellTreeDataExamples.OneVertex) :
    IsCardinalPresentable (GoodCellTreeDataExamples.quotientTree.{t}.vertex p)
      Cardinal.aleph0.{0} :=
  RelativeCellPresentability.vertex Cardinal.aleph0.{0}
    GoodCellTreeDataExamples.quotientTree.{t} GoodCellTreeDataExamples.quotientTreeGood.{t} p

/-- The original endpoint keeps its chosen under-root object and is presentable there. -/
theorem originalEndpointPresentable :
    IsCardinalPresentable GoodCellTreeDataExamples.quotientTree.{t}.endpointObj
      Cardinal.aleph0.{0} :=
  RelativeCellPresentability.endpoint Cardinal.aleph0.{0}
    GoodCellTreeDataExamples.quotientTree.{t} GoodCellTreeDataExamples.quotientTreeGood.{t}
    (hasCardinalLT_of_finite GoodCellTreeDataExamples.OneVertex Cardinal.aleph0.{0} le_rfl)

/-- Every chosen bounded lower piece retains the original lower-colimit dictionary. -/
theorem originalLowerPresentable (B : LowerSet GoodCellTreeDataExamples.OneVertex) :
    IsCardinalPresentable (GoodCellTreeDataExamples.quotientTree.{t}.lowerData.obj B)
      Cardinal.aleph0.{0} :=
  RelativeCellPresentability.lowerData Cardinal.aleph0.{0}
    GoodCellTreeDataExamples.quotientTree.{t} GoodCellTreeDataExamples.quotientTreeGood.{t} B
    (hasCardinalLT_of_finite (B : Set GoodCellTreeDataExamples.OneVertex)
      Cardinal.aleph0.{0} le_rfl)

/-- The original nonmonomorphic cell has its full same-choice free-under pushout. -/
theorem originalFreeUnderPushout (p : GoodCellTreeDataExamples.OneVertex) :
    IsPushout (transpose (GoodCellTreeDataExamples.quotientTree.{t}.attaching p))
      ((Under.costar ℕ).map
        (GoodCellTreeDataExamples.foldFamily
          (GoodCellTreeDataExamples.quotientTree.{t}.label p)).hom)
      (GoodCellTreeDataExamples.quotientTree.{t}.predecessorMap p)
      (transpose (GoodCellTreeDataExamples.quotientTree.{t}.cell p)) :=
  treeFreePushout GoodCellTreeDataExamples.quotientTree.{t} p

/-- The original attaching function is recovered through the original hom equivalence. -/
theorem originalAttachingFunction (p : GoodCellTreeDataExamples.OneVertex) :
    (Under.costarAdjForget ℕ).homEquiv _
      (GoodCellTreeDataExamples.quotientTree.{t}.predecessorObj p)
      (transpose (GoodCellTreeDataExamples.quotientTree.{t}.attaching p)) =
        GoodCellTreeDataExamples.quotientTree.{t}.attaching p :=
  congrFun (congrFun (congrFun transpose_homEquiv_function _) _) _

/-- The actual empty tree and its native root-adjoined colimit. -/
abbrev emptyAdjoinedColimit :
    ColimitCocone
      (adjoinedDiagram (Y := GoodCellTreeDataExamples.emptyTree.{t}.diagram)) :=
  adjoinedColimit GoodCellTreeDataExamples.emptyTree.{t}.endpoint

theorem emptyAdjoinedPoint : emptyAdjoinedColimit.{t}.cocone.pt = ℕ := rfl

/-- The actual empty-index star retains the original identity root function. -/
theorem emptyAdjoinedStar :
    emptyAdjoinedColimit.{t}.cocone.ι.app WithInitial.star = 𝟙 ℕ :=
  adjoined_star GoodCellTreeDataExamples.emptyTree.{t}.endpoint.cocone

/-- The same infinite root is not an initial object after arbitrary under-colimit forgetting. -/
theorem originalRootNotInitial : ¬ Nonempty (IsInitial (ℕ : Type)) := by
  rintro ⟨h⟩
  have hh := h.hom_ext (↾fun _ : ℕ => (0 : Fin 2)) (↾fun _ : ℕ => (1 : Fin 2))
  have he := ConcreteCategory.congr_hom hh 0
  change (0 : Fin 2) = 1 at he
  norm_num at he

/-- The original disconnected index has two literal discrete objects. -/
abbrev DisconnectedIndex := Discrete (Fin 2)

/-- Its original under-root diagram is the literal constant identity-root diagram. -/
abbrev disconnectedDiagram : DisconnectedIndex ⥤ Under ℕ :=
  (Functor.const DisconnectedIndex).obj (Under.mk (𝟙 ℕ))

/-- Retain the original chosen disconnected under-colimit cocone and universal property. -/
abbrev disconnectedColimit : ColimitCocone disconnectedDiagram :=
  ⟨colimit.cocone disconnectedDiagram, colimit.isColimit disconnectedDiagram⟩

/-- The SAME chosen cocone has the native original star adjoined. -/
abbrev disconnectedAdjoined :
    ColimitCocone (adjoinedDiagram (Y := disconnectedDiagram)) :=
  adjoinedColimit disconnectedColimit

theorem disconnectedAdjoinedPoint :
    disconnectedAdjoined.cocone.pt = disconnectedColimit.cocone.pt.right := rfl

/-- The full original root function survives the native disconnected extension. -/
theorem disconnectedStar :
    disconnectedAdjoined.cocone.ι.app WithInitial.star = disconnectedColimit.cocone.pt.hom :=
  adjoined_star disconnectedColimit.cocone

/-- Every original component function survives the native disconnected extension. -/
theorem disconnectedVertex (j : DisconnectedIndex) :
    disconnectedAdjoined.cocone.ι.app (WithInitial.of j) =
      (disconnectedColimit.cocone.ι.app j).right :=
  adjoined_vertex disconnectedColimit.cocone j

end RelativeCellPresentabilityExamples
