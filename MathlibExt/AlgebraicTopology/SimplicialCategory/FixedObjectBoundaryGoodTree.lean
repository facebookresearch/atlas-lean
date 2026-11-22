/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLocallyFinitelyPresentable
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFactorizations
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellTreeGoodification
import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeSmallObjectPresentation

/-!
# The same original boundary cells have genuine countable predecessor supports

Local finite presentability of the original fixed-label category permits
the existing full cell-tree refinement at the first uncountable regular
rank. It preserves the SAME native cell occurrences, original generator
arrows and source-fixed endpoint comparison. Each original predecessor
support is genuinely countable. No selected weak interval is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject MonoidalCategory
open scoped Simplicial
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryGoodTree
open NativeSmallObjectPresentation OriginalGoodification
variable {O : Type u} {C D : FixedObjects O}

/-- The first uncountable regular rank is used solely to bound actual original predecessor supports. -/
abbrev rank : Cardinal.{u} := Cardinal.aleph 1

/-- The SAME first uncountable rank is genuinely regular. -/
instance rank_regular : Fact rank.{u}.IsRegular := ⟨Cardinal.isRegular_aleph_one⟩

/-- The actual original category is locally presentable at that SAME rank by its proved free simplex generator. -/
instance original_locallyPresentable : IsCardinalLocallyPresentable (FixedObjects O) rank.{u} :=
  locallyPresentable_of_aleph0_le O rank Cardinal.aleph0_lt_aleph_one.le

/-- Every original boundary source is genuinely compact at the SAME predecessor rank. -/
theorem source_presentable (i : (boundaryFamily O).toSet) :
    IsCardinalPresentable i.val.left rank.{u} := by
  have h := boundaryFamily_domains_compact i.val.hom i.property
  exact (isCardinalPresentable_monotone (FixedObjects O)
    Cardinal.aleph0_lt_aleph_one.le) _ h

/-- Every original boundary target is genuinely compact at that SAME rank, including all loop cells. -/
theorem target_presentable (i : (boundaryFamily O).toSet) :
    IsCardinalPresentable i.val.right rank.{u} := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨x, y, n⟩⟩ := hf
  have h : IsFinitelyPresentable.{u} (FreeSingleHom.object x y (Δ[n] : SSet.{u})) :=
    inferInstance
  exact (isCardinalPresentable_monotone (FixedObjects O)
    Cardinal.aleph0_lt_aleph_one.le) _ h

variable (f : C ⟶ D)

/-- The complete SAME original native boundary cell tree, retaining its original countable iteration. -/
abbrev original := nativeTree (boundaryFamily O) Cardinal.aleph0.{u} f

/-- The actual original native occurrences are retained as the SAME cell carrier. -/
abbrev Cells := (SmallObject.relativeCellComplexιObj (boundaryFamily O) Cardinal.aleph0.{u} f).Cells

/-- The genuine original cell-tree refinement is constructed from actual compact original cell ends. -/
def refinement := cellTreeGoodification (original f) (original f).lowerData rank.{u}
  (fun p => source_presentable ((original f).label p))
  (fun p => target_presentable ((original f).label p))

/-- Retain the actual original cell carrier, labels and endpoint with its internally refined good order. -/
structure Data where
  /-- The genuinely refined order on the SAME original native occurrences. -/
  order : PartialOrder (Cells f)
  /-- The full original-root cell tree with every actual original generator retained. -/
  tree : @CellTree (FixedObjects O) inferInstance (Cells f) order
    (boundaryFamily O).toSet (generatorArrows (boundaryFamily O)) C
  /-- Its actual original lower colimit choices. -/
  lowerData : @LowerSetColimitData (Cells f) order.toPreorder (Under C) inferInstance tree.diagram
  /-- The full actual endpoint comparison under the SAME original source. -/
  endpointIso : tree.endpointObj ≅ Under.mk (FreeFactorization.boundary f).i
  /-- Every original native cell occurrence retains its literal original family label. -/
  labels : ∀ p : Cells f, tree.label p = p.i
  /-- Compactness and original predecessor bounds are genuine derived conclusions. -/
  good : @CellTree.IsGood (FixedObjects O) inferInstance (Cells f) order
    (boundaryFamily O).toSet (generatorArrows (boundaryFamily O)) C tree rank.{u} inferInstance

/-- Produce the SAME original full boundary tree with countable original predecessor supports. -/
def data : Data f := by
  let oldOrder : PartialOrder (Cells f) := inferInstance
  let T₀ := original f
  let L₀ := (original f).lowerData
  let G := refinement f
  let outOrder := @CellTreeGoodification.order (Cells f) oldOrder (FixedObjects O)
    inferInstance inferInstance (boundaryFamily O).toSet (generatorArrows (boundaryFamily O))
    C T₀ L₀ rank.{u} inferInstance G
  let T := @CellTreeGoodification.tree (Cells f) oldOrder (FixedObjects O)
    inferInstance inferInstance (boundaryFamily O).toSet (generatorArrows (boundaryFamily O))
    C T₀ L₀ rank.{u} inferInstance G
  let L := @CellTreeGoodification.lowerData (Cells f) oldOrder (FixedObjects O)
    inferInstance inferInstance (boundaryFamily O).toSet (generatorArrows (boundaryFamily O))
    C T₀ L₀ rank.{u} inferInstance G
  let e := @CellTreeGoodification.endpointIso (Cells f) oldOrder (FixedObjects O)
    inferInstance inferInstance (boundaryFamily O).toSet (generatorArrows (boundaryFamily O))
    C T₀ L₀ rank.{u} inferInstance G
  exact {
    order := outOrder
    tree := T
    lowerData := L
    endpointIso := e
    labels := fun p => @CellTreeGoodification.labels (Cells f) oldOrder (FixedObjects O)
      inferInstance inferInstance (boundaryFamily O).toSet (generatorArrows (boundaryFamily O))
      C T₀ L₀ rank.{u} inferInstance G p
    good := @CellTreeGoodification.good (Cells f) oldOrder (FixedObjects O)
      inferInstance inferInstance (boundaryFamily O).toSet (generatorArrows (boundaryFamily O))
      C T₀ L₀ rank.{u} inferInstance G }

end CategoryTheory.SimplicialEnrichment.FixedObjects.OriginalBoundaryGoodTree
