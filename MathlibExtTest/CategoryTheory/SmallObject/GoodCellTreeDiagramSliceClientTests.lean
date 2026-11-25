/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceIntersection
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.OriginalSliceFilteredUnion
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramActionCapture

/-!
# Diagram-slice clients on concrete uncountable-rank fold data

The inputs are the component trees `originalTrees`, their chosen lower colimits
`originalLower`, the uncountable regular rank `chi` with `chi_uncountable`, the arrow bound
`originalArrowBound`, goodness `originalTrees_good` and the nonempty seeds `nonemptySeeds`
from the diagram-action capture tests.

The clients check:
* `DiagramSliceIntersection.existsGenericBoundedCompatibleIntersection` for the empty original
  slice, seeded at `nonemptySeeds`: there are bounded slices `N` and `N'` such that `N`
  contains the seeds, `N'` has supports the intersection with `N`, and `N'` includes naturally
  into both;
* `DiagramSliceExtensions.cardinalFiltered`: the bounded slices form a `chi`-filtered category;
* `DiagramSliceExhaustion.isColimit`: the endpoint cocone over the bounded slices is a colimit.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open OriginalDiagramActionCaptureExamples DiagramActionConstraintBoundExamples

set_option autoImplicit false

noncomputable section

universe t

@[expose] public section

namespace MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramSliceClient

/-- A bounded compatible intersection with the empty original slice, seeded at a nonempty
support. -/
theorem concreteIntersection :
    ∃ (N Nprime : DiagramSliceExtensions.Slice originalTrees.{t} originalLower.{t} chi),
      (∀ d, nonemptySeeds.{t} d ≤ N.supports d) ∧
      (∀ d, (Nprime.supports d).1 =
        (OriginalSliceFilteredUnion.empty (theta := originalTrees.{t})
          (L := originalLower.{t})).supports d ⊓ (N.supports d).1) ∧
      Nonempty (DiagramSliceExhaustion.OriginalSlice.Inclusion
        (DiagramSliceExhaustion.OriginalSlice.ofBounded chi Nprime)
        (OriginalSliceFilteredUnion.empty (theta := originalTrees.{t})
          (L := originalLower.{t}))) ∧
      Nonempty (DiagramSliceExhaustion.OriginalSlice.Inclusion
        (DiagramSliceExhaustion.OriginalSlice.ofBounded chi Nprime)
        (DiagramSliceExhaustion.OriginalSlice.ofBounded chi N)) :=
  DiagramSliceIntersection.existsGenericBoundedCompatibleIntersection originalTrees.{t}
    originalLower.{t} _ chi chi_uncountable originalArrowBound originalTrees_good.{t}
    nonemptySeeds.{t}

/-- The bounded slices form a `chi`-filtered category. -/
theorem concreteCardinalFiltered :
    IsCardinalFiltered
      (DiagramSliceExtensions.Slice originalTrees.{t} originalLower.{t} chi) chi :=
  DiagramSliceExtensions.cardinalFiltered originalTrees.{t} originalLower.{t} chi
    originalArrowBound originalTrees_good.{t} chi_uncountable

/-- The endpoint cocone over the bounded slices is a colimit. -/
def concreteExhaustion :
    IsColimit (DiagramSliceExtensions.Slice.endpointCocone (theta := originalTrees.{t})
      (L := originalLower.{t}) (chi := chi)) :=
  DiagramSliceExhaustion.isColimit originalTrees.{t} originalLower.{t} chi originalArrowBound
    originalTrees_good.{t} chi_uncountable

#print axioms concreteIntersection
#print axioms concreteCardinalFiltered
#print axioms concreteExhaustion

end MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramSliceClient

end
