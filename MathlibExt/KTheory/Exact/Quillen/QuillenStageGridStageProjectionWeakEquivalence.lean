/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import
  MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridStageProjectionRows

/-!
# Weak equivalence of the Quillen Stage-grid projection

Every fixed-inner-degree row of the transposed Stage-grid projection is the
base change of the source map from the nerve of isomorphism arrows.  The
isomorphism-arrow contraction therefore makes each such row a realization
weak equivalence.  The inner-row diagonal theorem then promotes these column
results to the diagonal Stage-grid projection.

This file does not assert a fixed-outer-degree weak equivalence.  It also makes
no outer-edgewise, ordinary Stage-diagonal, Q/S, pointed, or loop-space claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The canonical Waldhausen structure used by the original Stage-grid projection weak comparison. -/
local instance quillenStageGridStageProjectionWeakEquivalenceWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- Every fixed-inner-degree row of the transposed Stage-grid projection is a
realization weak equivalence. -/
theorem quillenStageGridStageProjectionRow_mem_realizationWeakEquivalences
    (m : ℕ) :
    SSet.realizationWeakEquivalences
      ((SSet.simplicialTransposeFunctor.map
        (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌)) := by
  rw [← quillenStageGridStageProjectionRowPullbackIso_hom_fst (C := C) m]
  exact MorphismProperty.RespectsIso.precomp SSet.realizationWeakEquivalences
    (quillenStageGridStageProjectionRowPullbackIso (C := C) m).hom _
    (CategoryTheory.isomorphismArrowNerveSource_baseChange_mem_realizationWeakEquivalences
      (QuillenQ C) (edgewiseStageWeakRowLast (C := C) m))

/-- The diagonal Stage-grid projection to the outer-edgewise weak-Stage nerve
is a realization weak equivalence. -/
theorem quillenStageGridStageProjectionDiagonal_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (quillenStageGridStageProjectionDiagonal (C := C)) := by
  change SSet.realizationWeakEquivalences
    (SSet.simplicialDiagonalFunctor.map
      (quillenStageGridStageProjectionNerve (C := C)))
  apply
    SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
  intro m
  exact
    quillenStageGridStageProjectionRow_mem_realizationWeakEquivalences
      (C := C) m

end AlgebraicKTheory

end
