/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.WeaklyPointedLoopMapWeakHomotopy
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagWeaklyPointed

/-!
# Weak homotopy equivalences in the Quillen Q/S loop zigzag

The four previously defined weakly pointed loop maps in the Quillen Q/S
zigzag are weak homotopy equivalences.  The first three results concern the
elementary legs; the fourth concerns the already named factored right leg.

The factored map is not asserted to be strictly equal to the composite of the
two elementary loop maps.  This file defines no chosen endpoint map, inverse,
homotopy equivalence, localization, or spectrum map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The Waldhausen category structure on `C` from its exact structure, as a local instance. -/
local instance quillenQSZigzagLoopWeakEquivalenceWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The Q-side loop map in the Quillen Q/S zigzag is a weak homotopy
equivalence. -/
theorem quillenStageGridToNQLoopMap_mem_weakHomotopyEquivalences :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (quillenStageGridToNQLoopMap (C := C))) := by
  apply ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences
    (quillenStageGridToNQWeaklyPointed (C := C))
  change SSet.realizationWeakEquivalences
    (quillenStageGridToNQ (C := C))
  exact quillenStageGridToNQ_mem_realizationWeakEquivalences (C := C)

/-- The Stage-grid projection loop map in the Quillen Q/S zigzag is a weak
homotopy equivalence. -/
theorem quillenStageGridStageProjectionLoopMap_mem_weakHomotopyEquivalences :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom
        (quillenStageGridStageProjectionLoopMap (C := C))) := by
  apply ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences
    (quillenStageGridStageProjectionWeaklyPointed (C := C))
  change SSet.realizationWeakEquivalences
    (quillenStageGridStageProjectionDiagonal (C := C))
  exact
    quillenStageGridStageProjectionDiagonal_mem_realizationWeakEquivalences
      (C := C)

/-- The outer-edgewise Stage-comparison loop map in the Quillen Q/S zigzag
is a weak homotopy equivalence. -/
theorem outerEdgewiseStageDiagonalComparisonLoopMap_mem_weakHomotopyEquivalences :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom
        (outerEdgewiseStageDiagonalComparisonLoopMap (C := C))) := by
  apply ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences
    (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C))
  change SSet.realizationWeakEquivalences
    (outerEdgewiseStageDiagonalComparison (C := C))
  exact
    outerEdgewiseStageDiagonalComparison_mem_realizationWeakEquivalences
      (C := C)

/-- The named factored right loop map in the Quillen Q/S zigzag is a weak
homotopy equivalence. -/
theorem quillenStageGridToStageLoopMap_mem_weakHomotopyEquivalences :
    TopCat.weakHomotopyEquivalences
      (TopCat.ofHom (quillenStageGridToStageLoopMap (C := C))) := by
  apply ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences
    (quillenStageGridToStageWeaklyPointed (C := C))
  rw [quillenStageGridToStageWeaklyPointed_hom]
  change SSet.realizationWeakEquivalences
    (quillenStageGridToStageWeakDiagonal (C := C))
  exact
    quillenStageGridToStageWeakDiagonal_mem_realizationWeakEquivalences
      (C := C)

end AlgebraicKTheory

end
