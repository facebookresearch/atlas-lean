/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.StrictLoopMapWeakHomotopy
public import
  MathlibExt.Topology.Homotopy.WeaklyPointed.WeaklyPointedLoopMapFactorization

/-!
# Weakly pointed loop maps preserve weak homotopy equivalences

A weakly pointed loop map factors strictly as loop postcomposition followed
by change of basepoint along the chosen root path.  The first factor preserves
weak homotopy equivalences and the second is a homotopy equivalence, so their
composite is a weak homotopy equivalence.

The source and target spaces live in one universe.  No path-connectedness or
well-pointedness assumption, Q/S specialization, spectrum map, inverse, or
stronger equivalence is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

namespace ContinuousMap.WeaklyPointed

/-- A weakly pointed map that is a weak homotopy equivalence induces a weak
homotopy equivalence on its chosen-basepoint loop spaces. -/
theorem loopMap_mem_weakHomotopyEquivalences
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : ContinuousMap.WeaklyPointed x y)
    (hf : TopCat.weakHomotopyEquivalences (TopCat.ofHom f.hom)) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom f.loopMap) := by
  rw [loopMap_eq_loopBasepointChange_comp_strictLoopMap,
    TopCat.ofHom_comp]
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _
    (ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences
      f.hom x hf)
    (ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences
      f.rootPath)

end ContinuousMap.WeaklyPointed
