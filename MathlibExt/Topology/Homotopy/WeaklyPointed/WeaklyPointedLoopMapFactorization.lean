/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.LoopBasepointChange
public import MathlibExt.Topology.Homotopy.StrictLoopMap
public import MathlibExt.Topology.Homotopy.WeaklyPointedMap
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Factorization of weakly pointed loop maps

The loop map induced by a weakly pointed continuous map factors exactly as
strict postcomposition followed by change of basepoint along its chosen root
path.  The change-of-basepoint factor is a weak homotopy equivalence because
it is the forward map of the explicit loop-space homotopy equivalence.

This file does not assert that strict loop postcomposition preserves weak
homotopy equivalences, nor that a general weakly pointed loop map does so.  It
also makes no singular-comparison, loop-shift, spectrum, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

/-- Changing the basepoint of a loop along a path is a weak homotopy
equivalence. -/
theorem loopBasepointChange_mem_weakHomotopyEquivalences
    {x y : X} (p : Path x y) :
    TopCat.weakHomotopyEquivalences.{u}
      (TopCat.ofHom (loopBasepointChange p)) := by
  simpa only [loopBasepointChangeHomotopyEquiv_toFun] using
    (TopCat.homotopyEquiv_toFun_mem
      (loopBasepointChangeHomotopyEquiv p))

namespace WeaklyPointed

variable {Y : Type v} [TopologicalSpace Y] {x : X} {y : Y}

/-- A weakly pointed loop map is exactly strict loop postcomposition followed
by conjugation along the chosen root path. -/
theorem loopMap_eq_loopBasepointChange_comp_strictLoopMap
    (f : WeaklyPointed x y) :
    f.loopMap =
      (loopBasepointChange f.rootPath).comp
        (strictLoopMap f.hom x) := by
  apply ContinuousMap.ext
  intro gamma
  rfl

end WeaklyPointed

end ContinuousMap
