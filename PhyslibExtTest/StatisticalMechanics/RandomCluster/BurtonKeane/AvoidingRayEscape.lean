/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayEscape

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayEscape`

* `bc33_TavoidingRay_nonvacuous`: an explicit configuration with a `T`-avoiding ray;
* `bc33_arc_ray`: the explicit ray starts at `arc_p 1`;
* `bc33_injRay_escapes_box` for the explicit injective sequence `k ↦ arc_p k`;
* `bc33_Tcount_le_boundary_of_TavoidingRayData` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayEscape

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The avoiding-ray hypothesis is satisfiable.
example := bc33_TavoidingRay_nonvacuous

-- The explicit ray starts at `arc_p 1` and is injective.
example : Function.Injective (fun k : ℕ => arc_p (1 + (k : ℤ))) := bc33_arc_ray.2.1

-- An injective sequence leaves every box.
example : ∃ j : ℕ, arc_p (j : ℤ) ∉ box 2 3 :=
  bc33_injRay_escapes_box (fun k : ℕ => arc_p k) (arc_p_inj.comp Nat.cast_injective) 3

-- The count route from avoiding-ray data, by type.
example := @bc33_Tcount_le_boundary_of_TavoidingRayData

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingRayEscape
