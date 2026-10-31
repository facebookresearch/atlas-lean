/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OffBoxRaySet

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OffBoxRaySet`

* `bc6_origin_notMem_rayInterior` along `e₁` of `ℤ²`, while `2 e₁` is in the ray interior of
  length `3` (instance).
* `bc6_farEnd_mem_armRegion` with `N = 1 < R = 2` in the all-closed configuration (instance).
* `bc6_offBoxCluster_subset_offBox` in the same setting.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OffBoxRaySet

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The origin is not in the ray interior, but `2 e₁` is.
example : (0 : Site 2) ∉ bc6_rayInterior 1 3 ∧ hrHD_rayPt (1 : Fin 2) 2 ∈ bc6_rayInterior 1 3 :=
  ⟨bc6_origin_notMem_rayInterior, ⟨2, ⟨by norm_num, by norm_num⟩, rfl⟩⟩

-- The far end lies in the arm region.
example : hrHD_rayPt (1 : Fin 2) ((2 : ℕ) : ℤ) ∈ bc6_armRegion 1 1 2 fun _ => false :=
  bc6_farEnd_mem_armRegion (by norm_num) _

-- The off-box cluster stays outside `B_1`.
example : bc6_offBoxCluster 1 (1 : Fin 2) 2 (fun _ => false) ⊆ (box 2 1)ᶜ :=
  bc6_offBoxCluster_subset_offBox

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OffBoxRaySet
