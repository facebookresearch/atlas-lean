/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundaryPhi

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundaryPhi`

* `abbMag_meanfield_of_tildePc_le` on `Λ_1 ⊂ ℤ²`, conditional on `p̃_c ≤ p(β)`;
* `abbPhi_ge_one_of_tildePc_le` and `abbPhi_eq_phi` applied to a possible surface;
* the two combine to `φ_p(S') ≥ 1` for the percolation `φ`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundaryPhi

open _root_.StatMech _root_.StatMech.Sharpness

-- The mean-field inequality for the box magnetization above `p̃_c`.
example (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (hc : Percolation.tildePc 2 ≤ bondParam β) :
    1 - abbMag 2 1 β h ≤ β * deriv (fun b => abbMag 2 1 b h) β :=
  abbMag_meanfield_of_tildePc_le one_pos β h hβ hh hc

-- `φ(S) ≥ 1` for every possible surface above `p̃_c`.
example (S : Finset (Option (sctBox 2 1)))
    (hS : (mpiSurfaceEvent (withGhost (sctBoxGraph 2 1)) (abbTarget 2 1) S).Nonempty)
    (ho : some (sctBoxOrigin 2 1) ∈ S) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hc : Percolation.tildePc 2 ≤ bondParam β) : 1 ≤ abbPhi 2 1 β h S :=
  abbPhi_ge_one_of_tildePc_le one_pos hS ho β h hβ hh hc

-- Together with `abbPhi_eq_phi`: the percolation `φ` of the site set is at least `1`.
example (S : Finset (Option (sctBox 2 1)))
    (hS : (mpiSurfaceEvent (withGhost (sctBoxGraph 2 1)) (abbTarget 2 1) S).Nonempty)
    (ho : some (sctBoxOrigin 2 1) ∈ S) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hc : Percolation.tildePc 2 ≤ bondParam β) :
    ∃ hp : bondParam β ≤ 1, 1 ≤ Percolation.phi 2 (bondParam β) hp (abbSiteSurface 2 1 S) :=
  ⟨_, abbPhi_eq_phi one_pos hS ho β h hβ hh ▸
    abbPhi_ge_one_of_tildePc_le one_pos hS ho β h hβ hh hc⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundaryPhi
