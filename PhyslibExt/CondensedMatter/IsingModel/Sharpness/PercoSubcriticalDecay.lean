/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercoSusceptibility
public import MathlibExt.Probability.Percolation.SurfaceReassembly

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace StatMech
namespace Sharpness

open Lattice Percolation

variable {d : ℕ}





theorem subcritical_decay_of_lt_tildeBetaCPerco {beta : ℝ}
    (hbeta : beta < tildeBetaCPerco d) :
    ∃ c > 0, ∃ C > 0, ∀ n,
      crossProb d (bondParam beta) (bondParam_le_one beta) n
        ≤ C * Real.exp (-c * n) := by
  obtain ⟨S, h0S, hphi⟩ :=
    exists_phiBeta_witness_of_lt_tildeBetaCPerco (d := d) hbeta
  obtain ⟨N, hSN⟩ :=
    StatMech.Lattice.finite_subset_box ((S : Finset (Site d)) : Set (Site d))
      (Set.toFinite _)
  have hSbox : (S : Set (Site d)) ⊆ box d ((N + 1) - 1) := by
    rw [Nat.add_sub_cancel]
    exact hSN
  exact StatMech.Percolation.crossProb_exp_decay_of_phi_lt_one
    (bondParam beta) (bondParam_le_one beta) S h0S hphi
    (N + 1) (by omega) hSbox

end Sharpness
end StatMech
