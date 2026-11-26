/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercoSusceptibility
public import MathlibExt.Probability.Percolation.SurfaceReassembly

/-!
# Exponential decay below `β̃_c` for percolation

Below the finite-set critical point `β̃_c^{perc}`, the one-arm probability of bond percolation with
parameter `1 - e^{-β}` decays exponentially.

## i. Overview

`tildeBetaCPerco d` is the supremum of the `β ≥ 0` for which some finite set `S ∋ 0` has
`φ_β(S) < 1`. For `β` below it such a witness exists
(`exists_phiBeta_witness_of_lt_tildeBetaCPerco`), and the surface-reassembly argument of
`MathlibExt.Probability.Percolation.SurfaceReassembly` turns it into exponential decay of
`P_β(0 ↔ ∂Λ_n)`. The result is proved with no further hypotheses.

## ii. Key results

- `subcritical_decay_of_lt_tildeBetaCPerco` : exponential decay of the one-arm probability for
  `β < β̃_c^{perc}`

## iii. Table of contents

- A. Subcritical decay

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace StatMech
namespace Sharpness

open StatMech.Lattice Percolation

variable {d : ℕ}

/-! ## A. Subcritical decay -/

/-- **Subcritical exponential decay** (Duminil-Copin–Tassion 2016): for `β < β̃_c^{perc}`, the
one-arm probability satisfies `P_β(0 ↔ ∂Λ_n) ≤ C e^{-cn}` for some `c, C > 0`. -/
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
