/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.DifferentialInequality
public import MathlibExt.Probability.Percolation.SharpnessTheorem
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessBeta

/-!
# The critical point `β̃_c` when `p_c < 1`

If `p_c(d) < 1`, then `p̃_c(d) < 1`, the critical inverse temperature `β̃_c` of the
`β`-parametrized percolation is positive, and the mean-field lower bound on `θ` holds above it.

## i. Overview

Bond percolation with parameter `p(β) = 1 - e^{-βJ}` has critical inverse temperature
`β̃_c = -log(1 - p̃_c)/J`. The results of `SharpnessBeta` need `p̃_c < 1` as a hypothesis. Here it
is derived from `p_c < 1` through the identity `p̃_c = p_c` (the sharpness theorem
`StatMech.Percolation.sharp_phase_transition`).

## ii. Key results

- `sh1_tildePc_lt_one_of_pc_lt_one` : `p_c(d) < 1 → p̃_c(d) < 1`
- `sh1_betaTildeC_pos_of_pc_lt_one` : `β̃_c > 0` when `p_c(d) < 1`
- `sh1_theta_ge_betaForm_of_pc_lt_one` : `θ(p(β)) ≥ (β - β̃_c)/β` for `β > β̃_c`

All three are proved; their only hypotheses are `p_c(d) < 1`, `d > 0` and `J > 0`.

## iii. Table of contents

- A. From `p_c < 1` to `p̃_c < 1`

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}

/-! ## A. From `p_c < 1` to `p̃_c < 1` -/

/-- `p̃_c(d) < 1` whenever `p_c(d) < 1`, since `p̃_c = p_c`. -/
lemma sh1_tildePc_lt_one_of_pc_lt_one (hd : 0 < d) (hpc : pc d < 1) :
    (tildePc d : ℝ) < 1 := by
  have heq : tildePc d = pc d := (StatMech.Percolation.sharp_phase_transition hd).1
  rw [heq]
  exact_mod_cast hpc

/-- The critical inverse temperature `β̃_c` is positive when `p_c(d) < 1`. -/
lemma sh1_betaTildeC_pos_of_pc_lt_one {J : ℝ} (hJ : 0 < J) (hd : 0 < d)
    (hpc : pc d < 1) :
    0 < betaTildeC d J :=
  betaTildeC_pos hJ hd (sh1_tildePc_lt_one_of_pc_lt_one hd hpc)

/-- Mean-field lower bound `θ(p(β)) ≥ (β - β̃_c)/β` for `β > β̃_c`, assuming `p_c(d) < 1`. -/
theorem sh1_theta_ge_betaForm_of_pc_lt_one {J β : ℝ} (hJ : 0 < J) (hd : 0 < d)
    (hpc : pc d < 1) (hβ : betaTildeC d J < β) :
    theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β)
      ≥ (β - betaTildeC d J) / β :=
  theta_ge_betaForm hJ hd (sh1_tildePc_lt_one_of_pc_lt_one hd hpc) hβ

end Sharpness

end StatMech
