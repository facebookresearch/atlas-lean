/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PcUpperViaFK
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessAssembly

/-!
# Sharpness in the `β`-parametrization for `d ≥ 2`

The `β`-form sharpness theorem and the mean-field lower bound on `θ` for `d ≥ 2`, with the
hypothesis `p_c(d) < 1` discharged.

## i. Overview

`sas_sharpness_betaForm` and `sh1_theta_ge_betaForm_of_pc_lt_one` assume `p_c(d) < 1`. For `d ≥ 2`
this holds by `StatMech.Percolation.pc_nontrivial_of_two_le` (proved via the random-cluster
comparison in `PcUpperViaFK`), so the results here are unconditional apart from `d ≥ 2` and
`J > 0`.

## ii. Key results

- `theta_ge_betaForm_of_two_le` : `θ(p(β)) ≥ (β - β̃_c)/β` for `β > β̃_c`
- `theta_ge_betaForm_of_two_le_closed` : the same for `β ≥ β̃_c`
- `sharpness_betaForm_of_two_le` : the sharpness theorem in the `β`-parametrization

## iii. Table of contents

- A. Sharpness for `d ≥ 2`

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
-/

@[expose] public section

open scoped NNReal ENNReal

namespace StatMech.Sharpness

open StatMech.Percolation

/-! ## A. Sharpness for `d ≥ 2` -/

/-- **Mean-field lower bound** for `d ≥ 2`: `θ(p(β)) ≥ (β - β̃_c)/β` for `β > β̃_c`. -/
theorem theta_ge_betaForm_of_two_le {d : ℕ} {J beta : ℝ}
    (hd : 2 ≤ d) (hJ : 0 < J) (hbeta : betaTildeC d J < beta) :
    theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥
      (beta - betaTildeC d J) / beta := by
  exact sh1_theta_ge_betaForm_of_pc_lt_one hJ (by omega)
    (pc_nontrivial_of_two_le hd).2 hbeta

/-- The mean-field lower bound for `d ≥ 2` and `β ≥ β̃_c` (at `β = β̃_c` the bound is `0`). -/
theorem theta_ge_betaForm_of_two_le_closed {d : ℕ} {J beta : ℝ}
    (hd : 2 ≤ d) (hJ : 0 < J) (hbeta : betaTildeC d J ≤ beta) :
    theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥
      (beta - betaTildeC d J) / beta := by
  rcases hbeta.eq_or_lt with rfl | hbeta
  · simpa using theta_nonneg d (pBeta J (betaTildeC d J)).toNNReal
      (pBeta_toNNReal_le_one J (betaTildeC d J))
  · exact theta_ge_betaForm_of_two_le hd hJ hbeta

/-- **Sharpness of the phase transition** (Duminil-Copin–Tassion 2016) for `d ≥ 2` in the
`β`-parametrization, with no hypothesis on `p_c`. -/
theorem sharpness_betaForm_of_two_le {d : ℕ} {J : ℝ}
    (hd : 2 ≤ d) (hJ : 0 < J) :
    tildePc d = pc d
      ∧ (∀ beta : ℝ,
          betaTildeC d J < beta ↔ (tildePc d : ℝ) < pBeta J beta)
      ∧ (∀ beta : ℝ, (pBeta J beta).toNNReal ∈ tildePcSet d →
          ∃ c > 0, ∃ C > 0, ∀ n,
            crossProb d (pBeta J beta).toNNReal
                (pBeta_toNNReal_le_one J beta) n ≤
              C * Real.exp (-c * n))
      ∧ (∀ beta : ℝ, betaTildeC d J < beta →
          theta d (pBeta J beta).toNNReal
              (pBeta_toNNReal_le_one J beta) ≥
            (beta - betaTildeC d J) / beta) := by
  exact sas_sharpness_betaForm hJ (by omega) (pc_nontrivial_of_two_le hd).2

end StatMech.Sharpness
