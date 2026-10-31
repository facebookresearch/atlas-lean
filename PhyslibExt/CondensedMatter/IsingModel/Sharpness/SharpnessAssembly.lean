/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.TildePcBetaForm
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.BetaReparam

/-!
# Sharpness of the phase transition in the `β`-parametrization

The Duminil-Copin–Tassion sharpness theorem for bond percolation, stated for the parameter
`p(β) = 1 - e^{-βJ}`.

## i. Overview

For `d > 0`, `J > 0` and `p_c(d) < 1`, `sas_sharpness_betaForm` collects four facts: `p̃_c = p_c`;
`β > β̃_c` iff `p(β) > p̃_c`; exponential decay of the one-arm probability when `p(β)` lies in the
subcritical set `tildePcSet`; and the mean-field bound `θ(p(β)) ≥ (β - β̃_c)/β` above `β̃_c`. It is
proved with no hypotheses beyond `d > 0`, `J > 0` and `p_c(d) < 1`; `SharpnessBetaFormDimTwo`
discharges the last one for `d ≥ 2`.

## ii. Key results

- `sas_betaTildeC_lt_iff`, `sas_lt_betaTildeC_iff` : comparing `β` with `β̃_c` is comparing
  `p(β)` with `p̃_c`
- `sas_sharpness_betaForm` : sharpness of the phase transition in the `β`-parametrization

## iii. Table of contents

- A. Comparison of `β` with `β̃_c`
- B. The sharpness theorem

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

/-! ## A. Comparison of `β` with `β̃_c` -/

/-- `β > β̃_c` iff `p(β) > p̃_c`, when `p_c(d) < 1`. -/
lemma sas_betaTildeC_lt_iff {J β : ℝ} (hJ : 0 < J) (hd : 0 < d) (hpc : pc d < 1) :
    betaTildeC d J < β ↔ (tildePc d : ℝ) < pBeta J β := by
  have htc1 : (tildePc d : ℝ) < 1 := sh1_tildePc_lt_one_of_pc_lt_one hd hpc
  have hval : pBeta J (betaTildeC d J) = (tildePc d : ℝ) := pBeta_betaTildeC hJ htc1
  constructor
  · intro h
    have := pBeta_strictMono hJ h
    rwa [hval] at this
  · intro h
    rw [← hval] at h
    exact (pBeta_strictMono hJ).lt_iff_lt.mp h

/-- `β < β̃_c` iff `p(β) < p̃_c`, when `p_c(d) < 1`. -/
lemma sas_lt_betaTildeC_iff {J β : ℝ} (hJ : 0 < J) (hd : 0 < d) (hpc : pc d < 1) :
    β < betaTildeC d J ↔ pBeta J β < (tildePc d : ℝ) := by
  have htc1 : (tildePc d : ℝ) < 1 := sh1_tildePc_lt_one_of_pc_lt_one hd hpc
  have hval : pBeta J (betaTildeC d J) = (tildePc d : ℝ) := pBeta_betaTildeC hJ htc1
  constructor
  · intro h
    have := pBeta_strictMono hJ h
    rwa [hval] at this
  · intro h
    rw [← hval] at h
    exact (pBeta_strictMono hJ).lt_iff_lt.mp h

/-! ## B. The sharpness theorem -/

/-- **Sharpness of the phase transition** (Duminil-Copin–Tassion 2016) in the `β`-parametrization:
for `d > 0`, `J > 0` and `p_c(d) < 1`, `p̃_c = p_c`, `β > β̃_c ↔ p(β) > p̃_c`, the one-arm
probability decays exponentially when `p(β) ∈ tildePcSet d`, and `θ(p(β)) ≥ (β - β̃_c)/β` for
`β > β̃_c`. -/
theorem sas_sharpness_betaForm {J : ℝ} (hJ : 0 < J) (hd : 0 < d) (hpc : pc d < 1) :
    tildePc d = pc d
      ∧ (∀ β : ℝ, (betaTildeC d J < β ↔ (tildePc d : ℝ) < pBeta J β))
      ∧ (∀ β : ℝ, (pBeta J β).toNNReal ∈ tildePcSet d →
          ∃ c > 0, ∃ C > 0, ∀ n,
            crossProb d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) n
              ≤ C * Real.exp (-c * n))
      ∧ (∀ β : ℝ, betaTildeC d J < β →
          theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β)
            ≥ (β - betaTildeC d J) / β) := by
  refine ⟨(StatMech.Percolation.sharp_phase_transition hd).1, ?_, ?_, ?_⟩
  · intro β
    exact sas_betaTildeC_lt_iff hJ hd hpc
  · intro β hmem
    obtain ⟨hp, S, h0S, hphi⟩ := mem_tildePcSet.mp hmem
    have hphi' : phi d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) S < 1 := by
      rwa [Subsingleton.elim (pBeta_toNNReal_le_one J β) hp]
    have h0S' : origin d ∈ (S : Set (Site d)) := by exact_mod_cast h0S
    obtain ⟨N, hSN⟩ :=
      StatMech.Lattice.finite_subset_box ((S : Finset (Site d)) : Set (Site d))
        (Set.toFinite _)
    have hSbox : (S : Set (Site d)) ⊆ box d ((N + 1) - 1) := by
      rw [Nat.add_sub_cancel]; exact hSN
    exact shr_item3_beta J β S h0S' hphi' (N + 1) (by omega) hSbox
  · intro β hβ
    exact sh1_theta_ge_betaForm_of_pc_lt_one hJ hd hpc hβ

end Sharpness

end StatMech
