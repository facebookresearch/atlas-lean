/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Code.Sharpness.Item1Htc1
import Code.Sharpness.BetaReparam

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}














theorem sas_betaTildeC_lt_iff {J β : ℝ} (hJ : 0 < J) (hd : 0 < d) (hpc : pc d < 1) :
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





theorem sas_lt_betaTildeC_iff {J β : ℝ} (hJ : 0 < J) (hd : 0 < d) (hpc : pc d < 1) :
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
  refine ⟨(sharpness_unconditional hd).1, ?_, ?_, ?_⟩
  · 
    intro β
    exact sas_betaTildeC_lt_iff hJ hd hpc
  · 
    intro β hmem
    obtain ⟨hp, S, h0S, hphi⟩ := mem_tildePcSet.mp hmem
    
    have hphi' : phi d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) S < 1 := by
      rwa [Subsingleton.elim (pBeta_toNNReal_le_one J β) hp]
    have h0S' : origin d ∈ (S : Set (Site d)) := by exact_mod_cast h0S
    
    obtain ⟨N, hSN⟩ := finset_subset_box_su S
    have hSbox : (S : Set (Site d)) ⊆ box d ((N + 1) - 1) := by
      rw [Nat.add_sub_cancel]; exact hSN
    exact shr_item3_beta J β S h0S' hphi' (N + 1) (by omega) hSbox
  · 
    intro β hβ
    exact sh1_theta_ge_betaForm_of_pc_lt_one hJ hd hpc hβ

end Sharpness

end StatMech
