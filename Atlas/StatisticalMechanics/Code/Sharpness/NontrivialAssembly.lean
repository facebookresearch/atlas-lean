/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Percolation.PcUpperViaFK
import Code.Sharpness.SharpnessAssembly

open scoped NNReal ENNReal

namespace StatMech.Sharpness

open StatMech.Percolation



theorem theta_ge_betaForm_of_two_le {d : ℕ} {J beta : ℝ}
    (hd : 2 ≤ d) (hJ : 0 < J) (hbeta : betaTildeC d J < beta) :
    theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥
      (beta - betaTildeC d J) / beta := by
  exact sh1_theta_ge_betaForm_of_pc_lt_one hJ (by omega)
    (pc_nontrivial_of_two_le hd).2 hbeta


theorem theta_ge_betaForm_of_two_le_closed {d : ℕ} {J beta : ℝ}
    (hd : 2 ≤ d) (hJ : 0 < J) (hbeta : betaTildeC d J ≤ beta) :
    theta d (pBeta J beta).toNNReal (pBeta_toNNReal_le_one J beta) ≥
      (beta - betaTildeC d J) / beta := by
  rcases hbeta.eq_or_lt with rfl | hbeta
  · simpa using theta_nonneg d (pBeta J (betaTildeC d J)).toNNReal
      (pBeta_toNNReal_le_one J (betaTildeC d J))
  · exact theta_ge_betaForm_of_two_le hd hJ hbeta



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
