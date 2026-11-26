/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.NeuralNetworks.BarronInverseApproximation

/-!
# Tests for the inverse approximation theorem for the Barron space

Two edge cases of `barron_inverse_approximation`: networks with a nonzero output coefficient whose
path norm is zero at every width, and networks whose output coefficients are unbounded while their
path norms stay at most one and their outputs converge to a nonzero limit.
-/

namespace CSLibExt.MachineLearning.NeuralNetworks

open Filter Topology

-- Nonzero output coefficients can still give a network of path norm zero at every width.
example (d : ℕ) :
    (∃ ρ, IsBarronRepresentation (fun _ : Fin d → ℝ => 0) ρ) ∧
      barronNorm (fun _ : Fin d → ℝ => 0) ≤ 0 := by
  simpa only [ENNReal.ofReal_zero] using
    barron_inverse_approximation (fun _ : Fin d → ℝ => 0) continuousOn_const 0
      (fun k => k + 1) (fun _ => Nat.zero_lt_succ _) (fun _ _ => (7, 0, 0))
      (by intro k; simp) (by intro x _; simp [reluNeuron])

-- Even on the zero-dimensional cube, a nonzero bias matters. The output coefficients
-- tend to minus infinity, the path norms stay below one, and the outputs −k/(k+1) tend to −1.
example :
    (∃ ρ, IsBarronRepresentation (fun _ : Fin 0 → ℝ => -1) ρ) ∧
      barronNorm (fun _ : Fin 0 → ℝ => -1) ≤ 1 := by
  let r (k : ℕ) : ℝ := k + 1
  have hr k : 0 < r k := by dsimp [r]; positivity
  have hlim : Tendsto (fun k => (r k)⁻¹ - 1) atTop (𝓝 (-1)) := by
    simpa [r, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.sub_const (1 : ℝ)
  simpa only [ENNReal.ofReal_one] using
    barron_inverse_approximation (fun _ : Fin 0 → ℝ => -1) continuousOn_const 1
      (fun _ => 1) (fun _ => Nat.zero_lt_one) (fun k _ => (-(k : ℝ), 0, (r k)⁻¹))
      (by
        intro k
        simpa [abs_of_pos (hr k), ← div_eq_mul_inv, div_le_one (hr k)] using
          (show (k : ℝ) ≤ r k by dsimp [r]; linarith))
      (by
        intro x _
        apply hlim.congr fun k => ?_
        simp only [Nat.cast_one, inv_one, Fin.sum_univ_one, one_mul, reluNeuron,
          Finset.univ_eq_empty, Finset.sum_empty, zero_add, max_eq_left (inv_nonneg.mpr (hr k).le)]
        field_simp [(hr k).ne']
        simp [r])

end CSLibExt.MachineLearning.NeuralNetworks
