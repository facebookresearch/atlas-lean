/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.NeuralNetworks.BarronApproximation

open MeasureTheory

namespace CSLibExt.MachineLearning.NeuralNetworks

-- The hypotheses are satisfiable: a single neuron has finite Barron norm, so it is approximated
-- at the rate `3 ‖f‖_B² / m` by width-`m` networks for any probability measure on the cube, here
-- the Dirac mass at the origin.
example (d m : ℕ) (hm : 0 < m) (θ : ℝ × (Fin d → ℝ) × ℝ) :
    ∃ θs : Fin m → ℝ × (Fin d → ℝ) × ℝ,
      ∫⁻ x, ‖reluNeuron θ x - (m : ℝ)⁻¹ * ∑ k, reluNeuron (θs k) x‖ₑ ^ 2 ∂(Measure.dirac 0) ≤
          3 * barronNorm (reluNeuron θ) ^ 2 / m ∧
        (m : ENNReal)⁻¹ * ∑ k, ‖(θs k).1‖ₑ * (∑ j, ‖(θs k).2.1 j‖ₑ + ‖(θs k).2.2‖ₑ) ≤
          2 * barronNorm (reluNeuron θ) := by
  refine barron_direct_approximation _ ((barronNorm_neuron_le θ).trans_lt ?_) _ ?_ hm
  · exact ENNReal.mul_lt_top (by simp) (by simp)
  · have h0 : (0 : Fin d → ℝ) ∈ unitCube d := Set.mem_univ_pi.2 fun _ => by simp
    rw [Measure.dirac_apply]
    simp [h0]

end CSLibExt.MachineLearning.NeuralNetworks
