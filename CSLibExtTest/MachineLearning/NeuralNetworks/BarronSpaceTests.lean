/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.NeuralNetworks.BarronSpace

namespace CSLibExt.MachineLearning.NeuralNetworks

-- The origin lies in the cube.
example (d : ℕ) : (0 : Fin d → ℝ) ∈ unitCube d :=
  Set.mem_univ_pi.2 fun _ => by simp

-- The neuron with `a = 1`, `b = 0`, `c = 1` is the constant `1`.
example (d : ℕ) (x : Fin d → ℝ) : reluNeuron ((1, 0, 1) : ℝ × (Fin d → ℝ) × ℝ) x = 1 := by
  simp [reluNeuron]

-- So the constant function `1` has Barron norm at most `1`: the norm is not identically `∞`.
example (d : ℕ) : barronNorm (reluNeuron ((1, 0, 1) : ℝ × (Fin d → ℝ) × ℝ)) ≤ 1 := by
  simpa using barronNorm_neuron_le ((1, 0, 1) : ℝ × (Fin d → ℝ) × ℝ)

-- A neuron with zero outer weight has Barron norm `0`.
example (d : ℕ) (b : Fin d → ℝ) (c : ℝ) :
    barronNorm (reluNeuron ((0, b, c) : ℝ × (Fin d → ℝ) × ℝ)) = 0 := by
  simpa using barronNorm_neuron_le ((0, b, c) : ℝ × (Fin d → ℝ) × ℝ)

end CSLibExt.MachineLearning.NeuralNetworks
