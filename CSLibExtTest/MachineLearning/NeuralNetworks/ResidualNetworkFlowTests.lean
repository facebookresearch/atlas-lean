/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.NeuralNetworks.ResidualNetworkFlow
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace CSLibExt.MachineLearning.NeuralNetworks

-- The hypotheses are satisfiable: the linear block `g(t, z) = -z` (smooth, 1-Lipschitz) gives a
-- flow on `[0, 1]` and a depth-uniform `C / L` bound for the residual networks
-- `Z_{l+1} = (1 - 1/L) Z_l`.
example : ∃ z : ℝ → ℝ, z 0 = 1 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt z (-z t) t) ∧
    ∃ C : ℝ, ∀ L : ℕ, 0 < L → ∀ Z : ℕ → ℝ, Z 0 = 1 →
      (∀ l : ℕ, Z (l + 1) = Z l + (1 / (L : ℝ)) • -Z l) → ‖Z L - z 1‖ ≤ C / L :=
  residualNetwork_flow_error_le (fun _ z => -z) 1 1 contDiff_snd.neg
    (fun _ _ => LipschitzWith.of_dist_le_mul fun a b => by simp [Real.dist_eq])

-- A time-dependent block `g(t, z) = t - z` (a residual network whose bias grows with depth).
example : ∃ z : ℝ → ℝ, z 0 = 0 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt z (t - z t) t) ∧
    ∃ C : ℝ, ∀ L : ℕ, 0 < L → ∀ Z : ℕ → ℝ, Z 0 = 0 →
      (∀ l : ℕ, Z (l + 1) = Z l + (1 / (L : ℝ)) • ((l : ℝ) / L - Z l)) → ‖Z L - z 1‖ ≤ C / L :=
  residualNetwork_flow_error_le (fun t z => t - z) 0 1 (contDiff_fst.sub contDiff_snd)
    (fun t _ => LipschitzWith.of_dist_le_mul fun a b => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show t - a - (t - b) = -(a - b) by ring, abs_neg])

end CSLibExt.MachineLearning.NeuralNetworks
