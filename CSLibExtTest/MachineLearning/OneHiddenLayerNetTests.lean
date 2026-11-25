/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
import CSLibExt.MachineLearning.OneHiddenLayerNet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
namespace CSLibExtTest.MachineLearning.OneHiddenLayerNet
open Cslib.MachineLearning.OneHiddenLayerNet
theorem relu_universal_approximation_closedBall :
    ∃ (m : ℕ) (W : Fin m → EuclideanSpace ℝ (Fin 1)) (b c : Fin m → ℝ),
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
        |‖x‖ ^ 2 - (oneHiddenLayerNet 1 m (fun x => max x 0) W b c).forward 2 x 0| <
          1 / 10 := by
  exact universal_approximation_net (ProperSpace.isCompact_closedBall _ _)
    continuous_relu relu_not_polynomial
    (continuous_id.norm.pow 2).continuousOn (by norm_num)
theorem forward_relu_two_hidden :
    (oneHiddenLayerNet 1 2 (fun x => max x 0) (fun _ => EuclideanSpace.single 0 1)
      ![0, -1] ![1, -2]).forward 2 (EuclideanSpace.single 0 3) 0 = -1 := by
  rw [forward_oneHiddenLayerNet, Fin.sum_univ_two]
  simp [EuclideanSpace.single, EuclideanSpace.inner_single_left]; norm_num
theorem forward_stable_three (n m : ℕ) (σ : ℝ → ℝ)
    (W : Fin m → EuclideanSpace ℝ (Fin n)) (b c : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (oneHiddenLayerNet n m σ W b c).forward 3 x 0 =
      (oneHiddenLayerNet n m σ W b c).forward 2 x 0 := by
  rfl
#print axioms forward_oneHiddenLayerNet
#print axioms universal_approximation_net
#print axioms relu_not_polynomial
end CSLibExtTest.MachineLearning.OneHiddenLayerNet
