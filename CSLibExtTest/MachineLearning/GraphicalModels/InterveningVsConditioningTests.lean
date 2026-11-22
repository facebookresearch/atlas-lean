/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.InterveningVsConditioning
public import Mathlib.Tactic.NormNum

/-!
# Tests for intervening versus conditioning

A truncated-factorization value of the confounded network after `do(X = true)`, and the
probability of the conditioning event.
-/

@[expose] public section

namespace Cslib.MachineLearning.InterveningVsConditioningTests

open Cslib.MachineLearning GraphicalModels InterveningVsConditioning Finset

/-- After `do(X = true)`, `P(Z = true, X = true, Y = true) = 1/2 · 9/10 = 9/20`. -/
example : (confoundedNet.intervene 1 true).joint ![true, true, true] = 9 / 20 := by
  rw [BayesNet.joint_intervene, show univ.erase (1 : Fin 3) = {0, 2} by decide,
    prod_pair (by decide)]
  simp [confoundedNet, BayesNet.paVal, coin_true]
  norm_num

/-- The conditioning event has probability `P(X = true) = 1/2`. -/
example : ∑ x with x 1 = true, confoundedNet.joint x = 1 / 2 := sum_joint_x1

end Cslib.MachineLearning.InterveningVsConditioningTests
