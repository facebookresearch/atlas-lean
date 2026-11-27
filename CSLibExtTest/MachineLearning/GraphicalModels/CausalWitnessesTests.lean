/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalWitnesses
import Mathlib.Tactic.NormNum

/-!
# Tests for causal witnesses

Concrete checks for the equal-joint witness and the kidney-stone reversal.
-/

@[expose] public section

namespace Cslib.MachineLearning.CausalWitnessesTests

open Cslib.MachineLearning.GraphicalModels
open Cslib.MachineLearning.GraphicalModels.CausalWitnesses

theorem copyChain_all_true :
    copyChainNet.joint ![true, true, true] = 1 / 2 := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  simp [copyChainNet, InterveningVsConditioning.coin_true]

theorem kidney_aggregate_reversal_check :
    (273 : ℝ) / 350 < 289 / 350 ∧ (13 : ℝ) / 15 < 27 / 29 ∧
      (11 : ℝ) / 16 < 192 / 263 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

end Cslib.MachineLearning.CausalWitnessesTests
