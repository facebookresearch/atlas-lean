/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.EXP3

@[expose] public section

/-- Equal weights on two arms normalize to probabilities summing to 1. -/
example : ∑ i : Fin 2, (1 : ℝ) / (∑ j : Fin 2, (1 : ℝ)) = 1 :=
  exp3_probs_sum (fun _ => 1) (by norm_num)

end
