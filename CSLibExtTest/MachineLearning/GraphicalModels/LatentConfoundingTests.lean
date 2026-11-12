/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LatentConfounding

/-!
# Tests for non-identifiability under latent confounding

The observed laws of the two witness networks (mass `1/2` on `(true, true)` and
`(false, false)`), their interventional probabilities, and the confounding bias in network `b₂`:
`P(Y = 1 | X = 1) = 1` while `P(Y = 1 | do(X = 1)) = 1/2`.
-/

@[expose] public section

namespace Cslib.MachineLearning.LatentConfoundingTests

open Cslib.MachineLearning.GraphicalModels.LatentConfounding

-- Observed law values for network 1 (`Y = X`).
example : observedLaw b₁ true true = 1 / 2 := by simp [b₁_observedLaw]
example : observedLaw b₁ false false = 1 / 2 := by simp [b₁_observedLaw]
example : observedLaw b₁ true false = 0 := by simp [b₁_observedLaw]
example : observedLaw b₁ false true = 0 := by simp [b₁_observedLaw]

-- Observed law values for network 2 (`Y = U`).
example : observedLaw b₂ true true = 1 / 2 := by simp [b₂_observedLaw]
example : observedLaw b₂ false false = 1 / 2 := by simp [b₂_observedLaw]
example : observedLaw b₂ true false = 0 := by simp [b₂_observedLaw]
example : observedLaw b₂ false true = 0 := by simp [b₂_observedLaw]

-- Interventional probabilities.
example : doProb b₁ true true = 1 := b₁_doProb_tt
example : doProb b₂ true true = 1 / 2 := b₂_doProb_tt
example : doProb b₂ true false = 1 / 2 := b₂_doProb_tf

-- Confounding bias is visible: the observational conditional is `1`,
-- but `doProb b₂ true true = 1 / 2`.
example :
    observedLaw b₂ true true / (observedLaw b₂ true true + observedLaw b₂ true false) = 1 := by
  rw [show observedLaw b₂ true true = (1 / 2 : ℝ) from by simp [b₂_observedLaw],
    show observedLaw b₂ true false = (0 : ℝ) from by simp [b₂_observedLaw]]
  norm_num

end Cslib.MachineLearning.LatentConfoundingTests
