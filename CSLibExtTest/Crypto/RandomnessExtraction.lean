/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.RandomnessExtraction

/-! # Finite-source entropy and collision tests -/

namespace Cslib.Crypto.RandomnessExtraction.Tests

open Cslib.Security.QuantitativeInformationFlow

-- A fair bit attains the one-bit threshold exactly, not just strictly below it.
example : minEntropy (PMF.uniformFintype Bool) = 1 := by
  rw [minEntropy, vulnerability_uniformFintype, Fintype.card_bool]
  change -Real.logb 2 (1 / 2) = 1
  rw [one_div, Real.logb_inv, neg_neg, Real.logb_self_eq_one (by norm_num)]

-- A concentrated source has a zero-probability outcome; the two draws always agree.
example : collisionProbability (PMF.pure true) = 1 := by
  rw [collisionProbability_eq_sum_sq, Fintype.sum_bool]
  norm_num [PMF.pure_apply]

-- For a biased bit the best guess succeeds with probability 3/4, but a second draw
-- succeeds only (3/4)^2 + (1/4)^2 = 5/8 of the time.
private noncomputable def biasedBit : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (if b then 3 / 4 else 1 / 4)) (by
    rw [Fintype.sum_bool]
    change ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) = 1
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num)

example : collisionProbability biasedBit = 5 / 8 := by
  rw [collisionProbability_eq_sum_sq, Fintype.sum_bool]
  norm_num [biasedBit, PMF.ofFintype_apply, ENNReal.toReal_div]

example : ¬ 1 ≤ minEntropy biasedBit := by
  intro h
  have ht := (le_minEntropy_iff biasedBit 1).mp h true
  norm_num [biasedBit, PMF.ofFintype_apply, ENNReal.toReal_div] at ht

end Cslib.Crypto.RandomnessExtraction.Tests
