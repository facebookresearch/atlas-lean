/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic

open MetaMathlibExt

-- At the Farey fraction 2/3 the Markov triple for k = 1 is (13, 217, 3).
example : (fareyTree [false, true]).2.1 = (2, 3) ∧
    genMarkovTree 1 [false, true] = (13, 217, 3) := by decide

example : IsGenMarkovCharNumber 13 217 3 67 := by
  unfold IsGenMarkovCharNumber
  decide

example (u : ℕ) (hu : IsGenMarkovCharNumber 13 217 3 u) : (217 : ℤ) ∣ 13 * u - 3 :=
  genMarkovCharNumber_dvd_sub 1 [false, true] (by decide) (by decide) u hu

-- At the Farey fraction 1/2 with k = 0, the characteristic number 2 gives 2² + 1 = 5.
example : 5 ∣ (2 : ℕ) ^ 2 + 0 * 2 + 1 :=
  genMarkovCharNumber_sq_add 0 [false] (by decide) (by decide) 2 isGenMarkovCharNumber_one_five_two

-- Across 1/1 the reflected triple admits a characteristic number with only the opposite sign.
example : genMarkovTree 1 [true, false] = (3, 217, 13) ∧
    IsGenMarkovCharNumber 3 217 13 68 ∧ ¬ (217 : ℤ) ∣ 3 * 68 - 13 := by
  unfold IsGenMarkovCharNumber
  decide
