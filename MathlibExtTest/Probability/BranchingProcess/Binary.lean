/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.Binary

/-!
# Binary offspring instance tests

Extinction values at `p = 0, 1/2, 2/3, 1`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.GaltonWatson

open MathlibExt.Probability.GaltonWatson

theorem extinctionProb_binaryOffspring_p_zero :
    extinctionProb (binaryOffspring 0) = 1 := by
  exact extinctionProb_binaryOffspring_of_le (p := (0 : ℝ)) le_rfl zero_le_one
    (by norm_num)

theorem law_binaryOffspring_zero_one_real_zero :
    (law (binaryOffspring 0) 1).real {0} = 1 := by
  rw [law_binaryOffspring_real_zero (p := (0 : ℝ)) le_rfl zero_le_one 1,
    Function.iterate_one,
    pgf_binaryOffspring (p := (0 : ℝ)) le_rfl zero_le_one]
  norm_num

theorem extinctionProb_binaryOffspring_p_half :
    extinctionProb (binaryOffspring (1 / 2)) = 1 := by
  exact extinctionProb_binaryOffspring_of_le (p := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)

theorem extinctionProb_binaryOffspring_p_two_thirds :
    extinctionProb (binaryOffspring (2 / 3)) = 1 / 2 := by
  have h := extinctionProb_binaryOffspring_of_gt (p := (2 / 3 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  rw [h]
  norm_num

theorem extinctionProb_binaryOffspring_p_one :
    extinctionProb (binaryOffspring 1) = 0 := by
  have h := extinctionProb_binaryOffspring_of_gt (p := (1 : ℝ)) zero_le_one le_rfl
    (by norm_num)
  rw [h]
  norm_num

end MathlibExtTest.Probability.GaltonWatson
