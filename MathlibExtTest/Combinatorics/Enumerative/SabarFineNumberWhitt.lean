/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SabarFineNumberWhitt

/-! # The first two cases of Sabar's Fine number identity -/

open MetaMathlibExt

-- At the lower endpoint the negative correction cancels Whitt's value.
example : whittGeneralizedCatalan 2 2 = 3 := by
  rw [eq_sub_of_add_eq (two_pow_mul_fineNumber_eq_whittGeneralizedCatalan 1 (by decide)).symm]
  decide +kernel

-- At the next index the positive correction adds to Whitt's value.
example : whittGeneralizedCatalan 2 3 = 13 := by
  rw [eq_sub_of_add_eq (two_pow_mul_fineNumber_eq_whittGeneralizedCatalan 2 (by decide)).symm]
  decide +kernel
