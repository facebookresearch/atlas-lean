/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.AMS

import Mathlib.Tactic.NormNum

@[expose] public section

/-- With a single item, every sign gives estimate `1` and the total
matches `2^1` times the squared frequency. -/
example : (∑ s : Fin 1 → Bool, amsEst (fun _ => (1 : ℚ)) s) = 2 := by
  rw [amsEst_sum]
  norm_num

end
