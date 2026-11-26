/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.KFullParity

open Filter Topology

-- For squarefull numbers, the limiting ratio simplifies to 2 - √2.
example :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull 2 n ∧ Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull 2 n ∧ Even n}.ncard)
      atTop (𝓝 (2 - Real.sqrt 2)) := by
  rw [Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = 1 - 1 / (2 : ℝ) by norm_num]
  exact MetaMathlibExt.tendsto_card_odd_kFull_div_card_even_kFull (hk := le_rfl)
