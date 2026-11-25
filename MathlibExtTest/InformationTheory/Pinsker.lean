/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.InformationTheory.Pinsker

open MathlibExt.InformationTheory.Pinsker

-- Pinsker's inequality with a zero entry: `p = (1, 0)`, `q = (1/2, 1/2)` gives
-- `(1/2 + 1/2)² = 1 ≤ 2 log 2`.
example : (∑ a : Fin 2, |(![1, 0] : Fin 2 → ℝ) a - (![1 / 2, 1 / 2] : Fin 2 → ℝ) a|) ^ 2 ≤
    2 * ∑ a : Fin 2, (![1, 0] : Fin 2 → ℝ) a *
      Real.log ((![1, 0] : Fin 2 → ℝ) a / (![1 / 2, 1 / 2] : Fin 2 → ℝ) a) :=
  csiszar_kullback_pinsker_of_nonneg _ _ (fun a => by fin_cases a <;> simp)
    (fun a => by fin_cases a <;> norm_num) (by simp [Fin.sum_univ_two])
    (by simp [Fin.sum_univ_two]; norm_num)
