/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.FactorDegreesOfFreedom
import Mathlib.Tactic.NormNum

open Matrix
open MathlibExt.Probability.Statistics.Measurement

namespace MathlibExtTest.Probability.Statistics.Measurement.FactorDegreesOfFreedom

-- The explicit loading matrices give the same cross-block and within-block entries.
example :
    let A : Matrix (Fin 5) (Fin 2) ℝ := !![1, 0; 1, 0; 1, 0; 0, 1; 0, 1]
    let B : Matrix (Fin 5) (Fin 2) ℝ := !![1, 0; 1, 0; 1, 0; 0, 2; 0, 1 / 2]
    let CA := factorModelCov A 1 (Matrix.diagonal ![1, 1, 1, 4, 1])
    let CB := factorModelCov B 1 (Matrix.diagonal ![1, 1, 1, 1, 7 / 4])
    CA 2 3 = 0 ∧ CB 3 4 = 1 ∧ CB 4 4 = 2 := by
  intro A B CA CB
  have h := positive_dof_factor_model_not_identified
  have hA := congrArg (fun C : Matrix (Fin 5) (Fin 5) ℝ => C 2 3) h.2.2.2.2.1
  have hB := congrArg (fun C : Matrix (Fin 5) (Fin 5) ℝ => (C 3 4, C 4 4)) h.2.2.2.2.2.1
  have ha : (Matrix.of fun (i : Fin 5) (j : Fin 2) =>
      if j = (if i.val < 3 then 0 else 1) then (![1, 1, 1, 1, 1] : Fin 5 → ℝ) i else 0) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A]
  have hb : (Matrix.of fun (i : Fin 5) (j : Fin 2) =>
      if j = (if i.val < 3 then 0 else 1) then (![1, 1, 1, 2, 1 / 2] : Fin 5 → ℝ) i else 0) = B := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [B]
  dsimp only at hA hB
  rw [ha] at hA
  rw [hb] at hB
  exact ⟨hA, congrArg Prod.fst hB, congrArg Prod.snd hB⟩

end MathlibExtTest.Probability.Statistics.Measurement.FactorDegreesOfFreedom
