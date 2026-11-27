/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.Sampling.GibbsZeroTemperature
import Mathlib.Tactic.FinCases

namespace Cslib.MachineLearning.Sampling.SimulatedAnnealing

open Filter Topology
open scoped ENNReal

private def tiedEnergy : Fin 3 → ℝ := ![0, 0, 1]

private theorem globalMinSet_tiedEnergy : globalMinSet tiedEnergy = {0, 1} := by
  ext x
  fin_cases x <;> norm_num [globalMinSet, tiedEnergy, Fin.forall_fin_succ]

-- In the tied case both minimizers receive half, and the remaining state receives zero.
example : Tendsto (fun T => gibbs tiedEnergy T 0) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  simpa [globalMinSet_tiedEnergy, one_div] using tendsto_gibbs_apply tiedEnergy 0

example : Tendsto (fun T => gibbs tiedEnergy T 1) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  simpa [globalMinSet_tiedEnergy, one_div] using tendsto_gibbs_apply tiedEnergy 1

example : Tendsto (fun T => gibbs tiedEnergy T 2) (𝓝[>] 0) (𝓝 0) := by
  simpa [globalMinSet_tiedEnergy] using tendsto_gibbs_apply tiedEnergy 2

-- With constant energy, every state is a minimizer.
example (x : Fin 4) :
    Tendsto (fun T => gibbs (fun _ : Fin 4 => 7) T x) (𝓝[>] 0) (𝓝 (1 / 4)) := by
  have h : globalMinSet (fun _ : Fin 4 => (7 : ℝ)) = Set.univ := by
    ext y
    simp [globalMinSet]
  simpa [h, one_div] using tendsto_gibbs_apply (fun _ : Fin 4 => (7 : ℝ)) x

end Cslib.MachineLearning.Sampling.SimulatedAnnealing
