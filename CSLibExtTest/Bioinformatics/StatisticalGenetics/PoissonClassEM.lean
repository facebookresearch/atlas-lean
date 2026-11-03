/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.StatisticalGenetics.PoissonClassEM

@[expose] public section

open Cslib.Bioinformatics.StatisticalGenetics.PoissonClassEM
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization

namespace CSLibExtTest.Bioinformatics.StatisticalGenetics.PoissonClassEM

/-- Illustrative class rates `1` and `1/10` (tolerant and depleted). -/
noncomputable def rate : Fin 2 → ℝ := ![1, 1 / 10]

theorem rate_pos : ∀ c, 0 < rate c := by
  intro c; fin_cases c <;> norm_num [rate]

/-- Non-vacuity: equal weights are admissible. -/
noncomputable def half : PosWeights (Fin 2) :=
  ⟨fun _ => 1 / 2, fun _ => by norm_num, by norm_num⟩

/-- Three genes: one with no LoF variants of `E = 10`, two near expectation. -/
noncomputable def genes : Fin 3 → GeneData :=
  ![⟨0, 10, by norm_num⟩, ⟨9, 10, by norm_num⟩, ⟨4, 5, by norm_num⟩]

/-- The EM step returns weights summing to one. -/
example : ∑ c, (emStep rate_pos genes (by norm_num) half).1 c = 1 :=
  (emStep rate_pos genes (by norm_num) half).2.2

/-- One EM step does not decrease the log-likelihood. -/
example : logLik (joint rate) genes half ≤
    logLik (joint rate) genes (emStep rate_pos genes (by norm_num) half) :=
  logLik_le_logLik_emStep rate_pos genes (by norm_num) half

/-- Along the iterates the log-likelihood is monotone. -/
example : logLik (joint rate) genes half ≤
    logLik (joint rate) genes ((emStep rate_pos genes (by norm_num))^[5] half) := by
  have h := logLik_iterate_emStep_monotone rate_pos genes (by norm_num) half (Nat.zero_le 5)
  simpa only [Function.iterate_zero, id] using h

end CSLibExtTest.Bioinformatics.StatisticalGenetics.PoissonClassEM
