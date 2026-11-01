/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Regulatory.ChromHMM
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-!
# ChromHMM tests

Two chromatin states and one mark: a valid parameter (uniform initial and transition
distributions, mark probabilities `1/4` and `3/4`; the non-vacuity witness of `Params.Valid`) and
rich data (one sequence of two bins, mark present then absent; the witness of `Rich`). On them the
ChromHMM step does not decrease the likelihood. A product of two Bernoulli distributions sums to
one; `bernPMF` at a vector is the product of the per-mark probabilities; the factored update of
the weights `(c(false), c(true)) = (1, 3)` is `3/4`.
-/

namespace Cslib.Bioinformatics.Regulatory.ChromHMM

open Cslib.MachineLearning.LatentVariable.BernoulliMixture (bernPMF)
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization (logLik)

/-- A two-state, one-mark ChromHMM parameter. -/
noncomputable def θ₀ : Params Bool 1 where
  init _ := 1 / 2
  trans _ _ := 1 / 2
  prob s _ := if s then 3 / 4 else 1 / 4

theorem θ₀_valid : θ₀.Valid where
  init_pos _ := by norm_num [θ₀]
  init_sum := by norm_num [θ₀]
  trans_pos _ _ := by norm_num [θ₀]
  trans_sum _ := by norm_num [θ₀]
  prob_pos s _ := by cases s <;> norm_num [θ₀]
  prob_lt_one s _ := by cases s <;> norm_num [θ₀]

/-- One sequence: the mark is present in bin `0` and absent afterwards. -/
def xs₀ : Fin 1 → ℕ → Fin 1 → Bool := fun _ t _ => t == 0

theorem xs₀_rich : Rich 1 xs₀ where
  pos := by norm_num
  len := by norm_num
  marks j b := by
    cases b
    · exact ⟨0, 1, by simp [xs₀]⟩
    · exact ⟨0, 0, by simp [xs₀]⟩

example : logLik (joint 1) xs₀ ⟨θ₀, θ₀_valid⟩ ≤
    logLik (joint 1) xs₀ (emStep 1 xs₀ xs₀_rich ⟨θ₀, θ₀_valid⟩) :=
  logLik_le_emStep 1 xs₀ xs₀_rich _

example : bernPMF ![1 / 4, 2 / 3] ![true, false] = 1 / 12 := by
  norm_num [bernPMF, Fin.prod_univ_two]

example : ∑ x, bernPMF ![1 / 4, 2 / 3] x = 1 := sum_bernPMF _

example : factoredUpdate (fun o : Fin 1 → Bool => if o 0 then 3 else 1) 0 = 3 / 4 := by
  have hu : (Finset.univ : Finset (Fin 1 → Bool)) = {fun _ => false, fun _ => true} := by
    decide
  simp only [factoredUpdate, onesCount, zerosCount, hu]
  rw [Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  norm_num

end Cslib.Bioinformatics.Regulatory.ChromHMM
