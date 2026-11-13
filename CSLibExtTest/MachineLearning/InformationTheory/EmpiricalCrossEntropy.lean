/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.InformationTheory.EmpiricalCrossEntropy

/-!
# Tests for the empirical cross-entropy of a fixed model

Two-token vocabulary (`Bool`) with sample `[false, false, true]`: a model giving
`true` probability `0` has infinite empirical cross-entropy on both sides (the
cross-entropy and the average surprisal are both `∞`), while a fully supported
model is finite and satisfies entropy plus divergence.
-/

@[expose] public section

open Real InformationTheory Cslib.MachineLearning.InformationTheory
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.InformationTheory.EmpiricalCrossEntropy

/-- The two-token sample `[false, false, true]` indexed by `Fin 3`. -/
noncomputable def tokSample : Fin 3 → Bool := fun n => decide (n.val = 2)

/-- The sample is nonempty. -/
theorem tokSample_ne : 3 ≠ 0 := by decide

/-- A model that always predicts `false` rules out the sampled `true`. -/
theorem two_token_zero_model_top :
    crossEntropy (empiricalPMF tokSample tokSample_ne) (PMF.pure false) = ∞ := by
  rw [empiricalCrossEntropy_eq_top_iff]
  refine ⟨2, ?_⟩
  have hs : tokSample 2 = true := by simp [tokSample]
  rw [hs]
  simp

/-- The average surprisal is also infinite when the model rules out a sample. -/
theorem two_token_zero_model_avg_top :
    (∑ n, surprisal ((PMF.pure false) (tokSample n))) / ((3 : ℕ) : ℝ≥0∞) = ∞ := by
  have h := empiricalCrossEntropy_eq_avg_surprisal tokSample tokSample_ne
    (PMF.pure false)
  rw [two_token_zero_model_top] at h
  exact h.symm

/-- A model that always predicts a fair coin. -/
noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ => ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj,
      add_halves])

/-- The fully supported model has finite empirical cross-entropy. -/
theorem two_token_supported_ne_top :
    crossEntropy (empiricalPMF tokSample tokSample_ne) fair ≠ ∞ := by
  intro h
  rw [empiricalCrossEntropy_eq_top_iff] at h
  obtain ⟨n, hn⟩ := h
  exact (by simp [fair] : fair (tokSample n) ≠ 0) hn

/-- On the fully supported model, cross-entropy is entropy plus divergence. -/
theorem two_token_supported_decomp :
    crossEntropy (empiricalPMF tokSample tokSample_ne) fair =
      ENNReal.ofReal (shannonEntropy (empiricalPMF tokSample tokSample_ne)) +
        klDiv (empiricalPMF tokSample tokSample_ne).toMeasure fair.toMeasure /
          ENNReal.ofReal (Real.log 2) :=
  empiricalCrossEntropy_eq_shannonEntropy_add_klDiv _ _ _

/-- On the fully supported model, the average surprisal is the cross-entropy. -/
theorem two_token_supported_avg :
    (∑ n, surprisal (fair (tokSample n))) / ((3 : ℕ) : ℝ≥0∞) =
      crossEntropy (empiricalPMF tokSample tokSample_ne) fair :=
  (empiricalCrossEntropy_eq_avg_surprisal tokSample tokSample_ne _).symm

end CSLibExtTest.MachineLearning.InformationTheory.EmpiricalCrossEntropy
