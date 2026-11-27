/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.SampleCompression
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! # Regressions for bounded-loss sample compression -/

open MeasureTheory Set

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- Keeping index zero twice leaves three validation examples, not two.
example : compressionValidationRisk (fun (_ : Unit) (z : ℝ) => z)
    (fun _ : Fin 2 => (0 : Fin 4)) ![1, 0, 1 / 4, 1 / 2] () = 1 / 4 := by
  let I : Fin 2 → Fin 4 := fun _ => 0
  let S : Fin 4 → ℝ := ![1, 0, 1 / 4, 1 / 2]
  let p : Fin 4 → Prop := fun i => i ∉ Finset.univ.image I
  have hcard : Fintype.card {i // p i} = 3 := by decide
  change (∑ i : {i // p i}, S i) / (Fintype.card {i // p i} : ℝ) = 1 / 4
  rw [hcard, ← Finset.sum_subtype (Finset.univ.filter p) (fun i => by simp) S,
    Finset.sum_filter, Fin.sum_univ_four]
  norm_num [p, I, S]

private noncomputable def loss (h z : Bool) : ℝ := if h = z then 0 else 1

-- The reconstruction really reads the kept sample. Here the zero-validation bound is
-- strictly below the trivial bound of one, so the linear term gives a non-vacuous guarantee.
example : ∃ G : Set (Fin 128 → Bool), MeasurableSet G ∧
    1 / 2 ≤ (Measure.pi fun _ : Fin 128 => Measure.dirac false).real G ∧
    ∀ S ∈ G, ∀ I : Fin 1 → Fin 128,
      compressionValidationRisk loss I S (S (I 0)) = 0 →
        risk loss (Measure.dirac false) (S (I 0)) ≤ 1 / 2 := by
  have hloss (h z : Bool) : loss h z ∈ Icc (0 : ℝ) 1 := by
    by_cases he : h = z <;> simp [loss, he]
  obtain ⟨G, hG, hprob, hbound⟩ := sampleCompression_generalization (Measure.dirac false)
    (m := 128) (k := 1) (by decide) (by decide) loss (Measurable.of_discrete) hloss
    (fun a => a 0) (measurable_pi_apply 0) (δ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨G, hG, by linarith only [hprob], ?_⟩
  intro S hS I hzero
  refine ((hbound S hS I).2 hzero).trans ?_
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : ((128 : ℕ) : ℝ) / (1 / 2) = (2 : ℝ) ^ (8 : ℕ) := by norm_num
  rw [he, Real.log_pow]
  norm_num only [Nat.cast_one, Nat.cast_ofNat, one_mul]
  linarith only [hlog]

end CSLibExt.MachineLearning.GeneralizationBounds
