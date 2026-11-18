/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.SpectralGap

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Tests for the spectral gap and log-Sobolev constant in Dirichlet-form terms

`K₂` is the two-state chain moving to a uniform state, `π` is uniform, and `P₂ = (I + K₂)/2` is
its lazy version (stay with probability `3/4`). For every `f`, `E_{K₂}(f, f) = Var_π(f)` and
`E_{P₂}(f, f) = ½ Var_π(f)`, so the spectral gaps are `1` and `1/2`. Feeding `γ = 1/2` into
`isMixedAt_of_le_spectralGap` shows that `P₂` is `1/4`-mixed at time `2`; this exercises every
hypothesis of the bridge to Sinclair's mixing bound together. On a one-point space the gap is
`0` by the `sInf ∅ = 0` convention.
-/

set_option autoImplicit false

open Matrix ProbabilityTheory
open MathlibExt.Probability.DirichletForm MathlibExt.Probability.MarkovMixing

namespace MathlibExtTest.Probability.DirichletForm.SpectralGap

/-- Move to a uniformly random state. -/
noncomputable def K₂ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 / 2

/-- The uniform distribution on two states. -/
noncomputable def π₂ : Fin 2 → ℝ := fun _ => 1 / 2

theorem form_K₂ (f : Fin 2 → ℝ) : form π₂ (K₂ - 1) f f = weightedVariance π₂ f := by
  rw [form_sub_one π₂ (fun x => by simp [K₂])]
  simp [weightedVariance, π₂, K₂, Fin.sum_univ_two]
  ring

theorem lazy_eq : (1 / 2 : ℝ) • (1 + K₂) = Matrix.of fun i j => if i = j then 3 / 4 else 1 / 4 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K₂] <;> norm_num

theorem form_lazy (f : Fin 2 → ℝ) :
    form π₂ ((1 / 2 : ℝ) • (1 + K₂) - 1) f f = 1 / 2 * weightedVariance π₂ f := by
  rw [lazy_eq, form_sub_one π₂ (fun x => by fin_cases x <;> simp [Fin.sum_univ_two] <;> norm_num)]
  simp [weightedVariance, π₂, Fin.sum_univ_two]
  ring

theorem weightedVariance_ne_zero : weightedVariance π₂ ![1, 0] ≠ 0 := by
  simp [weightedVariance, π₂, Fin.sum_univ_two]

theorem spectralGap_K₂ : spectralGap π₂ K₂ = 1 := by
  have : (fun f => form π₂ (K₂ - 1) f f / weightedVariance π₂ f) ''
      {f | weightedVariance π₂ f ≠ 0} = {1} := by
    ext c
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, hf, rfl⟩; rw [form_K₂, div_self hf]
    · rintro rfl
      exact ⟨_, weightedVariance_ne_zero, by rw [form_K₂, div_self weightedVariance_ne_zero]⟩
  rw [spectralGap, this, csInf_singleton]

theorem spectralGap_lazy : spectralGap π₂ ((1 / 2 : ℝ) • (1 + K₂)) = 1 / 2 := by
  have : (fun f => form π₂ ((1 / 2 : ℝ) • (1 + K₂) - 1) f f / weightedVariance π₂ f) ''
      {f | weightedVariance π₂ f ≠ 0} = {1 / 2} := by
    ext c
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, hf, rfl⟩; rw [form_lazy]; field_simp
    · rintro rfl
      exact ⟨_, weightedVariance_ne_zero, by rw [form_lazy]; field_simp [weightedVariance_ne_zero]⟩
  rw [spectralGap, this, csInf_singleton]

/-- Mixing of the lazy chain at time `2` from its spectral gap `1/2`. -/
example : IsMixedAt ((1 / 2 : ℝ) • (1 + K₂)) π₂ 2 := by
  refine isMixedAt_of_le_spectralGap (fun _ => by norm_num [π₂]) (by simp [π₂])
    ?_ (fun i j => by simp [K₂, π₂]) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    spectralGap_lazy.ge (fun x => by norm_num [π₂])
  rw [mem_rowStochastic_iff_sum]
  exact ⟨fun i j => by simp [K₂], fun i => by simp [K₂]⟩

/-- The log-Sobolev inequality holds with the log-Sobolev constant. -/
example (f : Fin 2 → ℝ) :
    logSobolevConstant π₂ K₂ * entropyFunctional π₂ f ≤ form π₂ (K₂ - 1) f f :=
  logSobolevConstant_mul_entropyFunctional_le (fun _ => by norm_num [π₂]) (by simp [π₂])
    (fun _ _ => by simp [K₂]) (fun x => by simp [K₂]) f

/-- On a one-point space every function has zero variance and the gap is `0`. -/
example (P : Matrix Unit Unit ℝ) : spectralGap (fun _ => 1) P = 0 := by
  have : {f : Unit → ℝ | weightedVariance (fun _ => 1) f ≠ 0} = ∅ := by
    ext f; simp [weightedVariance]
  rw [spectralGap, this, Set.image_empty, Real.sInf_empty]

end MathlibExtTest.Probability.DirichletForm.SpectralGap
