/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.WaldSecondEquation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace MathlibExtTest.Probability.WaldSecondEquation

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ} {f : Filtration ℕ m} {T : Ω → ℕ}

/-- Wald's second equation restates with the exact public signature. -/
example (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hadapt : ∀ k, @Measurable Ω ℝ (f (k + 1)) inferInstance (X k))
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), X i ω) ^ 2 ∂μ =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) :=
  wald_second_equation hX_iid hX_int hmean hX_sq_int hT hXf hadapt hT_int

/-- Zero summands, constant stopping time: with `X n ≡ 0` and `T ≡ N`,
Wald's second equation says `E[(∑_{i < N} 0)²] = 0`. The filtration is the
constant `⊥` filtration, so the independence hypothesis is `Indep _ ⊥ μ` and
the stopping time is a constant stopping time. -/
example (N : ℕ) :
    ∫ _ω : Ω, (∑ _i ∈ Finset.range N, (0 : ℝ)) ^ 2 ∂μ = 0 := by
  have h := wald_second_equation (μ := μ) (X := fun _ _ => (0 : ℝ))
    (ℱ := Filtration.const ℕ (⊥ : MeasurableSpace Ω) bot_le) (T := fun _ => N)
    (fun _ _ => IdentDistrib.refl aemeasurable_const) (integrable_const (0 : ℝ))
    (by simp) (by simp)
    (isStoppingTime_const _ _)
    (fun _ => indep_bot_right _)
    (fun _ => measurable_const)
    (integrable_const _)
  rw [h]; simp

/-- Zero summands: Wald's second equation gives `E[S_T²] = 0` for any stopping
time with `E[T] < ∞`. -/
example (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (fun _ : Ω => (0 : ℝ)) inferInstance)
      (f k) μ)
    (hadapt : ∀ k, @Measurable Ω ℝ (f (k + 1)) inferInstance (fun _ : Ω => (0 : ℝ)))
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ _i ∈ Finset.range (T ω), (0 : ℝ)) ^ 2 ∂μ = 0 := by
  have h := wald_second_equation (μ := μ) (X := fun _ _ => (0 : ℝ))
    (fun _ _ => IdentDistrib.refl aemeasurable_const) (integrable_const (0 : ℝ))
    (by simp) (by simp)
    hT hXf hadapt hT_int
  rw [h]; simp

-- `#print axioms` for the public theorem: only the standard triple.
#print axioms MeasureTheory.wald_second_equation

end MathlibExtTest.Probability.WaldSecondEquation
