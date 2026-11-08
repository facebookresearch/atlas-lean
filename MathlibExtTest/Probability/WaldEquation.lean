/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.WaldEquation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace MathlibExtTest.Probability.WaldEquation

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ} {f : Filtration ℕ m} {T : Ω → ℕ}

/-- Wald's equation restates with the exact public signature. -/
example (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), X i ω) ∂μ =
      (∫ ω, X 0 ω ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) :=
  wald_equation hX_iid hX_int hT hXf hT_int

/-- Constant summands, constant stopping time: with `X n ≡ c` and `T ≡ N`,
Wald's equation says `N * c = c * N`. The filtration is the constant `⊥`
filtration, so the independence hypothesis is `Indep _ ⊥ μ` and the stopping
time is a constant stopping time. -/
example (c : ℝ) (N : ℕ) :
    ∫ _ω : Ω, (∑ _i ∈ Finset.range N, c) ∂μ =
      (∫ _ω : Ω, c ∂μ) * (∫ _ω : Ω, (N : ℝ) ∂μ) := by
  have h := wald_equation (μ := μ) (X := fun _ _ => c)
    (f := Filtration.const ℕ (⊥ : MeasurableSpace Ω) bot_le) (T := fun _ => N)
    (fun _ _ => IdentDistrib.refl aemeasurable_const) (integrable_const c)
    (isStoppingTime_const _ _)
    (fun _ => indep_bot_right _)
    (integrable_const _)
  simpa using h

/-- Zero summands: Wald's equation gives `E[S_T] = 0` for any stopping time
with `E[T] < ∞`. -/
example (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (fun _ : Ω => (0 : ℝ)) inferInstance)
      (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ _i ∈ Finset.range (T ω), (0 : ℝ)) ∂μ = 0 := by
  have h := wald_equation (μ := μ) (X := fun _ _ => 0)
    (fun _ _ => IdentDistrib.refl aemeasurable_const) (integrable_const (0 : ℝ))
    hT hXf hT_int
  rw [h]; simp

-- `#print axioms` for the public theorem: only the standard triple.
#print axioms MeasureTheory.wald_equation

end MathlibExtTest.Probability.WaldEquation
