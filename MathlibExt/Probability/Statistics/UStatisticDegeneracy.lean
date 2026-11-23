/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.UStatistic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- `ζ₁ = 0` iff the first Hoeffding projection is a.s. constant. -/
theorem zeta1_eq_zero_iff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] = 0 ↔
      ∀ᵐ y ∂(Measure.pi fun _ : Fin 1 => μ), hoeffdingProj μ h 1 y
        = ∫ z, hoeffdingProj μ h 1 z ∂(Measure.pi fun _ : Fin 1 => μ) := by
  have _hsymm' := hsymm
  have hX : MemLp (hoeffdingProj μ h 1) 2 (Measure.pi fun _ : Fin 1 => μ) :=
    memLp_hoeffdingProj_one μ hm hh
  constructor
  · intro hz
    exact ae_eq_integral_of_variance_eq_zero hX hz
  · intro hae
    have hae' : hoeffdingProj μ h 1 =ᵐ[Measure.pi fun _ : Fin 1 => μ]
        fun _ => ∫ z, hoeffdingProj μ h 1 z ∂(Measure.pi fun _ : Fin 1 => μ) := hae
    rw [variance_congr hae', variance_eq_integral aemeasurable_const]
    simp

/-- Degenerate kernels have `n Var(U_n) → 0`, derived in-proof from the
imported variance asymptotics. -/
theorem variance_degenerate_rate {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    {h : (Fin m → α) → ℝ} (hsymm : ∀ (σ : Equiv.Perm (Fin m)) y, h (y ∘ σ) = h y)
    (hh : MemLp h 2 (Measure.pi fun _ => μ))
    (hz : Var[hoeffdingProj μ h 1; Measure.pi fun _ : Fin 1 => μ] = 0) :
    Tendsto (fun n : ℕ => (n : ℝ)
      * Var[uStatistic h; Measure.pi fun _ : Fin n => μ]) atTop (𝓝 0) := by
  have _hm' := hm
  have hlim := tendsto_mul_variance_uStatistic μ hsymm hh
  rw [hz, mul_zero] at hlim
  exact hlim

end ProbabilityTheory
