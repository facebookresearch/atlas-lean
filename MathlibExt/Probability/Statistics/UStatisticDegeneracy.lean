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

-- Copied verbatim from `MathlibExt/Probability/Statistics/UStatistic.lean`
-- (private helpers, not importable): the worker proof of
-- `memLp_hoeffdingProj_one` below references them by these exact qualified
-- names. Kept private and unmodified.
namespace ProbabilityTheory

private theorem memLp_integral_right {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : A × B → ℝ}
    (hH : MemLp H 2 (μ.prod ν)) :
    MemLp (fun y => ∫ z, H (y, z) ∂ν) 2 μ := by
  have hP := hH.aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hP).mpr
  have hHi := hH.integrable (by norm_num)
  have hHs := hH.integrable_sq
  have hsec : ∀ᵐ y ∂μ, MemLp (fun z => H (y, z)) 2 ν := by
    filter_upwards [hHi.prod_right_ae, hHs.prod_right_ae] with y hy hys
    exact (memLp_two_iff_integrable_sq hy.aestronglyMeasurable).mpr hys
  refine hHs.integral_prod_left.mono' (hP.pow 2) ?_
  filter_upwards [hsec] with y hy
  have hb := variance_nonneg (fun z => H (y, z)) ν
  rw [variance_eq_sub hy] at hb
  dsimp only [Pi.pow_apply] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith

private theorem measurePreserving_prefix_join {α : Type*} [MeasurableSpace α]
    {m c : ℕ} (hc : c ≤ m) (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving
      (fun p : (Fin c → α) × (Fin (m - c) → α) =>
        fun j : Fin m => if hj : (j : ℕ) < c then p.1 ⟨j, hj⟩
          else p.2 ⟨j - c, by have := j.isLt; omega⟩)
      ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ))
      (Measure.pi fun _ => μ) := by
  let e : Fin c ⊕ Fin (m - c) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hc))
  have hp := (measurePreserving_piCongrLeft (fun _ : Fin m => μ) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin c ⊕ Fin (m - c) => μ))
  convert hp using 1
  funext p j
  obtain ⟨i, rfl⟩ := e.surjective j
  cases i with
  | inl i =>
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    simp [e, Equiv.trans_apply, finSumFinEquiv, i.isLt]
    rfl
  | inr i =>
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    simp [e, Equiv.trans_apply, finSumFinEquiv, Nat.not_lt.mpr (Nat.le_add_right c i)]
    rfl

end ProbabilityTheory

/-- The first Hoeffding projection of a square-integrable kernel is square-integrable. -/
theorem memLp_hoeffdingProj_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    {h : (Fin m → α) → ℝ} (hh : MemLp h 2 (Measure.pi fun _ => μ)) :
    MemLp (hoeffdingProj μ h 1) 2 (Measure.pi fun _ : Fin 1 => μ) := by
  let H : (Fin 1 → α) × (Fin (m - 1) → α) → ℝ := fun p =>
    h (fun j => if hj : (j : ℕ) < 1 then p.1 ⟨j, hj⟩
      else p.2 ⟨j - 1, by have := j.isLt; omega⟩)
  have hH : MemLp H 2 ((Measure.pi fun _ => μ).prod (Measure.pi fun _ => μ)) :=
    hh.comp_measurePreserving (ProbabilityTheory.measurePreserving_prefix_join hm μ)
  have hproj : hoeffdingProj μ h 1
      = fun y => ∫ z, H (y, z) ∂(Measure.pi fun _ => μ) := by
    funext y
    simp [hoeffdingProj, H]
  rw [hproj]
  exact ProbabilityTheory.memLp_integral_right _ _ hH

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
variance asymptotics in the copied closure above. -/
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
