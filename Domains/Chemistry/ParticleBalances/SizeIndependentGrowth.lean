/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Ring

/-!
# Moment equations for size-independent growth

For transport on a half-line, a locally dominated time derivative allows differentiation of the
moment integral. Integration by parts in size yields the boundary flux and the preceding moment.
This is an identity for an ordinary density, not an existence result or a statement about point
masses. The optional linear loss covers the additional term in the model of Rawlings and Ekerdt,
*Chemical Reactor Analysis and Design Fundamentals*, 2nd ed., Example 10.2.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Chemistry.ParticleBalances

private lemma integrableOn_prev_weight {L₀ : ℝ} {f : ℝ → ℝ} {k : ℕ} (hL₀ : 0 ≤ L₀)
    (h₀ : IntegrableOn f (Ioi L₀)) (hk : IntegrableOn (fun x ↦ x ^ k * f x) (Ioi L₀)) :
    IntegrableOn (fun x ↦ x ^ (k - 1) * f x) (Ioi L₀) := by
  refine (h₀.norm.add hk.norm).mono' ?_ ?_
  · exact (continuous_id.pow (k - 1)).aestronglyMeasurable.mul h₀.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  have hx₀ : 0 ≤ x := hL₀.trans (le_of_lt hx)
  have hpow : x ^ (k - 1) ≤ 1 + x ^ k := by
    by_cases hx₁ : 1 ≤ x
    · exact (pow_le_pow_right₀ hx₁ (Nat.sub_le k 1)).trans (le_add_of_nonneg_left zero_le_one)
    · exact (pow_le_one₀ hx₀ (le_of_not_ge hx₁)).trans (le_add_of_nonneg_right (pow_nonneg hx₀ k))
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx₀ _)]
  rw [← one_add_mul]
  exact mul_le_mul_of_nonneg_right hpow (abs_nonneg (f x))

/-- The derivative of the `k`th moment of a real density `n` on `x > L₀` is the sum of the
bulk growth and boundary flux contributions, minus a size-independent linear loss. Here `G`
and `B` are the speed and boundary flux **at time `t`**. `nt` represents the time derivative
locally, and `nx` is the size derivative at `t`. The hypotheses give absolute integrability of
the unweighted and `k`th-power-weighted densities at `t`, local measurability and domination for
time differentiation, and a right boundary trace and vanishing weighted tail for integration by
parts.

Set `loss = 0` for pure transport. For `k = 0` the bulk growth term is zero (natural subtraction
is truncated), and `L₀ ^ 0 = 1` even at `L₀ = 0`. At zero speed the flux identity forces `B = 0`;
no division by `G` is needed. No sign assumption on the density, speed, flux or loss is needed. -/
theorem hasDerivAt_moment_of_sizeIndependentGrowth {L₀ t G B loss : ℝ} {U : Set ℝ}
    {n nt : ℝ → ℝ → ℝ} {nx bound : ℝ → ℝ} (k : ℕ) (hL₀ : 0 ≤ L₀) (hU : U ∈ 𝓝 t)
    (hMass : IntegrableOn (n t) (Ioi L₀))
    (hMoment : IntegrableOn (fun x ↦ x ^ k * n t x) (Ioi L₀))
    (hnMeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (n s) (volume.restrict (Ioi L₀)))
    (hntMeas : AEStronglyMeasurable (nt t) (volume.restrict (Ioi L₀)))
    (ht : ∀ x ∈ Ioi L₀, ∀ s ∈ U, HasDerivAt (n · x) (nt s x) s)
    (hBound : ∀ x ∈ Ioi L₀, ∀ s ∈ U, ‖x ^ k * nt s x‖ ≤ bound x)
    (hBoundInt : IntegrableOn bound (Ioi L₀))
    (hx : ∀ x ∈ Ioi L₀, HasDerivAt (n t) (nx x) x)
    (hTrace : ContinuousWithinAt (n t) (Ioi L₀) L₀)
    (hTail : Tendsto (fun x ↦ x ^ k * n t x) atTop (𝓝 0))
    (hPDE : ∀ x ∈ Ioi L₀, nt t x + G * nx x + loss * n t x = 0)
    (hFlux : G * n t L₀ = B) :
    HasDerivAt (fun s ↦ ∫ x in Ioi L₀, x ^ k * n s x)
      ((k : ℝ) * G * (∫ x in Ioi L₀, x ^ (k - 1) * n t x) + B * L₀ ^ k -
        loss * (∫ x in Ioi L₀, x ^ k * n t x)) t ∧ (G = 0 → B = 0) := by
  refine ⟨?_, fun hG ↦ by simpa [hG] using hFlux.symm⟩
  let μ := volume.restrict (Ioi L₀)
  have hmem : ∀ᵐ x ∂μ, x ∈ Ioi L₀ := ae_restrict_mem measurableSet_Ioi
  have hweight : AEStronglyMeasurable (fun x : ℝ ↦ x ^ k) μ :=
    (continuous_id.pow k).aestronglyMeasurable
  obtain ⟨hnt, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x ↦ x ^ k * n s x) (F' := fun s x ↦ x ^ k * nt s x)
    hU (hnMeas.mono fun _ hs ↦ hweight.mul hs) hMoment (hweight.mul hntMeas)
    (hmem.mono hBound) hBoundInt (hmem.mono fun x hx' s hs ↦ (ht x hx' s hs).const_mul _)
  have hprev := integrableOn_prev_weight hL₀ hMass hMoment
  have hLoss : Integrable (fun x ↦ loss * (x ^ k * n t x)) μ := hMoment.const_mul loss
  have hbalance : ∀ᵐ x ∂μ,
      x ^ k * nt t x = -(x ^ k * (G * nx x)) - loss * (x ^ k * n t x) := by
    filter_upwards [hmem] with x hx'
    calc
      x ^ k * nt t x = x ^ k * (nt t x - (nt t x + G * nx x + loss * n t x)) := by
        rw [hPDE x hx', sub_zero]
      _ = _ := by ring
  have hTransport : Integrable (fun x ↦ x ^ k * (G * nx x)) μ := by
    refine (hnt.add hLoss).neg.congr ?_
    filter_upwards [hbalance] with x h
    change -(x ^ k * nt t x + loss * (x ^ k * n t x)) = _
    rw [h]
    ring
  have hTrace' : Tendsto (fun x ↦ x ^ k * (G * n t x)) (𝓝[Ioi L₀] L₀) (𝓝 (L₀ ^ k * B)) := by
    rw [← hFlux]
    exact ((continuous_id.pow k).continuousWithinAt.mul (continuousWithinAt_const.mul hTrace))
  have hTail' : Tendsto (fun x ↦ x ^ k * (G * n t x)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_left_comm] using hTail.const_mul G
  have hweightDeriv : IntegrableOn (fun x ↦ (↑k * x ^ (k - 1)) * (G * n t x)) (Ioi L₀) :=
    (hprev.const_mul ((k : ℝ) * G)).congr (Filter.Eventually.of_forall fun x ↦ by ring)
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hasDerivAt_pow k x) (fun x hx' ↦ (hx x hx').const_mul G)
    hTransport hweightDeriv hTrace' hTail'
  have hweightIntegral : (∫ x in Ioi L₀, (↑k * x ^ (k - 1)) * (G * n t x)) =
      (k : ℝ) * G * (∫ x in Ioi L₀, x ^ (k - 1) * n t x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by ring
  have hresult : (∫ x, x ^ k * nt t x ∂μ) =
      (k : ℝ) * G * (∫ x in Ioi L₀, x ^ (k - 1) * n t x) + B * L₀ ^ k -
        loss * (∫ x in Ioi L₀, x ^ k * n t x) := by
    have hNeg : Integrable (fun x ↦ -(x ^ k * (G * nx x))) μ := hTransport.neg
    rw [integral_congr_ae hbalance, integral_sub hNeg hLoss, integral_neg,
      integral_const_mul, hparts, hweightIntegral]
    ring
  rwa [hresult] at hderiv

end Chemistry.ParticleBalances
