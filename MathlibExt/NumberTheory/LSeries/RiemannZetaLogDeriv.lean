/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A bound for the logarithmic derivative of zeta near its pole

Subtracting the logarithmic derivative of the pole factor reduces the estimate to a bound for
an entire function's logarithmic derivative on a compact rectangle.
-/

open Complex Filter Set
open scoped Topology

namespace MetaMathlibExt

/-- **Logarithmic derivative of the zeta function near its pole.** Let $\zeta$ be the Riemann zeta
function. There are real numbers $C$ and $\alpha_0 > 0$ such that for all real $\alpha$ and $\tau$
with $0 < \alpha < \alpha_0$ and $|\tau| \le 1/2$, the point $s = 1 + \alpha + i\tau$ satisfies
$|\zeta'(s)/\zeta(s)| \le 1/|s - 1| + C$.

This is the estimate $|\zeta'(s)/\zeta(s)| \le 1/|s - 1| + O(1)$ as $\alpha \to 0^+$, uniformly
in $|\tau| \le 1/2$.

Source: Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via
Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 3 (`integers-2024-A66-lem-3`). -/
public theorem exists_norm_logDeriv_riemannZeta_le_inv_norm_add :
    ∃ C α₀ : ℝ, 0 < α₀ ∧ ∀ α τ : ℝ, 0 < α → α < α₀ → |τ| ≤ 1 / 2 →
      ‖deriv riemannZeta (1 + α + τ * Complex.I) / riemannZeta (1 + α + τ * Complex.I)‖ ≤
        1 / ‖(α : ℂ) + τ * Complex.I‖ + C := by
  -- Mathlib's `riemannZeta₁` extends `(s - 1) * ζ(s)` across the pole with value one.
  have hMul {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]
  let K := Icc (1 : ℝ) 2 ×ℂ Icc (-(1 / 2) : ℝ) (1 / 2)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hNonzero : ∀ s ∈ K, riemannZeta₁ s ≠ 0 := by
    intro s hs
    by_cases h : s = 1
    · simp [h]
    · rw [hMul h]
      exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re hs.1.1)
  have hCont : ContinuousOn (fun s ↦ ‖logDeriv riemannZeta₁ s‖) K :=
    (differentiable_riemannZeta₁.deriv.continuous.continuousOn.div
      differentiable_riemannZeta₁.continuous.continuousOn hNonzero).norm
  obtain ⟨z, _, hMax⟩ := hK.exists_isMaxOn ⟨1, by norm_num [K, mem_reProdIm]⟩ hCont
  refine ⟨‖logDeriv riemannZeta₁ z‖, 1, zero_lt_one, ?_⟩
  intro α τ hα hα₀ hτ
  let s : ℂ := 1 + α + τ * I
  have hre : s.re = 1 + α := by simp [s, mul_re]
  have him : s.im = τ := by simp [s, mul_im]
  have hs : s ∈ K := by
    simp only [K, mem_reProdIm, mem_Icc, hre, him]
    exact ⟨⟨by linarith, by linarith⟩, abs_le.mp hτ⟩
  have hsne : s ≠ 1 := by
    intro h
    have : s.re = 1 := by simp [h]
    linarith
  have heq : riemannZeta₁ =ᶠ[𝓝 s] (fun t ↦ (t - 1) * riemannZeta t) := by
    filter_upwards [compl_singleton_mem_nhds hsne] with t ht
    exact hMul ht
  have hDiff : DifferentiableAt ℂ (fun t : ℂ ↦ t - 1) s := by fun_prop
  have hlog := (logDeriv_congr_nhds heq).eq_of_nhds
  rw [logDeriv_fun_mul (f := fun t : ℂ ↦ t - 1) s (sub_ne_zero.mpr hsne)
    (riemannZeta_ne_zero_of_one_le_re hs.1.1) hDiff (differentiableAt_riemannZeta hsne)] at hlog
  have hpole : logDeriv (fun t : ℂ ↦ t - 1) s = 1 / (s - 1) := by
    simp [logDeriv_apply]
  have hsplit : logDeriv riemannZeta s = logDeriv riemannZeta₁ s - 1 / (s - 1) := by
    rw [hpole, add_comm] at hlog
    exact eq_sub_of_add_eq hlog.symm
  have hsSub : s - 1 = (α : ℂ) + τ * I := by
    dsimp [s]
    rw [add_assoc, add_sub_cancel_left]
  change ‖logDeriv riemannZeta s‖ ≤ 1 / ‖(α : ℂ) + τ * I‖ + ‖logDeriv riemannZeta₁ z‖
  rw [hsplit, ← hsSub]
  calc
    _ ≤ ‖logDeriv riemannZeta₁ s‖ + ‖(1 : ℂ) / (s - 1)‖ := norm_sub_le _ _
    _ ≤ _ := by
      simpa [norm_div, add_comm] using add_le_add_right (hMax hs) (1 / ‖s - 1‖)

end MetaMathlibExt
