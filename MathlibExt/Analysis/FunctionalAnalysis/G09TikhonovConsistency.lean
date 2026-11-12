/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Small-noise regularization consistency under a source condition

Let `A : H →L[ℝ] K` be a bounded operator between real Hilbert spaces,
`xdag = A† w` (the source condition, with `w : K`), `b = A xdag`, and
`xlam` the Tikhonov solution for noisy data `bdelta` at parameter
`lam > 0`, characterized by the normal equations
`(A† A + lam • 1) xlam = A† bdelta`.

This file proves the consistency bound
`‖xlam - xdag‖ ≤ delta / (2 * sqrt lam) + sqrt lam * ‖w‖ / 2`
when `‖bdelta - b‖ ≤ delta`, via the normal-equation energy bound
`lam * ‖x‖^2 ≤ ‖z‖ * ‖A x‖ - ‖A x‖^2 ≤ ‖z‖^2 / 4`, and convergence
`xlam → xdag` as `delta → 0+` with the parameter choice `lam = delta`.
This is the `lam → 0` consistency regime, not the `lam → ∞` limit
proved for Tikhonov solutions in
`MathlibExt.Analysis.FunctionalAnalysis.TikhonovRegularization`.

## Key results

- `g09_energy_bound`: the normal-equation energy bound.
- `g09_norm_le_of_normal_equations`: `‖x‖ ≤ ‖z‖ / (2 * sqrt lam)`.
- `g09_consistency_bound`: the small-noise error bound.
- `g09_convergence`: convergence with `lam(delta) = delta`.
-/

@[expose] public section

open Filter Topology Real
open scoped InnerProductSpace

namespace MathlibExt.Analysis.FunctionalAnalysis.G09TikhonovConsistency

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Normal-equation energy bound: if `(A† A + lam • 1) x = A† z` with
`lam > 0`, then `lam * ‖x‖^2 ≤ ‖z‖ * ‖A x‖ - ‖A x‖^2 ≤ ‖z‖^2 / 4`. -/
theorem g09_energy_bound (A : H →L[ℝ] K) (z : K) (x : H) {lam : ℝ} (hlam : 0 < lam)
    (hx : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) x =
      ContinuousLinearMap.adjoint A z) :
    lam * ‖x‖ ^ 2 ≤ ‖z‖ * ‖A x‖ - ‖A x‖ ^ 2 ∧
      ‖z‖ * ‖A x‖ - ‖A x‖ ^ 2 ≤ ‖z‖ ^ 2 / 4 := by
  have _hlam_use : 0 < lam := hlam
  have h_inner : ⟪((ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) x), x⟫_ℝ
      = ⟪ContinuousLinearMap.adjoint A z, x⟫_ℝ := by rw [hx]
  have h_lhs : ⟪((ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) x), x⟫_ℝ
      = ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 := by
    have h1 : ((ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) x)
        = (ContinuousLinearMap.adjoint A) (A x) + lam • x := by
      simp [add_apply, smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self]
    rw [h1, inner_add_left]
    have hA : ⟪(ContinuousLinearMap.adjoint A) (A x), x⟫_ℝ = ‖A x‖ ^ 2 := by
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
    have hlam : ⟪lam • x, x⟫_ℝ = lam * ‖x‖ ^ 2 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hA, hlam]
  have h_rhs : ⟪ContinuousLinearMap.adjoint A z, x⟫_ℝ = ⟪A x, z⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have h_eq : ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 = ⟪A x, z⟫_ℝ := by
    rw [← h_lhs, h_inner, h_rhs]
  have h_cs : ⟪A x, z⟫_ℝ ≤ ‖A x‖ * ‖z‖ := real_inner_le_norm _ _
  have h_le : ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 ≤ ‖z‖ * ‖A x‖ := by
    calc ‖A x‖ ^ 2 + lam * ‖x‖ ^ 2 = ⟪A x, z⟫_ℝ := h_eq
      _ ≤ ‖A x‖ * ‖z‖ := h_cs
      _ = ‖z‖ * ‖A x‖ := mul_comm _ _
  constructor
  · linarith
  · nlinarith [sq_nonneg (‖z‖ / 2 - ‖A x‖)]

/-- Norm bound for a normal-equation solution: `‖x‖ ≤ ‖z‖ / (2 * sqrt lam)`. -/
theorem g09_norm_le_of_normal_equations (A : H →L[ℝ] K) (z : K) (x : H) {lam : ℝ}
    (hlam : 0 < lam)
    (hx : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) x =
      ContinuousLinearMap.adjoint A z) :
    ‖x‖ ≤ ‖z‖ / (2 * Real.sqrt lam) := by
  have h := g09_energy_bound A z x hlam hx
  have h_comb : lam * ‖x‖ ^ 2 ≤ ‖z‖ ^ 2 / 4 := le_trans h.1 h.2
  have hlam_nn : 0 ≤ lam := le_of_lt hlam
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hx_nn : 0 ≤ ‖x‖ := norm_nonneg _
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have h_sqrt : Real.sqrt (lam * ‖x‖ ^ 2) ≤ Real.sqrt (‖z‖ ^ 2 / 4) :=
    Real.sqrt_le_sqrt h_comb
  have h_lhs : Real.sqrt (lam * ‖x‖ ^ 2) = Real.sqrt lam * ‖x‖ := by
    rw [Real.sqrt_mul hlam_nn, Real.sqrt_sq hx_nn]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    have h4eq : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4eq, Real.sqrt_sq (by norm_num)]
  have h_rhs : Real.sqrt (‖z‖ ^ 2 / 4) = ‖z‖ / 2 := by
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hz_nn, h4]
  have h_sqrt_le : Real.sqrt lam * ‖x‖ ≤ ‖z‖ / 2 := by
    rw [← h_lhs, ← h_rhs]
    exact h_sqrt
  have h_div : ‖x‖ ≤ (‖z‖ / 2) / Real.sqrt lam := by
    rw [le_div_iff₀ hsqrt_pos]
    calc ‖x‖ * Real.sqrt lam = Real.sqrt lam * ‖x‖ := mul_comm _ _
      _ ≤ ‖z‖ / 2 := h_sqrt_le
  calc ‖x‖ ≤ (‖z‖ / 2) / Real.sqrt lam := h_div
    _ = ‖z‖ / (2 * Real.sqrt lam) := by rw [div_div]

/-- Small-noise consistency under the source condition `xdag = A† w`,
`b = A xdag`: if `‖bdelta - b‖ ≤ delta` and `xlam` solves the normal
equations for `bdelta` at `lam > 0`, then
`‖xlam - xdag‖ ≤ delta / (2 * sqrt lam) + sqrt lam * ‖w‖ / 2`. -/
theorem g09_consistency_bound (A : H →L[ℝ] K) (xdag : H) (w : K) (b bdelta : K)
    (xlam : H) {lam delta : ℝ} (hlam : 0 < lam) (hdelta : 0 ≤ delta)
    (hsource : xdag = ContinuousLinearMap.adjoint A w)
    (hb : b = A xdag) (hnoise : ‖bdelta - b‖ ≤ delta)
    (hxlam : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) xlam =
      ContinuousLinearMap.adjoint A bdelta) :
    ‖xlam - xdag‖ ≤ delta / (2 * Real.sqrt lam) + Real.sqrt lam * ‖w‖ / 2 := by
  have _hdelta_use : 0 ≤ delta := hdelta
  have hlam_nn : 0 ≤ lam := le_of_lt hlam
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have he : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) (xlam - xdag)
      = ContinuousLinearMap.adjoint A ((bdelta - b) - lam • w) := by
    have h_expand : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) (xlam - xdag)
        = (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) xlam
          - (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) xdag := by
      rw [map_sub]
    rw [h_expand, hxlam]
    have h_xdag : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) xdag
        = ContinuousLinearMap.adjoint A (b + lam • w) := by
      have h1 : (ContinuousLinearMap.adjoint A ∘L A + (lam : ℝ) • (1 : H →L[ℝ] H)) xdag
          = (ContinuousLinearMap.adjoint A) (A xdag) + lam • xdag := by
        simp [add_apply, smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self]
      rw [h1, hsource]
      have hb' : A (ContinuousLinearMap.adjoint A w) = b := by
        rw [← hsource]
        exact hb.symm
      rw [hb']
      rw [← map_smul, ← map_add]
    rw [h_xdag, ← map_sub]
    congr 1
    abel
  have h_norm : ‖xlam - xdag‖ ≤ ‖(bdelta - b) - lam • w‖ / (2 * Real.sqrt lam) :=
    g09_norm_le_of_normal_equations A _ _ hlam he
  have h_smul_norm : ‖lam • w‖ = lam * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have h_z_le : ‖(bdelta - b) - lam • w‖ ≤ delta + lam * ‖w‖ := by
    calc ‖(bdelta - b) - lam • w‖ ≤ ‖bdelta - b‖ + ‖lam • w‖ := norm_sub_le _ _
      _ ≤ delta + lam * ‖w‖ := by
        rw [h_smul_norm]
        gcongr
  have h_pos : 0 < 2 * Real.sqrt lam := mul_pos (by norm_num) hsqrt_pos
  have h_div_le : ‖(bdelta - b) - lam • w‖ / (2 * Real.sqrt lam)
      ≤ (delta + lam * ‖w‖) / (2 * Real.sqrt lam) := by
    rw [div_le_div_iff_of_pos_right h_pos]
    exact h_z_le
  have h_lam_div : lam * ‖w‖ / (2 * Real.sqrt lam) = Real.sqrt lam * ‖w‖ / 2 := by
    have hsqrt_ne : Real.sqrt lam ≠ 0 := ne_of_gt hsqrt_pos
    have hlam_eq : lam = Real.sqrt lam * Real.sqrt lam := (Real.mul_self_sqrt hlam_nn).symm
    calc lam * ‖w‖ / (2 * Real.sqrt lam)
        = (Real.sqrt lam * Real.sqrt lam) * ‖w‖ / (2 * Real.sqrt lam) := by rw [← hlam_eq]
      _ = Real.sqrt lam * ‖w‖ / 2 := by field_simp
  calc ‖xlam - xdag‖ ≤ ‖(bdelta - b) - lam • w‖ / (2 * Real.sqrt lam) := h_norm
    _ ≤ (delta + lam * ‖w‖) / (2 * Real.sqrt lam) := h_div_le
    _ = delta / (2 * Real.sqrt lam) + lam * ‖w‖ / (2 * Real.sqrt lam) := by rw [add_div]
    _ = delta / (2 * Real.sqrt lam) + Real.sqrt lam * ‖w‖ / 2 := by rw [h_lam_div]

/-- Convergence with the parameter choice `lam(delta) = delta`: as
`delta → 0+`, the Tikhonov solutions for data within `delta` of `b`
converge to `xdag`. -/
theorem g09_convergence (A : H →L[ℝ] K) (xdag : H) (w : K) (b : K)
    (xlam : ℝ → H) (bdelta : ℝ → K)
    (hsource : xdag = ContinuousLinearMap.adjoint A w) (hb : b = A xdag)
    (h : ∀ delta : ℝ, 0 < delta →
      (ContinuousLinearMap.adjoint A ∘L A + (delta : ℝ) • (1 : H →L[ℝ] H)) (xlam delta) =
        ContinuousLinearMap.adjoint A (bdelta delta) ∧ ‖bdelta delta - b‖ ≤ delta) :
    Filter.Tendsto (fun delta : ℝ => xlam delta) (𝓝[>] 0) (𝓝 xdag) := by
  have h_bound_all : ∀ delta : ℝ, 0 < delta →
      ‖xlam delta - xdag‖ ≤ Real.sqrt delta / 2 + Real.sqrt delta * ‖w‖ / 2 := by
    intro delta hdelta
    have h_pair := h delta hdelta
    have hx := h_pair.1
    have hnoise : ‖bdelta delta - b‖ ≤ delta := h_pair.2
    have h_cons := g09_consistency_bound A xdag w b (bdelta delta) (xlam delta)
      hdelta (le_of_lt hdelta) hsource hb hnoise hx
    have h_delta_eq : delta / (2 * Real.sqrt delta) = Real.sqrt delta / 2 := by
      have hdelta_nn : 0 ≤ delta := le_of_lt hdelta
      have hsqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
      have hsqrt_ne : Real.sqrt delta ≠ 0 := ne_of_gt hsqrt_pos
      have hdelta_eq : delta = Real.sqrt delta * Real.sqrt delta :=
        (Real.mul_self_sqrt hdelta_nn).symm
      calc delta / (2 * Real.sqrt delta)
          = (Real.sqrt delta * Real.sqrt delta) / (2 * Real.sqrt delta) := by rw [← hdelta_eq]
        _ = Real.sqrt delta / 2 := by field_simp
    rw [h_delta_eq] at h_cons
    exact h_cons
  have h_event : ∀ᶠ delta in 𝓝[>] (0 : ℝ),
      ‖xlam delta - xdag‖ ≤ Real.sqrt delta / 2 + Real.sqrt delta * ‖w‖ / 2 := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    exact h_bound_all delta hdelta
  have h_sqrt_tendsto : Filter.Tendsto (fun delta : ℝ => Real.sqrt delta) (𝓝[>] 0) (𝓝 0) := by
    have h_cont : Filter.Tendsto (fun delta : ℝ => Real.sqrt delta) (𝓝 0) (𝓝 (Real.sqrt 0)) :=
      Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h_cont
    exact h_cont.mono_left nhdsWithin_le_nhds
  have h1 : Filter.Tendsto (fun delta : ℝ => Real.sqrt delta / 2) (𝓝[>] 0) (𝓝 0) := by
    have := h_sqrt_tendsto.div_const 2
    simpa using this
  have h2 : Filter.Tendsto (fun delta : ℝ => Real.sqrt delta * ‖w‖ / 2) (𝓝[>] 0) (𝓝 0) := by
    have := (h_sqrt_tendsto.mul_const ‖w‖).div_const 2
    simpa using this
  have h_bound_tendsto : Filter.Tendsto
      (fun delta : ℝ => Real.sqrt delta / 2 + Real.sqrt delta * ‖w‖ / 2) (𝓝[>] 0) (𝓝 0) := by
    have := h1.add h2
    simpa using this
  have h_zero : Filter.Tendsto (fun delta : ℝ => xlam delta - xdag) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero_norm' h_event h_bound_tendsto
  have h_eq : (fun delta : ℝ => xlam delta)
      = (fun delta : ℝ => (xlam delta - xdag) + xdag) := by
    funext delta
    abel
  rw [h_eq]
  have := h_zero.add_const xdag
  simpa using this

end MathlibExt.Analysis.FunctionalAnalysis.G09TikhonovConsistency
