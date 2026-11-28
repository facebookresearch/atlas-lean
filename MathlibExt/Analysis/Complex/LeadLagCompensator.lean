/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Order.Field

/-!
# Gain and phase of a lead or lag compensator

The frequency response of `C(s) = k (s + a) / (s + b)` is evaluated at `s = iω`.
For `k, a, b > 0`, on the nonnegative frequency axis the principal phase has a unique maximum
at `√(ab)` if `a < b` (lead) and a unique minimum there if `b < a` (lag). If `a = b`,
the phase is identically zero.
-/

public section

open Filter Set
open scoped Real Topology

namespace MetaMathlibExt

private theorem arctan_sub_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ω : ℝ) :
    Real.arctan (ω / a) - Real.arctan (ω / b) =
      Real.arctan ((b - a) * ω / (a * b + ω ^ 2)) := by
  have hab := mul_ne_zero ha.ne' hb.ne'
  have hprod : ω / a * -(ω / b) = -(ω ^ 2 / (a * b)) := by
    field_simp
  have h : ω / a * -(ω / b) < 1 := by
    rw [hprod]
    have : 0 ≤ ω ^ 2 / (a * b) := by positivity
    linarith
  have hnum : ω / a + -(ω / b) = (b - a) * ω / (a * b) := by
    field_simp
    ring
  rw [sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add h, hnum, hprod, sub_neg_eq_add,
    ← div_self hab, ← add_div, div_div_div_cancel_right₀ hab]

-- The sign of the difference after clearing the positive denominators is the
-- sign of `(y - x) * (c - x * y)`.
private theorem phaseKernel_mono {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun x : ℝ ↦ x / (c + x ^ 2)) (Icc 0 (√c)) ∧
      StrictAntiOn (fun x : ℝ ↦ x / (c + x ^ 2)) (Ici (√c)) := by
  have hr := Real.sqrt_pos.2 hc
  have hrsq := Real.sq_sqrt hc.le
  have hcross (x y : ℝ) :
      x / (c + x ^ 2) < y / (c + y ^ 2) ↔ 0 < (y - x) * (c - x * y) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [← sub_pos (a := y * (c + x ^ 2)), show
      y * (c + x ^ 2) - x * (c + y ^ 2) = (y - x) * (c - x * y) by ring]
  constructor
  · intro x hx y hy hxy
    have h₁ := mul_lt_mul_of_pos_right hxy (hx.1.trans_lt hxy)
    have h₂ := mul_le_mul hy.2 hy.2 hy.1 hr.le
    exact (hcross x y).2 (mul_pos (sub_pos.mpr hxy) (sub_pos.mpr (by nlinarith)))
  · intro x hx y _ hxy
    have hx' : √c ≤ x := hx
    have hxpos := hr.trans_le hx'
    have h₁ := mul_lt_mul_of_pos_left hxy hxpos
    have h₂ := mul_le_mul hx' hx' hr.le hxpos.le
    exact (hcross y x).2 (mul_pos_of_neg_of_neg (sub_neg.mpr hxy) (sub_neg.mpr (by nlinarith)))

/-- For `k, a, b > 0`, the gain of `C(iω) = k (a + iω)/(b + iω)` is
`k √((ω² + a²)/(ω² + b²))`, equals `ka/b` at DC and tends to `k` as `|ω| → ∞`.
Its principal phase is `arctan (ω/a) - arctan (ω/b)` in `(-π/2, π/2)`.
For `a < b` the phase is positive at positive frequencies, increases strictly up to
`√(ab)`, then decreases strictly, attaining its unique maximum there on `[0, ∞)`.
For `b < a` the signs and monotonicities reverse and the maximum becomes a minimum.
In either case the sine and tangent at `√(ab)` are `(b-a)/(b+a)` and `(b-a)/(2√(ab))`.

Source: K. J. Åström and R. M. Murray, *Feedback Systems*, 2nd ed., electronic
version v3.1.5 (2020-07-24), §12.3, (12.7) and Figure 12.9
<https://www.cds.caltech.edu/~murray/books/AM05/pdf/fbs-loopsyn_24Jul2020.pdf>,
for the transfer function and qualitative response. The exact extremum frequency
and phase formulas are derived here. -/
theorem lead_lag_frequency_response {k a b : ℝ} (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) :
    let C := fun ω : ℝ ↦ (k : ℂ) * ((a : ℂ) + (ω : ℂ) * Complex.I) /
      ((b : ℂ) + (ω : ℂ) * Complex.I)
    let φ := fun ω ↦ (C ω).arg
    let r := √(a * b)
    (∀ ω, ‖C ω‖ = k * √((ω ^ 2 + a ^ 2) / (ω ^ 2 + b ^ 2)) ∧
      φ ω = Real.arctan (ω / a) - Real.arctan (ω / b) ∧
      φ ω ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) ∧
    ‖C 0‖ = k * a / b ∧ Tendsto (fun ω ↦ ‖C ω‖) (cocompact ℝ) (𝓝 k) ∧
    Real.sin (φ r) = (b - a) / (b + a) ∧ Real.tan (φ r) = (b - a) / (2 * r) ∧
    (a < b → (∀ ω > 0, 0 < φ ω) ∧ StrictMonoOn φ (Icc 0 r) ∧ StrictAntiOn φ (Ici r) ∧
      ∀ ω ≥ 0, ω ≠ r → φ ω < φ r) ∧
    (b < a → (∀ ω > 0, φ ω < 0) ∧ StrictAntiOn φ (Icc 0 r) ∧ StrictMonoOn φ (Ici r) ∧
      ∀ ω ≥ 0, ω ≠ r → φ r < φ ω) := by
  intro C φ r
  have hnorm (x ω : ℝ) : ‖(x : ℂ) + (ω : ℂ) * Complex.I‖ = √(ω ^ 2 + x ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, sq, add_comm]
  have hgain (ω : ℝ) : ‖C ω‖ = k * √((ω ^ 2 + a ^ 2) / (ω ^ 2 + b ^ 2)) := by
    simp only [C, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, hnorm]
    rw [Real.sqrt_div (by positivity), mul_div_assoc]
  have hdc : ‖C 0‖ = k * a / b := by
    simp [C, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, abs_of_pos ha, abs_of_pos hb]
  have hlimit : Tendsto (fun ω ↦ ‖C ω‖) (cocompact ℝ) (𝓝 k) := by
    have hs : Tendsto (fun ω : ℝ ↦ ω ^ 2) (cocompact ℝ) atTop := by
      refine ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
        (tendsto_norm_cocompact_atTop (E := ℝ))).congr fun ω ↦ ?_
      change ‖ω‖ ^ 2 = ω ^ 2
      rw [Real.norm_eq_abs, sq_abs]
    have hd : Tendsto (fun ω : ℝ ↦ ω ^ 2 + b ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop.2 fun M ↦ (tendsto_atTop.1 hs M).mono fun _ hM ↦
        hM.trans (le_add_of_nonneg_right (sq_nonneg b))
    have hv : Tendsto (fun ω : ℝ ↦ (a ^ 2 - b ^ 2) / (ω ^ 2 + b ^ 2)) (cocompact ℝ) (𝓝 0) := by
      simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero.comp hd).const_mul (a ^ 2 - b ^ 2)
    have hq : Tendsto (fun ω : ℝ ↦ (ω ^ 2 + a ^ 2) / (ω ^ 2 + b ^ 2)) (cocompact ℝ) (𝓝 1) := by
      rw [← add_zero (1 : ℝ)]
      refine (hv.const_add 1).congr fun ω ↦ ?_
      have : 0 < ω ^ 2 + b ^ 2 := by positivity
      field_simp
      ring
    simpa only [Real.sqrt_one, mul_one, ← hgain] using hq.sqrt.const_mul k
  have harg (ω : ℝ) : φ ω = Real.arctan ((b - a) * ω / (a * b + ω ^ 2)) := by
    have hn : 0 < b ^ 2 + ω ^ 2 := by positivity
    have hre : (C ω).re = k * (a * b + ω ^ 2) / (b ^ 2 + ω ^ 2) := by
      simp only [C, Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, mul_one, sub_zero, zero_add, add_zero]
      ring
    have him : (C ω).im = k * ((b - a) * ω) / (b ^ 2 + ω ^ 2) := by
      simp only [C, Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, mul_one, sub_zero, zero_add, add_zero]
      ring
    have hp : 0 < (C ω).re := by rw [hre]; positivity
    have hl := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hp)
    have hu := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hp)
    change (C ω).arg = _
    rw [← Real.arctan_tan hl hu, Complex.tan_arg, hre, him]
    congr 1
    have : 0 < a * b + ω ^ 2 := by positivity
    field_simp
  have hab : 0 < a * b := mul_pos ha hb
  have hr : 0 < r := Real.sqrt_pos.2 hab
  have hrsq : r ^ 2 = a * b := Real.sq_sqrt hab.le
  have ht : (b - a) * r / (a * b + r ^ 2) = (b - a) / (2 * r) := by
    rw [← hrsq]
    field_simp
    ring
  have hsin : Real.sin (φ r) = (b - a) / (b + a) := by
    rw [harg, ht, Real.sin_arctan]
    have hs : √(1 + ((b - a) / (2 * r)) ^ 2) = (b + a) / (2 * r) := calc
      _ = √(((b + a) / (2 * r)) ^ 2) := by
        congr 1
        field_simp
        nlinarith [hrsq]
      _ = _ := Real.sqrt_sq (by positivity)
    rw [hs]
    field_simp
  have htan : Real.tan (φ r) = (b - a) / (2 * r) := by
    rw [harg, Real.tan_arctan, ht]
  obtain ⟨hmono, hanti⟩ := phaseKernel_mono hab
  have hφ (ω : ℝ) : φ ω = Real.arctan ((b - a) * (ω / (a * b + ω ^ 2))) := by
    rw [harg, mul_div_assoc]
  refine ⟨fun ω ↦ ⟨hgain ω, (harg ω).trans (arctan_sub_div ha hb ω).symm,
    harg ω ▸ Real.arctan_mem_Ioo _⟩, hdc, hlimit, hsin, htan, ?_, ?_⟩
  · intro hlead
    have hba := sub_pos.mpr hlead
    have h₁ : StrictMonoOn φ (Icc 0 r) := by
      intro x hx y hy hxy
      rw [hφ, hφ]
      exact Real.arctan_strictMono (mul_lt_mul_of_pos_left (hmono hx hy hxy) hba)
    have h₂ : StrictAntiOn φ (Ici r) := by
      intro x hx y hy hxy
      rw [hφ, hφ]
      exact Real.arctan_strictMono (mul_lt_mul_of_pos_left (hanti hx hy hxy) hba)
    refine ⟨fun ω hω ↦ ?_, h₁, h₂, fun ω hω hne ↦ ?_⟩
    · rw [harg, Real.arctan_pos]
      positivity
    · rcases lt_or_gt_of_ne hne with h | h
      · exact h₁ ⟨hω, h.le⟩ ⟨hr.le, le_rfl⟩ h
      · exact h₂ le_rfl h.le h
  · intro hlag
    have hba := sub_neg.mpr hlag
    have h₁ : StrictAntiOn φ (Icc 0 r) := by
      intro x hx y hy hxy
      rw [hφ, hφ]
      exact Real.arctan_strictMono (mul_lt_mul_of_neg_left (hmono hx hy hxy) hba)
    have h₂ : StrictMonoOn φ (Ici r) := by
      intro x hx y hy hxy
      rw [hφ, hφ]
      exact Real.arctan_strictMono (mul_lt_mul_of_neg_left (hanti hx hy hxy) hba)
    refine ⟨fun ω hω ↦ ?_, h₁, h₂, fun ω hω hne ↦ ?_⟩
    · rw [harg, Real.arctan_lt_zero]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hba hω) (by positivity)
    · rcases lt_or_gt_of_ne hne with h | h
      · exact h₁ ⟨hω, h.le⟩ ⟨hr.le, le_rfl⟩ h
      · exact h₂ le_rfl h.le h

end MetaMathlibExt
