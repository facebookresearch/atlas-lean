/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import MathlibExt.Analysis.Convex.SelfConcordant
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Convex.DikinEllipsoid

/-!
# Bounds on a self-concordant function in the Dikin ellipsoid

If `F` is self-concordant on `Q`, `x ∈ Q` and `r = |h|_x < 1`, then with `ρ(s) = -log (1 - s) - s`,
`F(x) + DF(x)[h] + ρ(-r) ≤ F(x + h) ≤ F(x) + DF(x)[h] + ρ(r)`, where `DᵏF(x)[h, …, h]` is the
`k`-th derivative at `0` of `t ↦ F (x + t h)` and `|h|_x = (D²F(x)[h, h])^{1/2}` is the local norm.

* `bounds_of_dikin_lt_one`: the bounds above.

Following A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture
notes (Georgia Tech, 2004), Section 2.2, item I, (2.4)–(2.5).
-/

@[expose] public section

open Filter Set Topology
open scoped ContDiff

open MathlibExt.Analysis.Convex.SelfConcordant

namespace WantedExt.Analysis.Convex.SelfConcordantWanted

private theorem hasDerivAt_psi_eps {w : ℝ → ℝ} {t ε : ℝ} (hw : DifferentiableAt ℝ w t)
    (hw₀ : 0 ≤ w t) (hderiv : |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ)) (hε : 0 < ε) :
    HasDerivAt (fun s => (w s + ε) ^ (-1 / 2 : ℝ))
      (deriv w t * ((-1 / 2 : ℝ) * (w t + ε) ^ (-3 / 2 : ℝ))) t ∧
      ‖deriv w t * ((-1 / 2 : ℝ) * (w t + ε) ^ (-3 / 2 : ℝ))‖ ≤ 1 := by
  have hpos : 0 < w t + ε := add_pos_of_nonneg_of_pos hw₀ hε
  have hn : HasDerivAt (fun s => (w s + ε) ^ (-1 / 2 : ℝ))
      (deriv w t * ((-1 / 2 : ℝ) * (w t + ε) ^ (-3 / 2 : ℝ))) t := by
    have h := (hw.hasDerivAt.add_const ε).rpow_const (p := -1 / 2) (Or.inl hpos.ne')
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] at h
    simpa only [mul_assoc] using h
  refine ⟨hn, ?_⟩
  let a := (w t + ε) ^ (3 / 2 : ℝ)
  let z := (w t + ε) ^ (-3 / 2 : ℝ)
  have hz : 0 ≤ z := Real.rpow_nonneg hpos.le _
  have hpow : w t ^ (3 / 2 : ℝ) ≤ a :=
    Real.rpow_le_rpow hw₀ (le_add_of_nonneg_right hε.le) (by norm_num)
  have hwz : |deriv w t| ≤ 2 * a := (hderiv).trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have habs : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
  have haz : a * z = 1 := by
    dsimp only [a, z]
    rw [← Real.rpow_add hpos, show (3 / 2 : ℝ) + (-3 / 2) = 0 by ring, Real.rpow_zero]
  change ‖deriv w t * ((-1 / 2 : ℝ) * z)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, habs, abs_of_nonneg hz]
  calc
    |deriv w t| * (1 / 2 * z) ≤ (2 * a) * (1 / 2 * z) :=
      mul_le_mul_of_nonneg_right hwz (mul_nonneg (by norm_num) hz)
    _ = a * z := by ring
    _ = 1 := haz

private theorem abs_psi_eps_sub_le {w : ℝ → ℝ} {b ε : ℝ}
    (hε : 0 < ε) (hw : ∀ t ∈ Icc 0 b, DifferentiableAt ℝ w t)
    (hw₀ : ∀ t ∈ Icc 0 b, 0 ≤ w t)
    (hderiv : ∀ t ∈ Icc 0 b, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 b) :
    |(w t + ε) ^ (-1 / 2 : ℝ) - (w 0 + ε) ^ (-1 / 2 : ℝ)| ≤ t := by
  have hsub : Icc 0 t ⊆ Icc 0 b := fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have h1 : ∀ u ∈ Icc 0 t, HasDerivWithinAt (fun s => (w s + ε) ^ (-1 / 2 : ℝ))
      (deriv w u * ((-1 / 2 : ℝ) * (w u + ε) ^ (-3 / 2 : ℝ))) (Icc 0 t) u := by
    intro u hu
    exact ((hasDerivAt_psi_eps (hw u (hsub hu)) (hw₀ u (hsub hu))
      (hderiv u (hsub hu)) hε).1.hasDerivWithinAt)
  have h2 : ∀ u ∈ Ico 0 t, ‖deriv w u * ((-1 / 2 : ℝ) * (w u + ε) ^ (-3 / 2 : ℝ))‖ ≤ 1 := by
    intro u hu
    exact (hasDerivAt_psi_eps (hw u (hsub (Ico_subset_Icc_self hu)))
      (hw₀ u (hsub (Ico_subset_Icc_self hu))) (hderiv u (hsub (Ico_subset_Icc_self hu)))
      hε).2
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' h1 h2 t ⟨ht.1, le_rfl⟩
  rw [Real.norm_eq_abs, one_mul, sub_zero] at hmv
  exact hmv

private theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-1 / 2 : ℝ) = (√x)⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

private theorem pos_of_self_concordant_1d {w : ℝ → ℝ} {b : ℝ} (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hw : ∀ t ∈ Icc 0 b, DifferentiableAt ℝ w t)
    (hw₀ : ∀ t ∈ Icc 0 b, 0 ≤ w t)
    (hderiv : ∀ t ∈ Icc 0 b, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ))
    (hpos0 : 0 < w 0) {t : ℝ} (ht : t ∈ Icc 0 b) : 0 < w t := by
  have h0mem : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb₀⟩
  have hw0_nn : 0 ≤ w 0 := hw₀ 0 h0mem
  have hwt_nn : 0 ≤ w t := hw₀ t ht
  set r0 := √(w 0) with hr0def
  have hr0_pos : 0 < r0 := Real.sqrt_pos.mpr hpos0
  have hsq : r0 ^ 2 = w 0 := Real.sq_sqrt hw0_nn
  have hden_pos : 0 < (1 + r0) ^ 2 := by positivity
  set ε := w 0 / (2 * (1 + r0) ^ 2) with hεdef
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  have hle := abs_psi_eps_sub_le hε_pos hw hw₀ hderiv ht
  have hup : (w t + ε) ^ (-1 / 2 : ℝ) ≤ (w 0 + ε) ^ (-1 / 2 : ℝ) + t := by
    have := (abs_le.mp hle).2
    linarith
  have h0ε_pos : 0 < w 0 + ε := add_pos_of_nonneg_of_pos hw0_nn hε_pos
  have htε_pos : 0 < w t + ε := add_pos_of_nonneg_of_pos hwt_nn hε_pos
  have hsqrt0 : (w 0 + ε) ^ (-1 / 2 : ℝ) = (√(w 0 + ε))⁻¹ :=
    rpow_neg_half_eq_inv_sqrt h0ε_pos.le
  have hsqrtt : (w t + ε) ^ (-1 / 2 : ℝ) = (√(w t + ε))⁻¹ :=
    rpow_neg_half_eq_inv_sqrt htε_pos.le
  have hsqrt_le : r0 ≤ √(w 0 + ε) := by
    rw [hr0def]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hε_pos.le)
  have hsqrt0_pos : 0 < √(w 0 + ε) := Real.sqrt_pos.mpr h0ε_pos
  have hsqritt_pos : 0 < √(w t + ε) := Real.sqrt_pos.mpr htε_pos
  have hinv0 : (√(w 0 + ε))⁻¹ ≤ r0⁻¹ := (inv_le_inv₀ hsqrt0_pos hr0_pos).mpr hsqrt_le
  have ht1 : t ≤ 1 := ht.2.trans hb₁
  have hS_pos : 0 < r0⁻¹ + 1 := by positivity
  rw [hsqrtt, hsqrt0] at hup
  have hpsi_le : (√(w t + ε))⁻¹ ≤ r0⁻¹ + 1 := by linarith [hup, hinv0, ht1]
  have hge : (r0⁻¹ + 1)⁻¹ ≤ √(w t + ε) := (inv_le_comm₀ hsqritt_pos hS_pos).mp hpsi_le
  have hr0_ne : r0 ≠ 0 := ne_of_gt hr0_pos
  have h1r0_pos : 0 < 1 + r0 := by positivity
  have hS_eq : (r0⁻¹ + 1)⁻¹ = r0 / (1 + r0) := by field_simp
  have hsq2 : ((r0⁻¹ + 1)⁻¹) ^ 2 = 2 * ε := by
    rw [hS_eq, hεdef, div_pow, hsq]
    field_simp
  have hsq_le : ((r0⁻¹ + 1)⁻¹) ^ 2 ≤ w t + ε := by
    have h0 : 0 ≤ (r0⁻¹ + 1)⁻¹ := le_of_lt (inv_pos.mpr hS_pos)
    have h1 := pow_le_pow_left₀ h0 hge 2
    rwa [Real.sq_sqrt htε_pos.le] at h1
  rw [hsq2] at hsq_le
  linarith

private theorem eq_zero_of_self_concordant_1d_of_zero {w : ℝ → ℝ}
    (hw : ∀ t ∈ Icc 0 1, DifferentiableAt ℝ w t)
    (hw₀ : ∀ t ∈ Icc 0 1, 0 ≤ w t)
    (hderiv : ∀ t ∈ Icc 0 1, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ))
    (h0 : w 0 = 0) {t : ℝ} (ht : t ∈ Icc 0 1) : w t = 0 := by
  by_contra hne
  have hpos : 0 < w t := lt_of_le_of_ne (hw₀ t ht) (Ne.symm hne)
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  set t1 := t with ht1def
  have ht1mem : t1 ∈ Icc 0 1 := ht
  set wrev : ℝ → ℝ := fun s => w (t1 - s) with hwrevdef
  have hmem : ∀ s ∈ Icc 0 t1, t1 - s ∈ Icc 0 1 := by
    intro s hs
    constructor
    · linarith [hs.2]
    · linarith [hs.1, ht1]
  have hwrev : ∀ s ∈ Icc 0 t1, DifferentiableAt ℝ wrev s := by
    intro s hs
    have hw_at : HasDerivAt w (deriv w (t1 - s)) (t1 - s) :=
      (hw (t1 - s) (hmem s hs)).hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ => t1 - s) (-1) s :=
      HasDerivAt.const_sub t1 (hasDerivAt_id s)
    have hcomp := hw_at.comp s hlin
    simpa [hwrevdef, Function.comp_def] using hcomp.differentiableAt
  have hwrev₀ : ∀ s ∈ Icc 0 t1, 0 ≤ wrev s := by
    intro s hs
    dsimp [wrev]
    exact hw₀ (t1 - s) (hmem s hs)
  have hderivrev : ∀ s ∈ Icc 0 t1, |deriv wrev s| ≤ 2 * wrev s ^ (3 / 2 : ℝ) := by
    intro s hs
    have hw_at : HasDerivAt w (deriv w (t1 - s)) (t1 - s) :=
      (hw (t1 - s) (hmem s hs)).hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ => t1 - s) (-1) s :=
      HasDerivAt.const_sub t1 (hasDerivAt_id s)
    have hcomp := hw_at.comp s hlin
    have hderiv_eq : deriv wrev s = deriv w (t1 - s) * (-1) := by
      simpa [hwrevdef, Function.comp_def] using hcomp.deriv
    have habs : |deriv wrev s| = |deriv w (t1 - s)| := by
      rw [hderiv_eq, abs_mul, abs_neg, abs_one, mul_one]
    have hle := hderiv (t1 - s) (hmem s hs)
    have hwrev_s : wrev s = w (t1 - s) := by dsimp [hwrevdef]
    rw [habs, hwrev_s]
    exact hle
  have hpos0rev : 0 < wrev 0 := by
    dsimp [wrev]
    rw [sub_zero]
    exact hpos
  have ht1_self : t1 ∈ Icc 0 t1 := ⟨ht0, le_rfl⟩
  have hcontra := pos_of_self_concordant_1d ht0 ht1 hwrev hwrev₀ hderivrev hpos0rev ht1_self
  have hzero : wrev t1 = 0 := by
    dsimp [wrev]
    rw [sub_self]
    exact h0
  rw [hzero] at hcontra
  exact lt_irrefl 0 hcontra

private theorem second_deriv_bounds_of_pos {w : ℝ → ℝ}
    (hw : ∀ t ∈ Icc 0 1, DifferentiableAt ℝ w t)
    (hderiv : ∀ t ∈ Icc 0 1, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ))
    (hpos : ∀ t ∈ Icc 0 1, 0 < w t)
    (hr : √(w 0) < 1) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (√(w 0)) ^ 2 / (1 + √(w 0) * t) ^ 2 ≤ w t ∧
      w t ≤ (√(w 0)) ^ 2 / (1 - √(w 0) * t) ^ 2 := by
  have h0mem : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hw0_pos : 0 < w 0 := hpos 0 h0mem
  have hw0_nn : 0 ≤ w 0 := le_of_lt hw0_pos
  have hwt_pos : 0 < w t := hpos t ht
  have hwt_nn : 0 ≤ w t := le_of_lt hwt_pos
  set r := √(w 0) with hrdef
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hw0_pos
  have hr_nn : 0 ≤ r := le_of_lt hr_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hsq : r ^ 2 = w 0 := Real.sq_sqrt hw0_nn
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hrt_le : r * t ≤ r * 1 := mul_le_mul_of_nonneg_left ht1 hr_nn
  rw [mul_one] at hrt_le
  have h1m_pos : 0 < 1 - r * t := by linarith [hrt_le, hr]
  have h1p_pos : 0 < 1 + r * t := by positivity
  have h1m_ne : (1 - r * t) ≠ 0 := ne_of_gt h1m_pos
  have h1p_ne : (1 + r * t) ≠ 0 := ne_of_gt h1p_pos
  have hn : ∀ s ∈ Icc 0 1, HasDerivAt (fun u => w u ^ (-1 / 2 : ℝ))
      (deriv w s * ((-1 / 2 : ℝ) * w s ^ (-3 / 2 : ℝ))) s := by
    intro s hs
    have hne : w s ≠ 0 := ne_of_gt (hpos s hs)
    have h := ((hw s hs).hasDerivAt).rpow_const (p := -1 / 2) (Or.inl hne)
    rw [show (-1 / 2 : ℝ) - 1 = -3 / 2 by norm_num] at h
    simpa only [mul_assoc] using h
  have hnr : ∀ s ∈ Icc 0 1,
      ‖deriv w s * ((-1 / 2 : ℝ) * w s ^ (-3 / 2 : ℝ))‖ ≤ 1 := by
    intro s hs
    have hpos_s : 0 < w s := hpos s hs
    let a := w s ^ (3 / 2 : ℝ)
    let z := w s ^ (-3 / 2 : ℝ)
    have hz : 0 ≤ z := Real.rpow_nonneg hpos_s.le _
    have hwz : |deriv w s| ≤ 2 * a := hderiv s hs
    have habs : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    have haz : a * z = 1 := by
      dsimp only [a, z]
      rw [← Real.rpow_add hpos_s, show (3 / 2 : ℝ) + (-3 / 2) = 0 by ring, Real.rpow_zero]
    change ‖deriv w s * ((-1 / 2 : ℝ) * z)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, habs, abs_of_nonneg hz]
    calc
      |deriv w s| * (1 / 2 * z) ≤ (2 * a) * (1 / 2 * z) :=
        mul_le_mul_of_nonneg_right hwz (mul_nonneg (by norm_num) hz)
      _ = a * z := by ring
      _ = 1 := haz
  have hsub : Icc 0 t ⊆ Icc 0 1 := fun u hu => ⟨hu.1, hu.2.trans ht1⟩
  have h1 : ∀ u ∈ Icc 0 t, HasDerivWithinAt (fun u => w u ^ (-1 / 2 : ℝ))
      (deriv w u * ((-1 / 2 : ℝ) * w u ^ (-3 / 2 : ℝ))) (Icc 0 t) u := by
    intro u hu
    exact (hn u (hsub hu)).hasDerivWithinAt
  have h2 : ∀ u ∈ Ico 0 t, ‖deriv w u * ((-1 / 2 : ℝ) * w u ^ (-3 / 2 : ℝ))‖ ≤ 1 := by
    intro u hu
    exact hnr u (hsub (Ico_subset_Icc_self hu))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' h1 h2 t ⟨ht0, le_rfl⟩
  rw [Real.norm_eq_abs, one_mul, sub_zero] at hmv
  have hsqrt0 : w 0 ^ (-1 / 2 : ℝ) = (√(w 0))⁻¹ := rpow_neg_half_eq_inv_sqrt hw0_nn
  have hsqrtt : w t ^ (-1 / 2 : ℝ) = (√(w t))⁻¹ := rpow_neg_half_eq_inv_sqrt hwt_nn
  rw [hsqrtt, hsqrt0] at hmv
  have hlow : (√(w 0))⁻¹ - t ≤ (√(w t))⁻¹ := by
    have := (abs_le.mp hmv).1
    linarith
  have hup : (√(w t))⁻¹ ≤ (√(w 0))⁻¹ + t := by
    have := (abs_le.mp hmv).2
    linarith
  have hsqrt0_pos : 0 < √(w 0) := Real.sqrt_pos.mpr hw0_pos
  have hsqrtt_pos : 0 < √(w t) := Real.sqrt_pos.mpr hwt_pos
  have hrw : √(w 0) = r := rfl
  rw [hrw] at hlow hup hsqrt0_pos
  have heq1 : r⁻¹ - t = (1 - r * t) / r := by field_simp
  have heq2 : r⁻¹ + t = (1 + r * t) / r := by field_simp
  rw [heq1] at hlow
  rw [heq2] at hup
  have hA_pos : 0 < (1 - r * t) / r := div_pos h1m_pos hr_pos
  have hB_pos : 0 < (1 + r * t) / r := div_pos h1p_pos hr_pos
  have hsqrt_le : √(w t) ≤ r / (1 - r * t) := by
    have hle : (1 - r * t) / r ≤ (√(w t))⁻¹ := hlow
    have hge := (le_inv_comm₀ hA_pos hsqrtt_pos).mp hle
    simpa [inv_div] using hge
  have hsqrt_ge : r / (1 + r * t) ≤ √(w t) := by
    have hle : (√(w t))⁻¹ ≤ (1 + r * t) / r := hup
    have hge := (inv_le_comm₀ hsqrtt_pos hB_pos).mp hle
    simpa [inv_div] using hge
  have hupper : w t ≤ r ^ 2 / (1 - r * t) ^ 2 := by
    have h0 : 0 ≤ √(w t) := Real.sqrt_nonneg _
    have h1 := pow_le_pow_left₀ h0 hsqrt_le 2
    rw [Real.sq_sqrt hwt_nn, div_pow] at h1
    exact h1
  have hlower : r ^ 2 / (1 + r * t) ^ 2 ≤ w t := by
    have h0 : 0 ≤ r / (1 + r * t) := by positivity
    have h1 := pow_le_pow_left₀ h0 hsqrt_ge 2
    rw [Real.sq_sqrt hwt_nn, div_pow] at h1
    exact h1
  exact ⟨hlower, hupper⟩

private theorem second_deriv_bounds {w : ℝ → ℝ}
    (hw : ∀ t ∈ Icc 0 1, DifferentiableAt ℝ w t)
    (hw₀ : ∀ t ∈ Icc 0 1, 0 ≤ w t)
    (hderiv : ∀ t ∈ Icc 0 1, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ))
    (hr : √(w 0) < 1) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (√(w 0)) ^ 2 / (1 + √(w 0) * t) ^ 2 ≤ w t ∧
      w t ≤ (√(w 0)) ^ 2 / (1 - √(w 0) * t) ^ 2 := by
  have h0mem : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hw0_nn : 0 ≤ w 0 := hw₀ 0 h0mem
  by_cases h0 : w 0 = 0
  · have hr0 : √(w 0) = 0 := by rw [h0, Real.sqrt_zero]
    have hz : w t = 0 := eq_zero_of_self_concordant_1d_of_zero hw hw₀ hderiv h0 ht
    rw [hr0, hz]
    norm_num
  · have hpos0 : 0 < w 0 := lt_of_le_of_ne hw0_nn (Ne.symm h0)
    have hpos : ∀ s ∈ Icc 0 1, 0 < w s := fun s hs =>
      pos_of_self_concordant_1d zero_le_one le_rfl hw hw₀ hderiv hpos0 hs
    exact second_deriv_bounds_of_pos hw hderiv hpos hr ht

private theorem hasDerivAt_lin_sub {r t : ℝ} :
    HasDerivAt (fun s : ℝ => (1 : ℝ) - r * s) (-r) t := by
  have h1 : HasDerivAt (fun y : ℝ => r * y) (r * 1) t :=
    HasDerivAt.const_mul r (hasDerivAt_id t)
  rw [mul_one] at h1
  exact HasDerivAt.const_sub 1 h1

private theorem hasDerivAt_u {r t : ℝ} (hr_nn : 0 ≤ r) (hr_lt : r < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (-(fun y : ℝ => Real.log (1 - r * y))) (r / (1 - r * t)) t := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hrt_le : r * t ≤ r * 1 := mul_le_mul_of_nonneg_left ht1 hr_nn
  rw [mul_one] at hrt_le
  have hpos : 0 < 1 - r * t := by linarith
  have hne : (1 - r * t) ≠ 0 := ne_of_gt hpos
  have hlin := hasDerivAt_lin_sub (r := r) (t := t)
  have hlog := hlin.log (by simpa using hne)
  have hneg := hlog.neg
  have heq : -((-r) / (1 - r * t)) = r / (1 - r * t) := by ring
  simpa [heq] using hneg

private theorem hasDerivAt_u1 {r t : ℝ} (hr_nn : 0 ≤ r) (hr_lt : r < 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => r / (1 - r * s)) (r ^ 2 / (1 - r * t) ^ 2) t := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hrt_le : r * t ≤ r * 1 := mul_le_mul_of_nonneg_left ht1 hr_nn
  rw [mul_one] at hrt_le
  have hpos : 0 < 1 - r * t := by linarith
  have hne : (1 - r * t) ≠ 0 := ne_of_gt hpos
  have hlin := hasDerivAt_lin_sub (r := r) (t := t)
  have hconst : HasDerivAt (fun _ : ℝ => r) 0 t := hasDerivAt_const t r
  have hdiv := hconst.fun_div hlin (by simpa using hne)
  simpa [pow_two] using hdiv

private theorem hasDerivAt_lin_add {r t : ℝ} :
    HasDerivAt (fun s : ℝ => (1 : ℝ) + r * s) r t := by
  have h1 : HasDerivAt (fun y : ℝ => r * y) (r * 1) t :=
    HasDerivAt.const_mul r (hasDerivAt_id t)
  rw [mul_one] at h1
  exact HasDerivAt.const_add 1 h1

private theorem hasDerivAt_l {r t : ℝ} (hr_nn : 0 ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (-(fun y : ℝ => Real.log (1 + r * y))) (-r / (1 + r * t)) t := by
  have ht0 : 0 ≤ t := ht.1
  have hpos : 0 < 1 + r * t := by positivity
  have hne : (1 + r * t) ≠ 0 := ne_of_gt hpos
  have hlin := hasDerivAt_lin_add (r := r) (t := t)
  have hlog := hlin.log (by simpa using hne)
  have hneg := hlog.neg
  have heq : -(r / (1 + r * t)) = -r / (1 + r * t) := by ring
  simpa [heq] using hneg

private theorem hasDerivAt_l1 {r t : ℝ} (hr_nn : 0 ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => -r / (1 + r * s)) (r ^ 2 / (1 + r * t) ^ 2) t := by
  have ht0 : 0 ≤ t := ht.1
  have hpos : 0 < 1 + r * t := by positivity
  have hne : (1 + r * t) ≠ 0 := ne_of_gt hpos
  have hlin := hasDerivAt_lin_add (r := r) (t := t)
  have hconst : HasDerivAt (fun _ : ℝ => -r) 0 t := hasDerivAt_const t (-r)
  have hdiv := hconst.fun_div hlin (by simpa using hne)
  simpa [pow_two] using hdiv

private theorem upper_bound_of_second_deriv {φ : ℝ → ℝ} {r : ℝ} (hr_nn : 0 ≤ r)
    (hr_lt : r < 1) (hφ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ φ t)
    (hφ₁ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (deriv φ) t)
    (hub : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv φ) t ≤ r ^ 2 / (1 - r * t) ^ 2) :
    φ 1 ≤ φ 0 + deriv φ 0 + (-Real.log (1 - r) - r) := by
  set u : ℝ → ℝ := -(fun y : ℝ => Real.log (1 - r * y)) with hu_def
  set u1 : ℝ → ℝ := fun s : ℝ => r / (1 - r * s) with hu1_def
  have hu_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt u (u1 t) t := by
    intro t ht
    have h := hasDerivAt_u hr_nn hr_lt ht
    simpa [hu_def, hu1_def] using h
  have hu1_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt u1 (r ^ 2 / (1 - r * t) ^ 2) t := by
    intro t ht
    simpa [hu1_def] using hasDerivAt_u1 hr_nn hr_lt ht
  set f1 : ℝ → ℝ := deriv φ - u1 with hf1_def
  have hf1_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f1 (deriv (deriv φ) t - r ^ 2 / (1 - r * t) ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) t) t := (hφ₁ t ht).hasDerivAt
    have h2 := hu1_deriv t ht
    simpa [hf1_def] using h1.sub h2
  have hf1_cont : ContinuousOn f1 (Icc 0 1) := by
    have hφc : ContinuousOn (deriv φ) (Icc 0 1) := fun x hx =>
      (hφ₁ x hx).continuousAt.continuousWithinAt
    have hu1c : ContinuousOn u1 (Icc 0 1) := fun x hx =>
      (hu1_deriv x hx).continuousAt.continuousWithinAt
    simpa [hf1_def] using hφc.sub hu1c
  have hf1_diff : DifferentiableOn ℝ f1 (interior (Icc 0 1)) := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    exact ((hf1_deriv x hxIcc).differentiableAt).differentiableWithinAt
  have hf1_nonpos : ∀ x ∈ interior (Icc (0 : ℝ) 1), deriv f1 x ≤ 0 := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    have hderiv_eq : deriv f1 x = deriv (deriv φ) x - r ^ 2 / (1 - r * x) ^ 2 :=
      (hf1_deriv x hxIcc).deriv
    rw [hderiv_eq]
    have := hub x hxIcc
    linarith
  have hanti1 : AntitoneOn f1 (Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hf1_cont hf1_diff hf1_nonpos
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hle1 : ∀ t ∈ Icc (0 : ℝ) 1, f1 t ≤ f1 0 := fun t ht => hanti1 h0mem ht ht.1
  set C : ℝ := f1 0 with hC_def
  set lin : ℝ → ℝ := fun t : ℝ => t * C with hlin_def
  have hlin_deriv : ∀ t : ℝ, HasDerivAt lin C t := by
    intro t
    simpa [hlin_def] using (hasDerivAt_id t).mul_const C
  set d : ℝ → ℝ := φ - u - lin with hd_def
  have hd_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt d (f1 t - C) t := by
    intro t ht
    have hφ_at : HasDerivAt φ (deriv φ t) t := (hφ t ht).hasDerivAt
    have hu_at := hu_deriv t ht
    have hlin_at := hlin_deriv t
    have hsub1 := hφ_at.sub hu_at
    have hsub2 := hsub1.sub hlin_at
    have heq_f1 : f1 t = deriv φ t - u1 t := by simp [hf1_def, Pi.sub_apply]
    simpa [hd_def, Pi.sub_apply, heq_f1] using hsub2
  have hd_cont : ContinuousOn d (Icc 0 1) := by
    have hφc : ContinuousOn φ (Icc (0 : ℝ) 1) := fun x hx =>
      (hφ x hx).continuousAt.continuousWithinAt
    have huc : ContinuousOn u (Icc (0 : ℝ) 1) := fun x hx =>
      (hu_deriv x hx).continuousAt.continuousWithinAt
    have hlinc : ContinuousOn lin (Icc (0 : ℝ) 1) := fun x hx =>
      (hlin_deriv x).continuousAt.continuousWithinAt
    simpa [hd_def] using (hφc.sub huc).sub hlinc
  have hd_diff : DifferentiableOn ℝ d (interior (Icc (0 : ℝ) 1)) := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    exact ((hd_deriv x hxIcc).differentiableAt).differentiableWithinAt
  have hd_nonpos : ∀ x ∈ interior (Icc (0 : ℝ) 1), deriv d x ≤ 0 := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    have hderiv_eq : deriv d x = f1 x - C := (hd_deriv x hxIcc).deriv
    rw [hderiv_eq]
    have hle := hle1 x hxIcc
    simpa [hC_def] using hle
  have hanti_d : AntitoneOn d (Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hd_cont hd_diff hd_nonpos
  have hle_d : d 1 ≤ d 0 := hanti_d h0mem h1mem zero_le_one
  have hu0 : u 0 = 0 := by simp [hu_def, Pi.neg_apply]
  have hu1_eval : u 1 = -Real.log (1 - r) := by simp [hu_def, Pi.neg_apply, mul_one]
  have hu1_0 : u1 0 = r := by simp [hu1_def]
  have hlin0 : lin 0 = 0 := by simp [hlin_def]
  have hlin1 : lin 1 = C := by simp [hlin_def]
  have hf1_0 : f1 0 = deriv φ 0 - r := by
    have : f1 0 = deriv φ 0 - u1 0 := by simp [hf1_def, Pi.sub_apply]
    rw [hu1_0] at this
    exact this
  have hC_eq : C = deriv φ 0 - r := by simpa [hC_def] using hf1_0
  have hd0 : d 0 = φ 0 := by
    simp [hd_def, Pi.sub_apply, hu0, hlin0]
  have hd1 : d 1 = φ 1 - u 1 - C := by
    simp [hd_def, Pi.sub_apply, hlin1]
  rw [hd0, hd1, hu1_eval, hC_eq] at hle_d
  linarith

private theorem lower_bound_of_second_deriv {φ : ℝ → ℝ} {r : ℝ} (hr_nn : 0 ≤ r)
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ φ t)
    (hφ₁ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (deriv φ) t)
    (hlow : ∀ t ∈ Icc (0 : ℝ) 1, r ^ 2 / (1 + r * t) ^ 2 ≤ deriv (deriv φ) t) :
    φ 0 + deriv φ 0 + (-Real.log (1 + r) + r) ≤ φ 1 := by
  set l : ℝ → ℝ := -(fun y : ℝ => Real.log (1 + r * y)) with hl_def
  set l1 : ℝ → ℝ := fun s : ℝ => -r / (1 + r * s) with hl1_def
  have hl_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt l (l1 t) t := by
    intro t ht
    have h := hasDerivAt_l hr_nn ht
    simpa [hl_def, hl1_def] using h
  have hl1_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt l1 (r ^ 2 / (1 + r * t) ^ 2) t := by
    intro t ht
    simpa [hl1_def] using hasDerivAt_l1 hr_nn ht
  set f1 : ℝ → ℝ := deriv φ - l1 with hf1_def
  have hf1_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f1 (deriv (deriv φ) t - r ^ 2 / (1 + r * t) ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) t) t := (hφ₁ t ht).hasDerivAt
    have h2 := hl1_deriv t ht
    simpa [hf1_def] using h1.sub h2
  have hf1_cont : ContinuousOn f1 (Icc 0 1) := by
    have hφc : ContinuousOn (deriv φ) (Icc (0 : ℝ) 1) := fun x hx =>
      (hφ₁ x hx).continuousAt.continuousWithinAt
    have hl1c : ContinuousOn l1 (Icc (0 : ℝ) 1) := fun x hx =>
      (hl1_deriv x hx).continuousAt.continuousWithinAt
    simpa [hf1_def] using hφc.sub hl1c
  have hf1_diff : DifferentiableOn ℝ f1 (interior (Icc (0 : ℝ) 1)) := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    exact ((hf1_deriv x hxIcc).differentiableAt).differentiableWithinAt
  have hf1_nonneg : ∀ x ∈ interior (Icc (0 : ℝ) 1), 0 ≤ deriv f1 x := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    have hderiv_eq : deriv f1 x = deriv (deriv φ) x - r ^ 2 / (1 + r * x) ^ 2 :=
      (hf1_deriv x hxIcc).deriv
    rw [hderiv_eq]
    have := hlow x hxIcc
    linarith
  have hmono1 : MonotoneOn f1 (Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hf1_cont hf1_diff hf1_nonneg
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hle1 : ∀ t ∈ Icc (0 : ℝ) 1, f1 0 ≤ f1 t := fun t ht => hmono1 h0mem ht ht.1
  set C : ℝ := f1 0 with hC_def
  set lin : ℝ → ℝ := fun t : ℝ => t * C with hlin_def
  have hlin_deriv : ∀ t : ℝ, HasDerivAt lin C t := by
    intro t
    simpa [hlin_def] using (hasDerivAt_id t).mul_const C
  set d : ℝ → ℝ := φ - l - lin with hd_def
  have hd_deriv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt d (f1 t - C) t := by
    intro t ht
    have hφ_at : HasDerivAt φ (deriv φ t) t := (hφ t ht).hasDerivAt
    have hl_at := hl_deriv t ht
    have hlin_at := hlin_deriv t
    have hsub1 := hφ_at.sub hl_at
    have hsub2 := hsub1.sub hlin_at
    have heq_f1 : f1 t = deriv φ t - l1 t := by simp [hf1_def, Pi.sub_apply]
    simpa [hd_def, Pi.sub_apply, heq_f1] using hsub2
  have hd_cont : ContinuousOn d (Icc 0 1) := by
    have hφc : ContinuousOn φ (Icc (0 : ℝ) 1) := fun x hx =>
      (hφ x hx).continuousAt.continuousWithinAt
    have hlc : ContinuousOn l (Icc (0 : ℝ) 1) := fun x hx =>
      (hl_deriv x hx).continuousAt.continuousWithinAt
    have hlinc : ContinuousOn lin (Icc (0 : ℝ) 1) := fun x hx =>
      (hlin_deriv x).continuousAt.continuousWithinAt
    simpa [hd_def] using (hφc.sub hlc).sub hlinc
  have hd_diff : DifferentiableOn ℝ d (interior (Icc (0 : ℝ) 1)) := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    exact ((hd_deriv x hxIcc).differentiableAt).differentiableWithinAt
  have hd_nonneg : ∀ x ∈ interior (Icc (0 : ℝ) 1), 0 ≤ deriv d x := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
    have hderiv_eq : deriv d x = f1 x - C := (hd_deriv x hxIcc).deriv
    rw [hderiv_eq]
    have hle := hle1 x hxIcc
    simpa [hC_def] using hle
  have hmono_d : MonotoneOn d (Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hd_cont hd_diff hd_nonneg
  have hle_d : d 0 ≤ d 1 := hmono_d h0mem h1mem zero_le_one
  have hl0 : l 0 = 0 := by simp [hl_def, Pi.neg_apply]
  have hl1_eval : l 1 = -Real.log (1 + r) := by simp [hl_def, Pi.neg_apply, mul_one]
  have hl1_0 : l1 0 = -r := by simp [hl1_def]
  have hlin0 : lin 0 = 0 := by simp [hlin_def]
  have hlin1 : lin 1 = C := by simp [hlin_def]
  have hf1_0 : f1 0 = deriv φ 0 - -r := by
    have : f1 0 = deriv φ 0 - l1 0 := by simp [hf1_def, Pi.sub_apply]
    rw [hl1_0] at this
    exact this
  have hC_eq : C = deriv φ 0 + r := by
    simpa [hC_def, sub_neg_eq_add] using hf1_0
  have hd0 : d 0 = φ 0 := by
    simp [hd_def, Pi.sub_apply, hl0, hlin0]
  have hd1 : d 1 = φ 1 - l 1 - C := by
    simp [hd_def, Pi.sub_apply, hlin1]
  rw [hd0, hd1, hl1_eval, hC_eq] at hle_d
  linarith

/-- **Bounds on a self-concordant function in the Dikin ellipsoid.** If `F` is self-concordant on
`Q`, `x ∈ Q` and `r = |h|_x < 1`, then with `ρ(s) = -log (1 - s) - s`,
`F(x) + DF(x)[h] + ρ(-r) ≤ F(x + h) ≤ F(x) + DF(x)[h] + ρ(r)`.
This is (2.4)–(2.5) in item I of Section 2.2 of A. Nemirovski, *Interior Point Polynomial Time
Methods in Convex Programming*, lecture notes (2004). -/
theorem bounds_of_dikin_lt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : E → ℝ} {Q : Set E} (hF : IsSelfConcordant F Q) {x h : E}
    (hx : x ∈ Q) (hr : √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0) < 1) :
    F x + deriv (fun t : ℝ => F (x + t • h)) 0 +
        (-Real.log (1 + √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) +
          √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) ≤ F (x + h) ∧
      F (x + h) ≤ F x + deriv (fun t : ℝ => F (x + t • h)) 0 +
        (-Real.log (1 - √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) -
          √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)) := by
  have hF_copy := hF
  obtain ⟨_, hQ, hcQ, hFcd, hFcv, hbar, hsc⟩ := hF
  let y : E := x + h
  have hab : y - x = h := by simp [y]
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hline (t : ℝ) : line t = x + t • h := by
    have h0 := AffineMap.lineMap_apply x y t
    simpa [line, y, hab, add_comm] using h0
  have hlinecd : ContDiff ℝ 3 (line : ℝ → E) := by
    rw [show (line : ℝ → E) = fun t => x + t • h from funext hline]
    fun_prop
  let U := line ⁻¹' Q
  have hU : IsOpen U := hQ.preimage hlinecd.continuous
  have hU₀ : (0 : ℝ) ∈ U := by
    have : line 0 = x := by simp [hline]
    simpa [U, this] using hx
  let φ := F ∘ line
  have hφcd : ContDiffOn ℝ 3 φ U := hFcd.comp hlinecd.contDiffOn (fun _ ht => ht)
  have hφcv : ConvexOn ℝ U φ := hFcv.comp_affineMap line
  have hφ₁ : ContDiffOn ℝ 2 (deriv φ) U := hφcd.deriv_of_isOpen hU (by norm_num)
  let w := deriv (deriv φ)
  have hw₁ : ContDiffOn ℝ 1 w U := hφ₁.deriv_of_isOpen hU (by norm_num)
  have hdφ (t : ℝ) (ht : t ∈ U) : DifferentiableAt ℝ φ t :=
    ((hφcd t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdφ₁ (t : ℝ) (ht : t ∈ U) : DifferentiableAt ℝ (deriv φ) t :=
    ((hφ₁ t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdw (t : ℝ) (ht : t ∈ U) : DifferentiableAt ℝ w t :=
    ((hw₁ t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hw₀U (t : ℝ) (ht : t ∈ U) : 0 ≤ w t := by
    rw [show w t = deriv (deriv φ) t from rfl, ← derivWithin_of_isOpen hU ht]
    exact (hφcv.monotoneOn_deriv hdφ).derivWithin_nonneg
  have hd₂ : iteratedDeriv 2 φ = w := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hd₃ : iteratedDeriv 3 φ = deriv w := by rw [iteratedDeriv_succ, hd₂]
  have hφ_eq : φ = fun t : ℝ => F (x + t • h) := by
    funext t
    simp [φ, Function.comp_def, hline t]
  have hw0_nn : 0 ≤ w 0 := hw₀U 0 hU₀
  have hw0_eq : w 0 = iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0 := by
    rw [← hφ_eq, ← hd₂]
  have hrw : √(w 0) < 1 := by rw [hw0_eq]; exact hr
  have hr_nn : 0 ≤ √(w 0) := Real.sqrt_nonneg _
  have hw0_lt1 : w 0 < 1 := by
    have hsq : (√(w 0)) ^ 2 = w 0 := Real.sq_sqrt hw0_nn
    nlinarith [hrw, hr_nn, hsq, sq_nonneg (√(w 0))]
  have hw0_lt1' : iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0 < 1 := by
    rw [← hw0_eq]
    exact hw0_lt1
  have hx_h : y ∈ Q := mem_of_dikin_lt_one hF_copy hx (by rw [hab]; exact hw0_lt1')
  have hx_h' : x + h ∈ Q := by simpa [y] using hx_h
  have hIcc : Icc (0 : ℝ) 1 ⊆ U := by
    intro t ht
    have hmem : x + t • h ∈ Q := hcQ.add_smul_mem hx hx_h' ht
    have : line t ∈ Q := by simpa [hline t] using hmem
    simpa [U] using this
  have hwIcc : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ w t :=
    fun t ht => hdw t (hIcc ht)
  have hw₀Icc : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ w t := fun t ht => hw₀U t (hIcc ht)
  have hderivIcc : ∀ t ∈ Icc (0 : ℝ) 1, |deriv w t| ≤ 2 * w t ^ (3 / 2 : ℝ) := by
    intro t ht
    have htU : t ∈ U := hIcc ht
    have htranslate : (fun a : ℝ => F (line t + a • h)) = fun a => φ (t + a) := by
      funext a
      change F (line t + a • h) = F (line (t + a))
      rw [hline t, hline (t + a), add_smul, add_assoc]
    have hh := hsc (line t) htU h
    rw [htranslate, iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_add] at hh
    simpa [add_zero, hd₂, hd₃] using hh
  have hbds : ∀ t ∈ Icc (0 : ℝ) 1,
      (√(w 0)) ^ 2 / (1 + √(w 0) * t) ^ 2 ≤ w t ∧
        w t ≤ (√(w 0)) ^ 2 / (1 - √(w 0) * t) ^ 2 :=
    fun t ht => second_deriv_bounds hwIcc hw₀Icc hderivIcc hrw ht
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1,
      (√(w 0)) ^ 2 / (1 + √(w 0) * t) ^ 2 ≤ deriv (deriv φ) t :=
    fun t ht => (hbds t ht).1
  have hup : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv φ) t ≤ (√(w 0)) ^ 2 / (1 - √(w 0) * t) ^ 2 :=
    fun t ht => (hbds t ht).2
  have hφIcc : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ φ t :=
    fun t ht => hdφ t (hIcc ht)
  have hφ₁Icc : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (deriv φ) t :=
    fun t ht => hdφ₁ t (hIcc ht)
  have hup_bound := upper_bound_of_second_deriv hr_nn hrw hφIcc hφ₁Icc hup
  have hlow_bound := lower_bound_of_second_deriv hr_nn hφIcc hφ₁Icc hlow
  have hφ0 : φ 0 = F x := by simp [φ, Function.comp_def, hline]
  have hφ1 : φ 1 = F (x + h) := by simp [φ, Function.comp_def, hline]
  have hderiv0 : deriv φ 0 = deriv (fun t : ℝ => F (x + t • h)) 0 := by rw [hφ_eq]
  have hr_eq : √(w 0) = √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0) := by
    rw [hw0_eq]
  rw [hφ0, hφ1, hderiv0, hr_eq] at hlow_bound hup_bound
  exact ⟨hlow_bound, hup_bound⟩

end WantedExt.Analysis.Convex.SelfConcordantWanted
