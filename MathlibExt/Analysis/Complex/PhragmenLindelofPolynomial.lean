/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip.lean` and
`P2M/Sol/S_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open Complex Set Filter Topology

/-!
# Phragmén–Lindelöf principle with polynomial boundary growth

In a vertical strip, a polynomial weight `(1 + |im z|) ^ α` on the two
boundary lines propagates to the interior, up to a constant depending
only on the strip and on `α`, under a double-exponential interior growth
hypothesis of rate less than `π / (b - a)`.
-/

namespace PhragmenLindelof

private theorem re_add_shift {a b : ℝ} (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    1 ≤ (z + ((1 - a : ℝ) : ℂ)).re ∧ (z + ((1 - a : ℝ) : ℂ)).re ≤ 1 + (b - a) := by
  simp only [add_re, ofReal_re]
  constructor <;> linarith

private theorem norm_shift_lower {a : ℝ} (z : ℂ) (hza : a ≤ z.re) :
    (1 + |z.im|) / 2 ≤ ‖z + ((1 - a : ℝ) : ℂ)‖ := by
  set w : ℂ := z + ((1 - a : ℝ) : ℂ) with hw
  have hre : 1 ≤ w.re := by simp only [hw, add_re, ofReal_re]; linarith
  have him : w.im = z.im := by simp [hw]
  have h1 : (1 : ℝ) ≤ ‖w‖ := le_trans hre (Complex.re_le_norm w)
  have h2 : |z.im| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
  linarith

private theorem norm_shift_upper {a b : ℝ} (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖z + ((1 - a : ℝ) : ℂ)‖ ≤ (1 + (b - a)) * (1 + |z.im|) := by
  set w : ℂ := z + ((1 - a : ℝ) : ℂ) with hw
  have hre : 1 ≤ w.re ∧ w.re ≤ 1 + (b - a) := by
    simp only [hw, add_re, ofReal_re]; constructor <;> linarith
  have him : w.im = z.im := by simp [hw]
  have hab : 0 ≤ b - a := by linarith
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ = w.re + |z.im| := by rw [him, abs_of_pos (by linarith)]
    _ ≤ (1 + (b - a)) + |z.im| := by linarith
    _ ≤ (1 + (b - a)) * (1 + |z.im|) := by nlinarith [abs_nonneg z.im]

private theorem shift_ne_zero {a : ℝ} (z : ℂ) (hza : a - 1 < z.re) :
    z + ((1 - a : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, ofReal_re, zero_re] at this
  linarith

private theorem shift_mem_slitPlane {a : ℝ} (z : ℂ) (hza : a - 1 < z.re) :
    z + ((1 - a : ℝ) : ℂ) ∈ slitPlane := by
  refine Or.inl ?_
  simp only [add_re, ofReal_re]
  linarith

/-- **Phragmén–Lindelöf principle in a vertical strip, polynomial form.**

For real `a < b` and `α ≥ 0` there is a constant `C > 0`, depending only on
`a`, `b` and `α`, with the following property. If `M ≥ 0`, `f` is differentiable
on the strip `a < re z < b` and continuous on its closure, has double-exponential
interior growth of rate `< π / (b - a)`, and satisfies
`‖f z‖ ≤ M * (1 + |im z|) ^ α` on both boundary lines, then
`‖f z‖ ≤ C * M * (1 + |im z|) ^ α` throughout the closed strip. -/
public theorem exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
    (a b α : ℝ) (hab : a < b) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℂ → ℂ) (M : ℝ), 0 ≤ M →
        DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b) →
        (∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ B : ℝ, ∀ z : ℂ, a < z.re → z.re < b →
            ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|))) →
        (∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        (∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * (1 + |z.im|) ^ α) →
        ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C * M * (1 + |z.im|) ^ α := by
  refine ⟨(2 * (1 + (b - a))) ^ α, Real.rpow_pos_of_pos (by linarith) α, ?_⟩
  intro f M hM hfd hgrowth hle_a hle_b z hza hzb
  set c₀ : ℂ := ((1 - a : ℝ) : ℂ) with hc₀
  set g : ℂ → ℂ := fun z => ((z + c₀) ^ (α : ℂ))⁻¹ with hg
  set F : ℂ → ℂ := fun z => g z * f z with hF
  have hnorm_pow : ∀ w : ℂ, ‖(w + c₀) ^ (α : ℂ)‖ = ‖w + c₀‖ ^ α :=
    fun w => Complex.norm_cpow_real _ _
  have hg_norm : ∀ w : ℂ, ‖g w‖ = (‖w + c₀‖ ^ α)⁻¹ := fun w => by
    simp only [hg, norm_inv, hnorm_pow]
  have hg_diff : DifferentiableOn ℂ g {w : ℂ | a - 1 < w.re} := by
    intro w hw
    have hw' : a - 1 < w.re := hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (z + c₀) ^ (α : ℂ)) w :=
      ((differentiableAt_id).add_const c₀).cpow_const (shift_mem_slitPlane w hw')
    have h2 : (w + c₀) ^ (α : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (shift_ne_zero w hw'))
    exact (h1.inv h2).differentiableWithinAt
  have hclosure : closure (Complex.re ⁻¹' Set.Ioo a b) = Complex.re ⁻¹' Set.Icc a b := by
    rw [closure_preimage_re, closure_Ioo hab.ne]
  have hg_dc : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo a b) := by
    refine DifferentiableOn.diffContOnCl (hg_diff.mono ?_)
    rw [hclosure]
    intro w hw
    simp only [mem_preimage, mem_Icc] at hw
    show a - 1 < w.re
    linarith [hw.1]
  have hF_dc : DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo a b) := hg_dc.smul hfd
  have hg_le_one : ∀ w : ℂ, a ≤ w.re → ‖g w‖ ≤ 1 := by
    intro w hwa
    rw [hg_norm]
    have h1 : (1 : ℝ) ≤ ‖w + c₀‖ := by
      have hre : 1 ≤ (w + c₀).re := by simp only [hc₀, add_re, ofReal_re]; linarith
      exact le_trans hre (Complex.re_le_norm _)
    have h2 : (1 : ℝ) ≤ ‖w + c₀‖ ^ α := Real.one_le_rpow h1 hα
    exact inv_le_one_of_one_le₀ h2
  have hbdry : ∀ w : ℂ, a ≤ w.re → ‖f w‖ ≤ M * (1 + |w.im|) ^ α →
      ‖F w‖ ≤ (2 : ℝ) ^ α * M := by
    intro w hwa hfw
    have hlow : (1 + |w.im|) / 2 ≤ ‖w + c₀‖ := by rw [hc₀]; exact norm_shift_lower w hwa
    have hpos1 : 0 < 1 + |w.im| := by positivity
    have hpos : 0 < ‖w + c₀‖ := lt_of_lt_of_le (by positivity) hlow
    have hpowpos : 0 < ‖w + c₀‖ ^ α := Real.rpow_pos_of_pos hpos α
    rw [hF, norm_mul, hg_norm]
    have hkey : (1 + |w.im|) ^ α ≤ (2 : ℝ) ^ α * ‖w + c₀‖ ^ α := by
      rw [← Real.mul_rpow (by norm_num) hpos.le]
      exact Real.rpow_le_rpow hpos1.le (by linarith) hα
    calc (‖w + c₀‖ ^ α)⁻¹ * ‖f w‖ ≤ (‖w + c₀‖ ^ α)⁻¹ * (M * (1 + |w.im|) ^ α) :=
          mul_le_mul_of_nonneg_left hfw (inv_nonneg.mpr hpowpos.le)
      _ ≤ (‖w + c₀‖ ^ α)⁻¹ * (M * ((2 : ℝ) ^ α * ‖w + c₀‖ ^ α)) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpowpos.le)
          exact mul_le_mul_of_nonneg_left hkey hM
      _ = (2 : ℝ) ^ α * M := by field_simp
  have hFa : ∀ w : ℂ, w.re = a → ‖F w‖ ≤ (2 : ℝ) ^ α * M :=
    fun w hw => hbdry w hw.symm.le (hle_a w hw)
  have hFb : ∀ w : ℂ, w.re = b → ‖F w‖ ≤ (2 : ℝ) ^ α * M :=
    fun w hw => hbdry w (by rw [hw]; exact hab.le) (hle_b w hw)
  have hFgrowth : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      F =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    obtain ⟨c, hc, B, hB⟩ := hgrowth
    refine ⟨c, hc, B, Asymptotics.IsBigO.of_bound 1 ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    simp only [mem_preimage, mem_Ioo] at hw
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hF, norm_mul]
    calc ‖g w‖ * ‖f w‖ ≤ 1 * ‖f w‖ :=
          mul_le_mul_of_nonneg_right (hg_le_one w hw.1.le) (norm_nonneg _)
      _ = ‖f w‖ := one_mul _
      _ ≤ Real.exp (B * Real.exp (c * |w.im|)) := hB w hw.1 hw.2
  have hPL : ‖F z‖ ≤ (2 : ℝ) ^ α * M :=
    PhragmenLindelof.vertical_strip hF_dc hFgrowth hFa hFb hza hzb
  have hup : ‖z + c₀‖ ≤ (1 + (b - a)) * (1 + |z.im|) := by
    rw [hc₀]; exact norm_shift_upper z hza hzb
  have hzne : z + c₀ ≠ 0 := by rw [hc₀]; exact shift_ne_zero z (by linarith)
  have hpos : 0 < ‖z + c₀‖ := norm_pos_iff.mpr hzne
  have hpowpos : 0 < ‖z + c₀‖ ^ α := Real.rpow_pos_of_pos hpos α
  have hfF : ‖f z‖ = ‖z + c₀‖ ^ α * ‖F z‖ := by
    rw [hF, norm_mul, hg_norm, ← mul_assoc, mul_inv_cancel₀ hpowpos.ne', one_mul]
  have hpow_up : ‖z + c₀‖ ^ α ≤ (1 + (b - a)) ^ α * (1 + |z.im|) ^ α := by
    rw [← Real.mul_rpow (by linarith) (by positivity)]
    exact Real.rpow_le_rpow hpos.le hup hα
  have h1ba : (0 : ℝ) ≤ (1 + (b - a)) ^ α := Real.rpow_nonneg (by linarith) α
  have h2a : (0 : ℝ) ≤ (2 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) α
  calc ‖f z‖ = ‖z + c₀‖ ^ α * ‖F z‖ := hfF
    _ ≤ ((1 + (b - a)) ^ α * (1 + |z.im|) ^ α) * ((2 : ℝ) ^ α * M) :=
        mul_le_mul hpow_up hPL (norm_nonneg _) (by positivity)
    _ = (2 * (1 + (b - a))) ^ α * M * (1 + |z.im|) ^ α := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
        ring

end PhragmenLindelof
