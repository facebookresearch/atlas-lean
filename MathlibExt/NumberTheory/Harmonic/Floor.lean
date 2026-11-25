/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Harmonic numbers at `Nat.floor` track `Real.log` up to `O(1 / x)`

This module proves that the centered harmonic error
`harmonic ⌊x⌋₊ - log x - γ` is `O(1 / x)` at infinity, by sandwiching
harmonic numbers between the two Euler–Mascheroni sequences and combining
this with an elementary `log ⌊x⌋₊ - log x` estimate.
-/

open Asymptotics Filter

namespace Real

/-- Elementary floor–logarithm estimate used for the harmonic error term. -/
private lemma aux_norm_log_natCast_floor_sub_log :
    ∀ᶠ x : ℝ in atTop, ‖Real.log (⌊x⌋₊ : ℝ) - Real.log x‖ ≤ x⁻¹ * 2 := by
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hN_le : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hN_lt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn_ne : ⌊x⌋₊ ≠ 0 := by
    intro h
    rw [h] at hN_lt
    simp at hN_lt
    linarith
  have hn_pos : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_ne)
  have hn_ne' : ((⌊x⌋₊ : ℕ) : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hlog_mono : Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := by
    apply Real.log_le_log
    · exact hn_pos
    · exact hN_le
  have hdiv_pos : (0 : ℝ) < x / ((⌊x⌋₊ : ℕ) : ℝ) := div_pos hx_pos hn_pos
  have hlog_le : Real.log (x / ((⌊x⌋₊ : ℕ) : ℝ)) ≤ x / ((⌊x⌋₊ : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hdiv_pos
  have hlog_eq : Real.log (x / ((⌊x⌋₊ : ℕ) : ℝ))
      = Real.log x - Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    Real.log_div hx_ne hn_ne'
  have hnorm_eq : ‖Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x‖
      = Real.log (x / ((⌊x⌋₊ : ℕ) : ℝ)) := by
    rw [Real.norm_eq_abs,
      abs_of_nonpos (by linarith : Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x ≤ 0)]
    linarith [hlog_eq]
  have hfrac_eq : x / ((⌊x⌋₊ : ℕ) : ℝ) - 1
      = (x - ((⌊x⌋₊ : ℕ) : ℝ)) / ((⌊x⌋₊ : ℕ) : ℝ) := by
    field_simp
  have hfrac_le1 : (x - ((⌊x⌋₊ : ℕ) : ℝ)) / ((⌊x⌋₊ : ℕ) : ℝ)
      ≤ 1 / ((⌊x⌋₊ : ℕ) : ℝ) := by
    gcongr
    linarith
  have hx2_pos : (0 : ℝ) < x / 2 := by linarith
  have h_half : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have hn1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn_ne
    linarith
  have hn_inv_le : ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ ≤ x⁻¹ * 2 := by
    calc ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ = 1 / ((⌊x⌋₊ : ℕ) : ℝ) := by rw [one_div]
      _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le hx2_pos h_half
      _ = x⁻¹ * 2 := by field_simp
  have hfrac : x / ((⌊x⌋₊ : ℕ) : ℝ) - 1 ≤ x⁻¹ * 2 := by
    rw [hfrac_eq]
    calc (x - ((⌊x⌋₊ : ℕ) : ℝ)) / ((⌊x⌋₊ : ℕ) : ℝ)
        ≤ 1 / ((⌊x⌋₊ : ℕ) : ℝ) := hfrac_le1
      _ = ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ := by rw [one_div]
      _ ≤ x⁻¹ * 2 := hn_inv_le
  rw [hnorm_eq]
  exact le_trans hlog_le hfrac

@[expose] public section

/-- **Harmonic numbers at the floor track the logarithm.** Let $H_k$ denote the $k$-th harmonic
number, $\lfloor x \rfloor$ the floor of a real number $x$, and $\gamma$ the Euler–Mascheroni
constant. Then $H_{\lfloor x \rfloor} - \log x - \gamma = O(1/x)$ as $x \to \infty$. -/
theorem isBigO_harmonic_floor_sub_log_sub_eulerMascheroniConstant :
    (fun x : ℝ => (harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant)
      =O[atTop] (fun x : ℝ => x⁻¹) := by
  have hlog := aux_norm_log_natCast_floor_sub_log
  refine Asymptotics.IsBigO.of_bound (4 : ℝ) ?_
  filter_upwards [eventually_ge_atTop 2, hlog] with x hx2 hlogx
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx0 : (0 : ℝ) ≤ x := le_of_lt hx_pos
  have hN_le : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hN_lt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hn_ne : ⌊x⌋₊ ≠ 0 := by
    intro h
    rw [h] at hN_lt
    simp at hN_lt
    linarith
  have hn_pos : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn_ne)
  have hn_ne' : ((⌊x⌋₊ : ℕ) : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn1 : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn_ne
  have hNp1_pos : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by linarith
  have hNp1_ne : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≠ 0 := ne_of_gt hNp1_pos
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant ⌊x⌋₊
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' ⌊x⌋₊
  unfold Real.eulerMascheroniSeq at h1
  unfold Real.eulerMascheroniSeq' at h2
  rw [ite_eq_right hn_ne] at h2
  have hdiv_pos' : (0 : ℝ) < (((⌊x⌋₊ : ℕ) : ℝ) + 1) / ((⌊x⌋₊ : ℕ) : ℝ) :=
    div_pos hNp1_pos hn_pos
  have hlog_le' : Real.log ((((⌊x⌋₊ : ℕ) : ℝ) + 1) / ((⌊x⌋₊ : ℕ) : ℝ))
      ≤ ((((⌊x⌋₊ : ℕ) : ℝ) + 1) / ((⌊x⌋₊ : ℕ) : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos hdiv_pos'
  have hlog_eq' : Real.log ((((⌊x⌋₊ : ℕ) : ℝ) + 1) / ((⌊x⌋₊ : ℕ) : ℝ))
      = Real.log (((⌊x⌋₊ : ℕ) : ℝ) + 1) - Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    Real.log_div hNp1_ne hn_ne'
  have hfrac_eq' : ((((⌊x⌋₊ : ℕ) : ℝ) + 1) / ((⌊x⌋₊ : ℕ) : ℝ)) - 1
      = ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ := by
    field_simp
    ring
  have hdiff_le : Real.log (((⌊x⌋₊ : ℕ) : ℝ) + 1) - Real.log ((⌊x⌋₊ : ℕ) : ℝ)
      ≤ ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ := by
    rw [← hlog_eq', ← hfrac_eq']
    exact hlog_le'
  have hH_pos : (0 : ℝ) < (harmonic ⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant
      - Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hH_upper : (harmonic ⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant
      - Real.log ((⌊x⌋₊ : ℕ) : ℝ)
      < Real.log (((⌊x⌋₊ : ℕ) : ℝ) + 1) - Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    linarith
  have hH_le : (harmonic ⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant
      - Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ :=
    le_trans (le_of_lt hH_upper) hdiff_le
  have hn_inv_nonneg : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ :=
    le_of_lt (inv_pos.mpr hn_pos)
  have hH_norm : ‖(harmonic ⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant
      - Real.log ((⌊x⌋₊ : ℕ) : ℝ)‖ ≤ ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hH_le⟩
  have hx2_pos : (0 : ℝ) < x / 2 := by linarith
  have h_half : x / 2 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hn_inv_le : ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ ≤ x⁻¹ * 2 := by
    calc ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ = 1 / ((⌊x⌋₊ : ℕ) : ℝ) := by rw [one_div]
      _ ≤ 1 / (x / 2) := one_div_le_one_div_of_le hx2_pos h_half
      _ = x⁻¹ * 2 := by field_simp
  have hnorm_inv : ‖(x⁻¹ : ℝ)‖ = x⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx_pos)]
  have htri : ‖(harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant‖
      ≤ ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ + x⁻¹ * 2 := by
    have heq : (harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant
        = ((harmonic ⌊x⌋₊ : ℝ) - Real.eulerMascheroniConstant
          - Real.log ((⌊x⌋₊ : ℕ) : ℝ))
        + (Real.log ((⌊x⌋₊ : ℕ) : ℝ) - Real.log x) := by ring
    rw [heq]
    exact le_trans (norm_add_le _ _) (add_le_add hH_norm hlogx)
  change ‖(harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant‖
    ≤ 4 * ‖(x⁻¹ : ℝ)‖
  rw [hnorm_inv]
  calc ‖(harmonic ⌊x⌋₊ : ℝ) - Real.log x - Real.eulerMascheroniConstant‖
      ≤ ((⌊x⌋₊ : ℕ) : ℝ)⁻¹ + x⁻¹ * 2 := htri
    _ ≤ (x⁻¹ * 2) + x⁻¹ * 2 := by gcongr
    _ = 4 * x⁻¹ := by ring

end

end Real
