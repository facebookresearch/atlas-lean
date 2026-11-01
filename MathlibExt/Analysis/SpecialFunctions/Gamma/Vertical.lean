/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import MathlibExt.Analysis.Complex.VerticalIntegral.Integrable
import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet

/-!
# The Gamma function on vertical lines

Bounds and asymptotics for `Γ(σ + it)` with `σ` fixed and `|t|` large.

## Main statements

* `Complex.norm_Gamma_le_Gamma_re`: `‖Γ s‖ ≤ Γ(Re s)` for `Re s > 0`.
* `Complex.mellin_exp_neg`: the Mellin transform of `e^{-t}` is `Γ`.
* `Complex.norm_Gamma_vertical_le`: `‖Γ(σ + it)‖ ≤ Γ(σ + 2) / ‖σ + it‖²` for `σ > 0`.
* `Complex.integral_cpow_mul_Gamma_vertical`: by Mellin inversion,
  `(1/2π) ∫ y^{σ+it} Γ(σ+it) dt = e^{-1/y}` for `σ, y > 0`.
* `Complex.norm_Gamma_vertical_isEquivalent`: **Stirling's formula on vertical lines**,
  `|Γ(σ + it)| ∼ √(2π) |t|^{σ - 1/2} e^{-π|t|/2}` as `|t| → ∞`.
* `Complex.exists_norm_Gamma_vertical_le_mul_rpow`: for large `|t|`,
  `‖Γ(σ₁ + it)‖ ≤ 3 |t|^{σ₁ - σ₂} ‖Γ(σ₂ + it)‖`.
-/

open Filter Topology Asymptotics MeasureTheory

@[expose] public section

namespace Complex

/-- `‖Γ s‖ ≤ Γ(Re s)` for `Re s > 0`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- The Mellin transform of `e^{-t}` is `Γ` on `Re s > 0`. -/
theorem mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Gamma s := by
  rw [Gamma_eq_integral hs, GammaIntegral, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [smul_eq_mul, mul_comm]

/-- Quadratic decay of `Γ` on the line `Re s = σ > 0`:
`‖Γ(σ + it)‖ ≤ Γ(σ + 2) / ‖σ + it‖²`. -/
theorem norm_Gamma_vertical_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖Gamma ((σ : ℂ) + t * I)‖ ≤ Real.Gamma (σ + 2) / ‖(σ : ℂ) + (t : ℂ) * I‖ ^ 2 := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg re h
    simp [hsre] at this; linarith
  have h2 : Gamma (s + 2) = (s + 1) * s * Gamma s := by
    rw [show s + 2 = (s + 1) + 1 by ring, Gamma_add_one _ hs1, Gamma_add_one _ hs0]
    ring
  have hn : ‖s‖ ≤ ‖s + 1‖ := by
    have e1 : s + 1 = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      rw [hs]; push_cast; ring
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, e1, hs,
      Complex.sq_norm, Complex.sq_norm, normSq_add_mul_I, normSq_add_mul_I]
    nlinarith
  have hb := norm_Gamma_le_Gamma_re (s := s + 2) (by simp [hsre]; linarith)
  rw [show (s + 2).re = σ + 2 by simp [hsre], h2, norm_mul, norm_mul] at hb
  have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  rw [le_div_iff₀ (by positivity)]
  calc ‖Gamma s‖ * ‖s‖ ^ 2 = ‖s‖ * ‖s‖ * ‖Gamma s‖ := by ring
    _ ≤ ‖s + 1‖ * ‖s‖ * ‖Gamma s‖ := by gcongr
    _ ≤ _ := hb

/-- `t ↦ Γ(σ + it)` is continuous for `σ > 0`. -/
theorem continuous_Gamma_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ => Gamma ((σ : ℂ) + t * I) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  refine ContinuousAt.comp (g := Gamma) ?_ (by fun_prop)
  refine (differentiableAt_Gamma _ fun m h => ?_).continuousAt
  have := congrArg re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

private theorem cpow_mul_Gamma_vertical_aux {σ y : ℝ} (hσ0 : 0 < σ) (hx0 : 0 < y) :
    Integrable (fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I)) ∧
    (1 / (2 * Real.pi)) • ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I) =
      ((Real.exp (-1 / y) : ℝ) : ℂ) := by
  set f : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ) with hf
  have hmel : ∀ s : ℂ, 0 < s.re → mellin f s = Gamma s := fun s hs => mellin_exp_neg hs
  have hconv : MellinConvergent f σ := by
    have := GammaIntegral_convergent (s := (σ : ℂ)) (by simpa using hσ0)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [hf, smul_eq_mul, mul_comm]
  have hbd2 : ∀ t : ℝ, ‖Gamma ((σ : ℂ) + t * I)‖ ≤
      Real.Gamma (σ + 2) / ‖(σ : ℂ) + (t : ℂ) * I‖ ^ (0 + 2) := by
    simpa using norm_Gamma_vertical_le hσ0
  have hGc := continuous_Gamma_vertical hσ0
  have hint : Integrable
      (fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I)) := by
    refine integrable_of_norm_le_div_pow hσ0 (n := 0)
      (M := y ^ σ * Real.Gamma (σ + 2))
      (by have := Real.Gamma_pos_of_pos (show 0 < σ + 2 by linarith); positivity) ?_ ?_
    · refine Continuous.mul ?_ hGc
      exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx0.ne'))
    · intro t
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, mul_div_assoc]
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul,
        sub_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hbd2 t) (by positivity)
  have hVI : VerticalIntegrable (mellin f) σ := by
    have hG : Integrable (fun t : ℝ => Gamma ((σ : ℂ) + t * I)) :=
      integrable_of_norm_le_div_pow hσ0 (n := 0)
        (le_of_lt (Real.Gamma_pos_of_pos (show 0 < σ + 2 by linarith))) hGc hbd2
    refine hG.congr (Eventually.of_forall fun t => ?_)
    exact (hmel _ (by simpa using hσ0)).symm
  have hinv := mellinInv_mellin_eq σ f (x := 1 / y) (by positivity) hconv hVI
    (by fun_prop)
  have heq : (fun t : ℝ => (((1 / y : ℝ) : ℂ)) ^ (-((σ : ℂ) + t * I)) •
      mellin f ((σ : ℂ) + t * I)) = fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) *
        Gamma ((σ : ℂ) + t * I) := by
    funext t
    rw [hmel _ (by simpa using hσ0), smul_eq_mul, cpow_neg, one_div,
      ofReal_inv, inv_cpow _ _ (by simp [arg_ofReal_of_nonneg hx0.le,
        Real.pi_ne_zero.symm]), inv_inv]
  rw [mellinInv, heq] at hinv
  refine ⟨hint, ?_⟩
  rw [hinv]
  simp only [hf, one_div, neg_div]

/-- `t ↦ y^{σ+it} Γ(σ+it)` is integrable for `σ > 0`, `y > 0`. -/
theorem integrable_cpow_mul_Gamma_vertical {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) :
    Integrable (fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I)) :=
  (cpow_mul_Gamma_vertical_aux hσ hy).1

/-- **Mellin inversion for `e^{-t}`**: `(1/2π) ∫ y^{σ+it} Γ(σ+it) dt = e^{-1/y}` for
`σ, y > 0`. -/
theorem integral_cpow_mul_Gamma_vertical {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) :
    (1 / (2 * Real.pi)) • ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I) * Gamma ((σ : ℂ) + t * I) =
      ((Real.exp (-1 / y) : ℝ) : ℂ) :=
  (cpow_mul_Gamma_vertical_aux hσ hy).2

/-- `(σ - 1/2) log ‖σ/t + i‖ + (t arctan (σ/t) - σ) → 0` as `t → ∞`. -/
private lemma tendsto_stirling_vertical_error (σ : ℝ) :
    Tendsto (fun t : ℝ => (σ - 1 / 2) * Real.log ‖((σ / t : ℝ) : ℂ) + I‖ +
      (t * Real.arctan (σ / t) - σ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log ‖((σ / t : ℝ) : ℂ) + I‖) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => σ / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hc : Continuous fun u : ℝ => ‖((u : ℝ) : ℂ) + I‖ := by fun_prop
    have h := (hc.tendsto 0).comp hu
    simp only [ofReal_zero, zero_add, norm_I] at h
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun t : ℝ => t * Real.arctan (σ / t)) atTop (𝓝 σ) := by
    have hd : HasDerivAt (fun u : ℝ => Real.arctan (σ * u)) σ 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul σ).arctan
      simpa using this
    have hs := hd.tendsto_slope_zero
    have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝[≠] 0) :=
      tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    refine (hs.comp hinv).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [div_eq_mul_inv, smul_eq_mul]
  have := (h1.const_mul (σ - 1 / 2)).add (h2.sub_const σ)
  simpa using this

/-- **Stirling's formula on vertical lines.** For fixed real `σ`, as `|t| → ∞`,
`|Γ(σ + it)| ∼ e^{-π|t|/2} |t|^{σ - 1/2} √(2π)`. The filter is
`comap (fun t => |t|) atTop`, i.e. `|t| → ∞` with `t` of either sign. -/
theorem norm_Gamma_vertical_isEquivalent (σ : ℝ) :
    IsEquivalent (comap (fun t : ℝ => |t|) atTop)
      (fun t : ℝ => ‖Gamma (σ + t * I)‖)
      (fun t : ℝ => Real.exp (-(Real.pi * |t|) / 2) * |t| ^ (σ - 1 / 2) *
        Real.sqrt (2 * Real.pi)) := by
  set F : ℝ → ℝ := fun t => ‖Gamma (σ + t * I)‖ with hF
  set G : ℝ → ℝ := fun t => Real.exp (-(Real.pi * t) / 2) * t ^ (σ - 1 / 2) *
    Real.sqrt (2 * Real.pi) with hG
  have hFabs : F = F ∘ (fun t => |t|) := by
    funext t
    simp only [Function.comp, hF]
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h]
      have : ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [this, Gamma_conj, norm_conj]
  have hGabs : (fun t : ℝ => Real.exp (-(Real.pi * |t|) / 2) * |t| ^ (σ - 1 / 2) *
      Real.sqrt (2 * Real.pi)) = G ∘ (fun t => |t|) := rfl
  rw [hGabs, hFabs]
  refine IsEquivalent.comp_tendsto ?_ tendsto_comap
  apply isEquivalent_of_tendsto_one
  obtain ⟨C, hC⟩ := Gamma_eq_exp_stirling_sector (Real.pi / 4) (by positivity)
  set A : ℝ → ℝ := fun t => (σ - 1 / 2) * (Real.log ‖(σ : ℂ) + t * I‖ - Real.log t) +
    (t * Real.arctan (σ / t) - σ) with hA
  have hAlim : Tendsto A atTop (𝓝 0) := by
    refine (tendsto_stirling_vertical_error σ).congr' (eventually_atTop.2 ⟨1, fun t ht => ?_⟩)
    have ht0 : 0 < t := by linarith
    simp only [hA]
    congr 2
    have : (σ : ℂ) + t * I = (t : ℂ) * (((σ / t : ℝ) : ℂ) + I) := by
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      push_cast; field_simp
    rw [this, norm_mul, norm_real, Real.norm_of_nonneg ht0.le,
      Real.log_mul ht0.ne' (by simp [Complex.ext_iff]), add_sub_cancel_left]
  have hCt : Tendsto (fun t : ℝ => |C| / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hbound : ∀ᶠ t in atTop, Real.exp (A t - |C| / t) ≤ (F / G) t ∧
      (F / G) t ≤ Real.exp (A t + |C| / t) := by
    filter_upwards [eventually_ge_atTop (|σ| + 1)] with t ht
    have ht0 : 0 < t := by linarith [abs_nonneg σ]
    set z : ℂ := (σ : ℂ) + t * I with hz
    set x : ℝ := σ / t with hx
    have hx1 : |x| < 1 := by
      rw [hx, abs_div, abs_of_pos ht0, div_lt_one ht0]; linarith
    have harc1 : Real.arctan x < Real.pi / 4 := by
      rw [← Real.arctan_one]; exact Real.arctan_strictMono (lt_of_abs_lt hx1)
    have harc2 : -(Real.pi / 4) < Real.arctan x := by
      rw [← Real.arctan_one, ← Real.arctan_neg]
      exact Real.arctan_strictMono (neg_lt_of_abs_lt hx1)
    set θ := Real.pi / 2 - Real.arctan x with hθ
    have hs : 0 < Real.sqrt (1 + x ^ 2) := by positivity
    have hzpolar : z = ((t * Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) * (cos θ + sin θ * I) := by
      rw [← ofReal_cos, ← ofReal_sin, hθ, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
        Real.sin_arctan, Real.cos_arctan]
      apply Complex.ext <;> simp [hz, hx] <;> field_simp
    have harg : arg z = θ := by
      rw [hzpolar]
      exact arg_mul_cos_add_sin_mul_I (by positivity)
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hz0 : z ≠ 0 := by
      intro h
      have := congrArg im h
      simp [hz] at this
      linarith
    obtain ⟨E, hE, hΓ⟩ := hC z hz0 (by rw [harg]; linarith) (by rw [harg]; linarith)
    have hnz : t ≤ ‖z‖ := by
      have := abs_im_le_norm z
      simpa [hz, abs_of_pos ht0] using this
    have hEre : |E.re| ≤ |C| / t := by
      calc |E.re| ≤ ‖E‖ := abs_re_le_norm E
        _ ≤ C / ‖z‖ := hE
        _ ≤ |C| / ‖z‖ := by gcongr; exact le_abs_self C
        _ ≤ |C| / t := by gcongr
    have hratio : (F / G) t = Real.exp (A t + E.re) := by
      simp only [Pi.div_apply, hF, hG, hA]
      rw [← hz, hΓ, norm_exp, Real.rpow_def_of_pos ht0, Real.sqrt_eq_rpow,
        Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      simp only [add_re, sub_re, mul_re, sub_im, log_re, log_im, harg, one_re, one_im,
        div_ofNat_re, div_ofNat_im]
      simp only [one_div, zero_div, sub_zero, Complex.norm_mul, norm_ofNat, norm_real,
        Real.norm_eq_abs, Real.abs_pi, zero_mul]
      simp only [hz, hθ, hx]
      simp
      ring
    rw [hratio]
    have := abs_le.1 hEre
    constructor <;> apply Real.exp_le_exp.2 <;> linarith
  have h1 : Tendsto (fun t => Real.exp (A t - |C| / t)) atTop (𝓝 1) := by
    simpa using (hAlim.sub hCt).rexp
  have h2 : Tendsto (fun t => Real.exp (A t + |C| / t)) atTop (𝓝 1) := by
    simpa using (hAlim.add hCt).rexp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (hbound.mono fun _ h => h.1)
    (hbound.mono fun _ h => h.2)

/-- On vertical lines, `‖Γ(σ₁ + iu)‖ ≤ 3 |u| ^ (σ₁ - σ₂) ‖Γ(σ₂ + iu)‖` for large `|u|`. -/
theorem exists_norm_Gamma_vertical_le_mul_rpow (σ1 σ2 : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ u : ℝ, R ≤ |u| →
      ‖Gamma (σ1 + u * I)‖ ≤ 3 * |u| ^ (σ1 - σ2) * ‖Gamma (σ2 + u * I)‖ := by
  have h1 := (norm_Gamma_vertical_isEquivalent σ1).isLittleO.bound (c := 1/2) (by norm_num)
  have h2 := (norm_Gamma_vertical_isEquivalent σ2).isLittleO.bound (c := 1/2) (by norm_num)
  have h := h1.and h2
  rw [eventually_comap, eventually_atTop] at h
  obtain ⟨R0, hR0⟩ := h
  refine ⟨max R0 1, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨hA, hB⟩ := hR0 |u| (le_trans (le_max_left _ _) hu) u rfl
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hA hB
  have hu1 : 1 ≤ |u| := le_trans (le_max_right _ _) hu
  have hu0 : 0 < |u| := by linarith
  set g1 := Real.exp (-(Real.pi * |u|) / 2) * |u| ^ (σ1 - 1 / 2) * Real.sqrt (2 * Real.pi)
  set g2 := Real.exp (-(Real.pi * |u|) / 2) * |u| ^ (σ2 - 1 / 2) * Real.sqrt (2 * Real.pi)
  have hg2 : 0 ≤ g2 := by positivity
  have hg : g1 = |u| ^ (σ1 - σ2) * g2 := by
    simp only [g1, g2]
    rw [show σ1 - 1/2 = (σ1 - σ2) + (σ2 - 1/2) by ring, Real.rpow_add hu0]
    ring
  rw [abs_of_nonneg hg2] at hB
  have hg1 : 0 ≤ g1 := by positivity
  rw [abs_of_nonneg hg1] at hA
  have hA' := (abs_le.1 hA).2
  have hB' := (abs_le.1 hB).1
  have hp : 0 ≤ |u| ^ (σ1 - σ2) := by positivity
  rw [hg] at hA'
  nlinarith [mul_le_mul_of_nonneg_left hB' hp]

/-- The ratio of a Gamma factor `Γ(α s + r)` between the lines `Re s = 2` and `Re s = -1` grows
at most like `|t| ^ (3α)`:
`‖Γ(α(2 + it) + r)‖ ‖Γ(α(-1 + it) + r)⁻¹‖ = O(|t| ^ (3α))`. -/
theorem exists_norm_Gamma_line_two_mul_inv_line_neg_one_le (α : ℝ) (hα : 0 < α) (r : ℂ) :
    ∃ M T : ℝ, 0 ≤ M ∧ ∀ t : ℝ, T ≤ |t| →
      ‖Gamma (α * (2 + t * I) + r)‖ * ‖(Gamma (α * (-1 + t * I) + r))⁻¹‖ ≤
        M * |t| ^ (3 * α) := by
  obtain ⟨R, hR1, hR⟩ := exists_norm_Gamma_vertical_le_mul_rpow (2 * α + r.re) (-α + r.re)
  have hK : 0 < α + |r.im| := by positivity
  refine ⟨3 * (α + |r.im|) ^ (3 * α), max 1 ((R + |r.im|) / α),
    by positivity, fun t ht => ?_⟩
  have hb : (α : ℂ) * (2 + t * I) + r =
      ((2 * α + r.re : ℝ) : ℂ) + ((α * t + r.im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp; ring
    · simp
  have hc : (α : ℂ) * (-1 + t * I) + r =
      ((-α + r.re : ℝ) : ℂ) + ((α * t + r.im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
  rw [hb, hc]
  have htR : (R + |r.im|) / α ≤ |t| := le_trans (le_max_right _ _) ht
  rw [div_le_iff₀ hα] at htR
  have hat : |α * t| = α * |t| := by rw [abs_mul, abs_of_pos hα]
  have hu_ge : R ≤ |α * t + r.im| := by
    have := abs_add_le (α * t + r.im) (-r.im)
    rw [abs_neg, add_neg_cancel_right, hat] at this
    linarith
  have hu_le : |α * t + r.im| ≤ (α + |r.im|) * |t| := by
    have ht1 : 1 ≤ |t| := le_trans (le_max_left _ _) ht
    calc |α * t + r.im| ≤ |α * t| + |r.im| := abs_add_le _ _
      _ ≤ (α + |r.im|) * |t| := by
        rw [hat]; nlinarith [abs_nonneg r.im]
  have key := hR _ hu_ge
  rw [show 2 * α + r.re - (-α + r.re) = 3 * α by ring] at key
  set g := Gamma (((-α + r.re : ℝ) : ℂ) + ((α * t + r.im : ℝ) : ℂ) * I)
  have hgg : ‖g‖ * ‖g⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    by_cases h : ‖g‖ = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h]
  have hpow : |α * t + r.im| ^ (3 * α) ≤ (α + |r.im|) ^ (3 * α) * |t| ^ (3 * α) := by
    rw [← Real.mul_rpow hK.le (abs_nonneg _)]
    exact Real.rpow_le_rpow (abs_nonneg _) hu_le (by positivity)
  have hp0 : 0 ≤ |α * t + r.im| ^ (3 * α) := by positivity
  calc _ ≤ 3 * |α * t + r.im| ^ (3 * α) * ‖g‖ * ‖g⁻¹‖ :=
        mul_le_mul_of_nonneg_right key (norm_nonneg _)
    _ ≤ 3 * |α * t + r.im| ^ (3 * α) := by
        rw [mul_assoc]; exact mul_le_of_le_one_right (by positivity) hgg
    _ ≤ 3 * ((α + |r.im|) ^ (3 * α) * |t| ^ (3 * α)) := by gcongr
    _ = _ := by ring

end Complex
