/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredPartitionsJensen.MajorArcIntegral

/-!
# The circle-method assembly for `C_r(n)`

With `A = rπ²/6`, `m = n − r/24`, `y = √(A/m)` (the saddle), the Cauchy integral of `CircleMethod`
(`coef_eq_integral`) is split at `|θ| = y`:

* **major arc** `|θ| ≤ y`: `EtaTransform` cone bound (`partGen_cone`, `M = 1`) writes the integrand
as
  `(2π)^{−r/2} τ^{r/2} e^{A/τ + mτ} (1 + E)^r` (`major_pt`, using `tau_div_cpow` for the power),
with
  `‖E‖ ≤ 4e^{−2π²/y}`; the main part is `(2π)^{−r/2} I_y(−r/2)` (`MajorArcIntegral` `iArc`);
* **minor arcs** `y ≤ |θ| ≤ π`: `CircleMethod` `minorArc_pow` and `EtaTransform` `partGen_real`
bound the integrand by
  `e^{A/y + my + r − r/(8y)}` (`minor_pt`);
* **main term**: `MajorArcIntegral` `norm_iArc_sub_sSer_saddle` and `MajorArc` `bT_neg_half_eq`,
`abs_bH_le`.

`coef_sub_main_le` is the explicit absolute bound; `coef_asymp` is the asymptotic formula:

  `C_r(n) = c'_r · besselInt((r+1)/2, κ_r √(n − r/24)) · (1 + ρ(n))`,   `‖ρ(n)‖ ≤ e^{−c√n}`
eventually,

with `c'_r = (2π)^{−r/2} A^{r/2+1} / (M₀((r+1)/2) Γ(r/2+2)) > 0` (`cPrime`), `κ_r = coloredKappa r`.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Nat

namespace MetaMathlibExt.ColoredPartitionsJensen

@[expose] public section

noncomputable section

/-- `A = rπ²/6`. -/
def cA (r : ℕ) : ℝ := r * Real.pi ^ 2 / 6

/-- `c'_r = (2π)^{−r/2} A^{r/2+1} / (M₀((r+1)/2) Γ(r/2+2))`. -/
def cPrime (r : ℕ) : ℝ :=
  (2 * Real.pi) ^ (-((r : ℝ) / 2)) * cA r ^ ((r : ℝ) / 2 + 1) /
    (bMom (((r : ℝ) + 1) / 2) 0 * Real.Gamma ((r : ℝ) / 2 + 2))

theorem cA_pos {r : ℕ} (hr : 1 ≤ r) : 0 < cA r := by
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold cA; have := Real.pi_pos; positivity

theorem cPrime_pos {r : ℕ} (hr : 1 ≤ r) : 0 < cPrime r := by
  have hA := cA_pos hr
  have hM := bMom_zero_pos (a := ((r : ℝ) + 1) / 2) (by positivity)
  have hG : 0 < Real.Gamma ((r : ℝ) / 2 + 2) := Real.Gamma_pos_of_pos (by positivity)
  unfold cPrime; have := Real.pi_pos; positivity

/-! ### The power `(τ/2π)^{r/2}` -/

theorem cpow_mul_ofReal_pos {c : ℝ} (hc : 0 < c) {τ : ℂ} (hτ : τ ≠ 0) (w : ℂ) :
    (τ * (c : ℂ)) ^ w = τ ^ w * (c : ℂ) ^ w := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hτ hc'), log_mul_ofReal c hc τ hτ, cpow_def_of_ne_zero hc',
    cpow_def_of_ne_zero hτ, ← Complex.exp_add, ofReal_log hc.le]
  ring_nf

/-- `(τ/2π)^{r/2} = (2π)^{−r/2} τ^{−(−r/2)}` (principal powers, `τ ≠ 0`). -/
theorem tau_div_cpow {τ : ℂ} (hτ : τ ≠ 0) (r : ℕ) :
    (τ / (2 * Real.pi)) ^ ((r : ℂ) / 2) =
      (((2 * Real.pi) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) * τ ^ (-(((-((r : ℝ) / 2)) : ℝ) : ℂ)) := by
  have h2π : (0 : ℝ) < (2 * Real.pi)⁻¹ := by have := Real.pi_pos; positivity
  rw [show τ / (2 * Real.pi) = τ * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) by push_cast; ring,
    cpow_mul_ofReal_pos h2π hτ, show ((r : ℂ) / 2) = (((r : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow h2π.le, Real.inv_rpow (by have := Real.pi_pos; positivity),
    ← Real.rpow_neg (by have := Real.pi_pos; positivity), mul_comm]
  congr 2
  push_cast; ring

/-! ### Pointwise bounds -/

theorem tauL_re' (y θ : ℝ) : (tauL y θ).re = y := by simp [tauL]

theorem tauL_im' (y θ : ℝ) : (tauL y θ).im = θ := by simp [tauL]

/-- **Major arc, pointwise.** For `0 < y ≤ 1`, `|θ| ≤ y`:
`F(e^{−τ})^r e^{nτ} = (2π)^{−r/2} v_{−r/2}(θ) (1 + E)^r`, `‖E‖ ≤ 4e^{−2π²/y}`, with `A = rπ²/6`,
`m = n − r/24`. -/
theorem major_pt (r n : ℕ) {y θ : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hθ : |θ| ≤ y) :
    ∃ E : ℂ, ‖E‖ ≤ 4 * Real.exp (-(2 * Real.pi ^ 2 / y)) ∧
      partGen (cexp (-tauL y θ)) ^ r * cexp (n * tauL y θ) =
        (((2 * Real.pi) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) *
          vInt (cA r) ((n : ℝ) - r / 24) y (-((r : ℝ) / 2)) θ * (1 + E) ^ r := by
  have hπ := Real.pi_pos
  have hτ := tauL_ne_zero hy θ
  obtain ⟨E, hE, hF⟩ := partGen_cone (M := 1) (τ := tauL y θ) (by rw [tauL_re']; exact hy)
    (by rw [tauL_re', tauL_im', one_mul]; exact hθ)
    (by
      rw [tauL_re', le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three])
  refine ⟨E, ?_, ?_⟩
  · refine hE.trans (le_of_eq ?_)
    rw [tauL_re']
    congr 2
    field_simp
    ring
  · rw [partGen_pow_eq r hF, vInt, tau_div_cpow hτ]
    have hexp : cexp (r * (Real.pi ^ 2 / (6 * tauL y θ) - tauL y θ / 24)) * cexp (n * tauL y θ) =
        cexp ((cA r : ℂ) / tauL y θ + (((n : ℝ) - r / 24 : ℝ) : ℂ) * tauL y θ) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [cA]
      push_cast
      field_simp
      ring
    rw [← hexp]
    ring

/-- `‖(1+E)^r − 1‖ ≤ r 2^r ‖E‖` for `‖E‖ ≤ 1`. -/
theorem norm_one_add_pow_sub_one_le {E : ℂ} (hE : ‖E‖ ≤ 1) (r : ℕ) :
    ‖(1 + E) ^ r - 1‖ ≤ r * 2 ^ r * ‖E‖ := by
  have h := geom_sum_mul (1 + E) r
  rw [add_sub_cancel_left] at h
  rw [← h, norm_mul]
  gcongr
  calc ‖∑ i ∈ Finset.range r, (1 + E) ^ i‖ ≤ ∑ i ∈ Finset.range r, ‖(1 + E) ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range r, (2 : ℝ) ^ r := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_pow]
        have h1 : ‖1 + E‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
        calc ‖1 + E‖ ^ i ≤ 2 ^ i := pow_le_pow_left₀ (norm_nonneg _) h1 i
          _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le
    _ = r * 2 ^ r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem exp_neg_le_quarter {x : ℝ} (hx : 2 ≤ x) : 4 * Real.exp (-x) ≤ 1 := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have h2 : 4 ≤ Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith
  have h1 : Real.exp (-x) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-2) ≤ 1 / 4 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]; linarith
  linarith

theorem norm_tauL_le {y θ : ℝ} (hy : 0 < y) (hθ : |θ| ≤ y) : ‖tauL y θ‖ ≤ √2 * y := by
  have h2 : √2 * y = √(2 * y ^ 2) := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hy.le]
  rw [norm_tauL, h2]
  refine Real.sqrt_le_sqrt ?_
  have : θ ^ 2 ≤ y ^ 2 := by
    rw [← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  linarith

/-- **Major arc error, pointwise**:
`‖integrand − (2π)^{−r/2} v‖ ≤ (2π)^{−r/2} (√2y)^{r/2} e^{A/y + my} r 2^r 4e^{−2π²/y}`. -/
theorem major_err_pt (r n : ℕ) {y θ : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hθ : |θ| ≤ y) :
    ‖partGen (cexp (-tauL y θ)) ^ r * cexp (n * tauL y θ) -
        (((2 * Real.pi) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) * vInt (cA r) ((n : ℝ) - r / 24) y (-((r : ℝ)
            / 2)) θ‖ ≤
      (2 * Real.pi) ^ (-((r : ℝ) / 2)) * ((√2 * y) ^ ((r : ℝ) / 2) *
        Real.exp (cA r / y + ((n : ℝ) - r / 24) * y)) * (r * 2 ^ r * (4 * Real.exp (-(2 * Real.pi ^
            2 / y)))) := by
  have hπ := Real.pi_pos
  obtain ⟨E, hE, hEq⟩ := major_pt r n hy hy1 hθ
  have hE1 : ‖E‖ ≤ 1 := hE.trans (exp_neg_le_quarter (by
    rw [le_div_iff₀ hy]; nlinarith [Real.pi_gt_three]))
  rw [hEq, show ∀ a b c : ℂ, a * b * c - a * b = a * b * (c - 1) from fun a b c => by ring,
      norm_mul, norm_mul,
    norm_real, Real.norm_of_nonneg (by positivity)]
  have hA : 0 ≤ cA r := by unfold cA; positivity
  have hv : ‖vInt (cA r) ((n : ℝ) - r / 24) y (-((r : ℝ) / 2)) θ‖ ≤
      (√2 * y) ^ ((r : ℝ) / 2) * Real.exp (cA r / y + ((n : ℝ) - r / 24) * y) := by
    refine (norm_vInt_le _ _ hy _ θ).trans ?_
    rw [neg_neg, abs_of_nonneg hA]
    gcongr
    exact norm_tauL_le hy hθ
  gcongr
  exact (norm_one_add_pow_sub_one_le hE1 r).trans (by gcongr)

/-- **Minor arcs, pointwise**: for `0 < y ≤ 1/2`, `y ≤ |θ| ≤ π`,
`‖F(e^{−τ})^r e^{nτ}‖ ≤ e^{A/y + my + r − r/(8y)}`. -/
theorem minor_pt (r n : ℕ) {y θ : ℝ} (hy : 0 < y) (hy2 : y ≤ 1 / 2) (hθ1 : y ≤ |θ|) (hθ2 : |θ| ≤
    Real.pi) :
    ‖partGen (cexp (-tauL y θ)) ^ r * cexp (n * tauL y θ)‖ ≤
      Real.exp (cA r / y + ((n : ℝ) - r / 24) * y + r - r / (8 * y)) := by
  have hπ := Real.pi_pos
  have hmin : ‖partGen (cexp (-tauL y θ)) ^ r‖ ≤
      ‖partGen (cexp (-(y : ℂ)))‖ ^ r * Real.exp (-(r / (8 * y))) := minorArc_pow r hy hy2 hθ1 hθ2
  obtain ⟨e, he, hFe⟩ := partGen_real hy (by linarith)
  have he1 : e ≤ 1 := by
    have h8 : 8 * Real.exp (-(4 * Real.pi ^ 2 / y)) ≤ 1 := by
      have h3 : Real.exp (-(4 * Real.pi ^ 2 / y)) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by
        have : 3 ≤ 4 * Real.pi ^ 2 / y := by rw [le_div_iff₀ hy]; nlinarith [Real.pi_gt_three]
        linarith)
      have h8 : Real.exp (-3) ≤ 1 / 8 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]
        have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
        have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        calc ((1 : ℝ) / 8)⁻¹ = 2 ^ 3 := by norm_num
          _ ≤ Real.exp 1 ^ 3 := by gcongr
      linarith
    linarith [(abs_le.1 he).2]
  have hlog : Real.log (y / (2 * Real.pi)) ≤ 0 :=
    Real.log_nonpos (by positivity)
      (by rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three])
  have hF : ‖partGen (cexp (-(y : ℂ)))‖ ≤ Real.exp (Real.pi ^ 2 / (6 * y) - y / 24 + 1) := by
    rw [hFe, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [norm_mul]
  have hn : ‖cexp (n * tauL y θ)‖ = Real.exp (n * y) := by
    rw [Complex.norm_exp]; simp [tauL]
  rw [hn]
  calc ‖partGen (cexp (-tauL y θ)) ^ r‖ * Real.exp (n * y)
      ≤ (Real.exp (Real.pi ^ 2 / (6 * y) - y / 24 + 1) ^ r * Real.exp (-(r / (8 *
          y)))) * Real.exp (n * y) := by
        gcongr
        exact hmin.trans (by gcongr)
    _ = Real.exp (cA r / y + ((n : ℝ) - r / 24) * y + r - r / (8 * y)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        simp only [cA]
        field_simp
        ring

/-! ### The integrals -/

/-- The circle integrand at `τ = y + iθ`. -/
def circ (r n : ℕ) (y θ : ℝ) : ℂ := partGen (cexp (-tauL y θ)) ^ r * cexp (n * tauL y θ)

theorem continuous_circ (r n : ℕ) {y : ℝ} (hy : 0 < y) : Continuous (circ r n y) := by
  unfold circ
  refine Continuous.mul ?_ ((continuous_const.mul (continuous_tauL y)).cexp)
  have h := (differentiableOn_partGen_pow r).continuousOn
  exact h.comp_continuous ((continuous_tauL y).neg.cexp) fun θ => by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp, neg_re, tauL_re']
    exact Real.exp_lt_one_iff.2 (by linarith)

/-- `P_r(y)` of `MajorArcIntegral`. -/
def Pr (r : ℕ) (y : ℝ) : ℝ :=
  2 * (y ^ (-(1 : ℝ)) + y ^ (-(1 / 2 : ℝ))) + (y ^ (-(2 : ℝ)) + y ^ (-(3 / 2 : ℝ))) +
    ((r : ℝ) / 2 + 2) * ((√2 * y) ^ (-(2 : ℝ)) + (√2 * y) ^ (-(3 / 2 : ℝ)) + (√2 * y) ^ ((r : ℝ) /
        2))

/-- `P_r(y) ≤ (2r + 12) y^{−2}` for `0 < y ≤ 1/2`. -/
theorem Pr_le (r : ℕ) {y : ℝ} (hy : 0 < y) (hy2 : y ≤ 1 / 2) : Pr r y ≤ (2 * r + 12) * y ^ (-(2 :
    ℝ)) := by
  have hy1 : y ≤ 1 := by linarith
  have hs2 : √2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs1 : 1 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hx0 : 0 < √2 * y := by positivity
  have hx1 : √2 * y ≤ 1 := by nlinarith
  have hyx : y ≤ √2 * y := by nlinarith
  set Y := y ^ (-(2 : ℝ)) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by norm_num)
  have a1 : y ^ (-(1 : ℝ)) ≤ Y := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by norm_num)
  have a2 : y ^ (-(1 / 2 : ℝ)) ≤ Y := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by norm_num)
  have a3 : y ^ (-(3 / 2 : ℝ)) ≤ Y := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by norm_num)
  have b1 : (√2 * y) ^ (-(2 : ℝ)) ≤ Y := Real.rpow_le_rpow_of_nonpos hy hyx (by norm_num)
  have b2 : (√2 * y) ^ (-(3 / 2 : ℝ)) ≤ Y :=
    (Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by norm_num : (-(2 : ℝ)) ≤ -(3 / 2))).trans b1
  have b3 : (√2 * y) ^ ((r : ℝ) / 2) ≤ Y := (Real.rpow_le_one hx0.le hx1 (by positivity)).trans hY1
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  unfold Pr
  rw [← hY]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add (add_le_add b1 b2) b3)
      (by positivity : (0 : ℝ) ≤ (r : ℝ) / 2 + 2)]

/-- At the saddle, `A/y + my = 2√(Am)`. -/
theorem saddle_exp_two {A m : ℝ} (hA : 0 < A) (hm : 0 < m) :
    A / √(A / m) + m * √(A / m) = 2 * √(A * m) := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ A = a ^ 2 := ⟨√A, Real.sqrt_pos.2 hA, (Real.sq_sqrt
      hA.le).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ m = b ^ 2 := ⟨√m, Real.sqrt_pos.2 hm, (Real.sq_sqrt
      hm.le).symm⟩
  rw [show a ^ 2 / b ^ 2 = (a / b) ^ 2 by ring, show a ^ 2 * b ^ 2 = (a * b) ^ 2 by ring,
    Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- The series at `s = −r/2` is the main term plus the reflection defect:
`(2π)^{−r/2} S(−r/2, m) = c'_r besselInt((r+1)/2, 2√(Am)) + (2π)^{−r/2} m^{−r/2−1} bH(r/2+1, Am)`.
-/
theorem sSer_neg_half_eq (r : ℕ) (hr : 1 ≤ r) {m : ℝ} (hm : 0 < m) :
    (2 * Real.pi) ^ (-((r : ℝ) / 2)) * sSer (cA r) m (-((r : ℝ) / 2)) =
      cPrime r * besselInt (((r : ℝ) + 1) / 2) (2 * √(cA r * m)) +
        (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (m ^ (-((r : ℝ) / 2) - 1) * bH ((r : ℝ) / 2 + 1) (cA r *
            m)) := by
  have hA := cA_pos hr
  have hM := bMom_zero_pos (a := ((r : ℝ) + 1) / 2) (by positivity)
  have hG : 0 < Real.Gamma ((r : ℝ) / 2 + 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [sSer, bT_neg_half_eq r (by positivity), Real.mul_rpow hA.le hm.le]
  have hmm : m ^ (-((r : ℝ) / 2) - 1) * m ^ ((r : ℝ) / 2 + 1) = 1 := by
    rw [← Real.rpow_add hm]; norm_num
  set B := besselInt (((r : ℝ) + 1) / 2) (2 * √(cA r * m))
  set D := bMom (((r : ℝ) + 1) / 2) 0 * Real.Gamma ((r : ℝ) / 2 + 2)
  have e : m ^ (-((r : ℝ) / 2) - 1) * (cA r ^ ((r : ℝ) / 2 + 1) * m ^ ((r : ℝ) / 2 + 1) * B / D) =
      cA r ^ ((r : ℝ) / 2 + 1) * B / D := by
    rw [show m ^ (-((r : ℝ) / 2) - 1) * (cA r ^ ((r : ℝ) / 2 + 1) * m ^ ((r : ℝ) / 2 + 1) * B / D) =
      (m ^ (-((r : ℝ) / 2) - 1) * m ^ ((r : ℝ) / 2 + 1)) * (cA r ^ ((r : ℝ) / 2 + 1) * B /
          D) by ring, hmm, one_mul]
  rw [mul_add, e]
  unfold cPrime
  ring

/-- **The assembly, absolute form.** For `r ≥ 1`, `m = n − r/24` with `m ≥ A + r/2 + 2`, `m ≥ 4A`,
`Am ≥ 1`
(`A = rπ²/6`, `y = √(A/m)`, `K = (2π)^{−r/2}`):
`‖C_r(n) − c'_r besselInt((r+1)/2,
    2√(Am))‖ ≤ K e^{(3/2)√(Am)} P_r(y)/π + K m^{−r/2−1}(r+2)!(Am+1)^{r+1}e^{−2√(Am)}
  + (2π)⁻¹ K (√2y)^{r/2} e^{2√(Am)} r 2^r 4e^{−2π²/y} · 2y + e^{2√(Am) + r − r/(8y)}`. -/
theorem coef_sub_main_le (r n : ℕ) (hr : 1 ≤ r) (hm : cA r + r / 2 + 2 ≤ (n : ℝ) - r / 24)
    (hm4 : 4 * cA r ≤ (n : ℝ) - r / 24) (hAm : 1 ≤ cA r * ((n : ℝ) - r / 24)) :
    ‖coef r n - ((cPrime r * besselInt (((r : ℝ) + 1) / 2) (2 * √(cA r * ((n : ℝ) - r / 24))) : ℝ)
        : ℂ)‖ ≤
      (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (Real.exp (3 / 2 * √(cA r * ((n : ℝ) - r / 24))) / Real.pi
          *
          Pr r (√(cA r / ((n : ℝ) - r / 24)))) +
        (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (((n : ℝ) - r / 24) ^ (-((r : ℝ) / 2) - 1) *
          ((r + 2)! * (cA r * ((n : ℝ) - r / 24) + 1) ^ (r + 1) *
            Real.exp (-(2 * √(cA r * ((n : ℝ) - r / 24)))))) +
        (2 * Real.pi)⁻¹ * ((2 * Real.pi) ^ (-((r : ℝ) / 2)) *
          ((√2 * √(cA r / ((n : ℝ) - r / 24))) ^ ((r : ℝ) / 2) * Real.exp (2 * √(cA r * ((n : ℝ) -
              r / 24)))) *
          (r * 2 ^ r * (4 * Real.exp (-(2 * Real.pi ^ 2 / √(cA r / ((n : ℝ) - r / 24)))))) *
          (2 * √(cA r / ((n : ℝ) - r / 24)))) +
        Real.exp (2 * √(cA r * ((n : ℝ) - r / 24)) + r - r / (8 * √(cA r / ((n : ℝ) - r /
            24)))) := by
  set m : ℝ := (n : ℝ) - r / 24 with hmdef
  set A := cA r with hAdef
  have hπ := Real.pi_pos
  have hA : 0 < A := cA_pos hr
  have hm0 : 0 < m := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  set y := √(A / m) with hydef
  have hy : 0 < y := Real.sqrt_pos.2 (div_pos hA hm0)
  have hy2 : y ≤ 1 / 2 := by
    rw [hydef, Real.sqrt_le_left (by norm_num), div_le_iff₀ hm0]; linarith
  have hy1 : y ≤ 1 := by linarith
  have hsad : A / y + m * y = 2 * √(A * m) := saddle_exp_two hA hm0
  set K : ℝ := (2 * Real.pi) ^ (-((r : ℝ) / 2)) with hK
  have hK0 : 0 < K := by positivity
  set v := vInt A m y (-((r : ℝ) / 2)) with hv
  have hc := continuous_circ r n hy
  have hvc : Continuous v := continuous_vInt A m hy _
  -- the split
  have hcoef : coef r n = (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, circ r n y θ := by
    rw [coef_eq_integral r n hy]; push_cast; rfl
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume)
      (-Real.pi) (-y))
    (hc.intervalIntegrable (μ := volume) (-y) y)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume)
      (-Real.pi) y)
    (hc.intervalIntegrable (μ := volume) y Real.pi)
  set I1 := ∫ θ in (-Real.pi)..(-y), circ r n y θ
  set I3 := ∫ θ in y..Real.pi, circ r n y θ
  set G := ∫ θ in (-y)..y, (circ r n y θ - (K : ℂ) * v θ) with hG
  have hGeq : G = (∫ θ in (-y)..y, circ r n y θ) - (K : ℂ) * ((2 * Real.pi : ℂ) * iArc A m y (-((r
      : ℝ) / 2))) := by
    rw [hG, intervalIntegral.integral_sub (f := circ r n y) (g := fun θ => (K : ℂ) * v θ)
        (hc.intervalIntegrable (μ := volume) _ _)
      ((continuous_const.mul hvc).intervalIntegrable (μ := volume) _
          _), intervalIntegral.integral_const_mul]
    unfold iArc
    have : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    rw [← mul_assoc (2 * (Real.pi : ℂ)), mul_inv_cancel₀ this, one_mul]
  have hser := sSer_neg_half_eq r hr hm0
  rw [← hAdef] at hser
  set B := besselInt (((r : ℝ) + 1) / 2) (2 * √(A * m))
  set H := m ^ (-((r : ℝ) / 2) - 1) * bH ((r : ℝ) / 2 + 1) (A * m)
  have hkey : coef r n - ((cPrime r * B : ℝ) : ℂ) =
      (K : ℂ) * (iArc A m y (-((r : ℝ) / 2)) - (sSer A m (-((r : ℝ) / 2)) : ℂ)) + ((K * H : ℝ) :
          ℂ) +
        (2 * Real.pi : ℂ)⁻¹ * G + (2 * Real.pi : ℂ)⁻¹ * (I1 + I3) := by
    have hser' : (K : ℂ) * (sSer A m (-((r : ℝ) / 2)) : ℂ) = ((cPrime r * B : ℝ) : ℂ) + ((K * H :
        ℝ) : ℂ) := by
      rw [← ofReal_mul, hser, ofReal_add]
    have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    rw [hcoef, ← h2, ← h1, hGeq]
    rw [← sub_eq_zero]
    field_simp
    linear_combination (2 * Real.pi : ℂ) * hser'
  rw [hkey]
  -- the four bounds
  have e1 : ‖(K : ℂ) * (iArc A m y (-((r : ℝ) / 2)) - (sSer A m (-((r : ℝ) / 2)) : ℂ))‖ ≤
      K * (Real.exp (3 / 2 * √(A * m)) / Real.pi * Pr r y) := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hK0.le]
    gcongr
    exact norm_iArc_sub_sSer_saddle r hA hm
  have e2 : ‖((K * H : ℝ) : ℂ)‖ ≤ K * (m ^ (-((r : ℝ) / 2) - 1) *
      ((r + 2)! * (A * m + 1) ^ (r + 1) * Real.exp (-(2 * √(A * m))))) := by
    rw [norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hK0, abs_mul, abs_of_pos
        (Real.rpow_pos_of_pos hm0 _)]
    gcongr
    exact abs_bH_le r hAm
  have e3 : ‖(2 * Real.pi : ℂ)⁻¹ * G‖ ≤ (2 * Real.pi)⁻¹ * (K * ((√2 * y) ^ ((r : ℝ) / 2) *
      Real.exp (2 * √(A * m))) * (r * 2 ^ r * (4 * Real.exp (-(2 * Real.pi ^ 2 / y)))) * (2 *
          y)) := by
    rw [norm_mul, norm_inv, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)]]
    gcongr
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -y) (b := y)
      (f := fun θ => circ r n y θ - (K : ℂ) * v θ)
      (C := K * ((√2 * y) ^ ((r : ℝ) / 2) * Real.exp (2 * √(A * m))) *
        (r * 2 ^ r * (4 * Real.exp (-(2 * Real.pi ^ 2 / y))))) (fun θ hθ => by
        rw [Set.uIoc_of_le (by linarith)] at hθ
        have h := major_err_pt r n hy hy1 (θ := θ) (abs_le.2 ⟨hθ.1.le, hθ.2⟩)
        rw [hsad] at h
        exact h)
    rw [show |y - -y| = 2 * y by rw [abs_of_pos (by linarith)]; ring] at hb
    exact hb
  have e4 : ‖(2 * Real.pi : ℂ)⁻¹ * (I1 + I3)‖ ≤ Real.exp (2 * √(A * m) + r - r / (8 * y)) := by
    set C := Real.exp (2 * √(A * m) + r - r / (8 * y))
    have hC : ∀ θ, y ≤ |θ| → |θ| ≤ Real.pi → ‖circ r n y θ‖ ≤ C := fun θ h1 h2 => by
      have := minor_pt r n hy hy2 h1 h2
      rw [hsad] at this
      exact this
    have b1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := -y) (C := C)
      (f := circ r n y) (fun θ hθ => by
        rw [Set.uIoc_of_le (by linarith [Real.pi_gt_three])] at hθ
        exact hC θ (by rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.2])
          (by rw [abs_of_neg (by linarith [hθ.2])]; linarith [hθ.1]))
    have b3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := Real.pi) (C := C)
      (f := circ r n y) (fun θ hθ => by
        rw [Set.uIoc_of_le (by linarith [Real.pi_gt_three])] at hθ
        exact hC θ (by rw [abs_of_pos (by linarith [hθ.1])]; exact hθ.1.le)
          (by rw [abs_of_pos (by linarith [hθ.1])]; exact hθ.2))
    rw [abs_of_pos (by linarith [Real.pi_gt_three])] at b1 b3
    rw [norm_mul, norm_inv, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)], inv_mul_le_iff₀ (by positivity)]
    have hC0 : 0 ≤ C := (Real.exp_pos _).le
    calc ‖I1 + I3‖ ≤ ‖I1‖ + ‖I3‖ := norm_add_le _ _
      _ ≤ C * (-y - -Real.pi) + C * (Real.pi - y) := add_le_add b1 b3
      _ ≤ 2 * Real.pi * C := by nlinarith
  calc _ ≤ ‖(K : ℂ) * (iArc A m y (-((r : ℝ) / 2)) - (sSer A m (-((r : ℝ) / 2)) : ℂ)) + ((K * H :
      ℝ) : ℂ) +
        (2 * Real.pi : ℂ)⁻¹ * G‖ + ‖(2 * Real.pi : ℂ)⁻¹ * (I1 + I3)‖ := norm_add_le _ _
    _ ≤ ‖(K : ℂ) * (iArc A m y (-((r : ℝ) / 2)) - (sSer A m (-((r : ℝ) / 2)) : ℂ)) + ((K * H : ℝ) :
        ℂ)‖ +
        ‖(2 * Real.pi : ℂ)⁻¹ * G‖ + ‖(2 * Real.pi : ℂ)⁻¹ * (I1 +
            I3)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
        have := norm_add_le ((K : ℂ) * (iArc A m y (-((r : ℝ) / 2)) - (sSer A m (-((r : ℝ) / 2)) :
            ℂ)))
          ((K * H : ℝ) : ℂ)
        linarith

/-! ### The eventual relative form -/

/-- `C tᵏ e^{−c₀t} ≤ e^{−ct}/4` eventually, for `c ≤ c₀/2`. -/
theorem ev_poly_exp (C : ℝ) (k : ℕ) {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc : c ≤ c₀ / 2) :
    ∀ᶠ t : ℝ in atTop, C * t ^ k * Real.exp (-(c₀ * t)) ≤ Real.exp (-(c * t)) / 4 := by
  have ho := isLittleO_pow_exp_pos_mul_atTop k (half_pos hc₀)
  have hε : (0 : ℝ) < 1 / (4 * (|C| + 1)) := by positivity
  filter_upwards [ho.bound hε, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 k), abs_of_pos
      (Real.exp_pos _)] at ht
  have h1 : C * t ^ k ≤ |C| * (1 / (4 * (|C| + 1)) * Real.exp (c₀ / 2 * t)) :=
    mul_le_mul (le_abs_self C) ht (pow_nonneg ht0 k) (abs_nonneg C)
  have h3 : |C| * (1 / (4 * (|C| + 1))) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [abs_nonneg C]
  have h4 : Real.exp (c₀ / 2 * t) * Real.exp (-(c₀ * t)) ≤ Real.exp (-(c * t)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
  calc C * t ^ k * Real.exp (-(c₀ * t))
      ≤ |C| * (1 / (4 * (|C| + 1)) * Real.exp (c₀ / 2 * t)) * Real.exp (-(c₀ * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (|C| * (1 / (4 * (|C| + 1)))) * (Real.exp (c₀ / 2 * t) * Real.exp (-(c₀ * t))) := by ring
    _ ≤ (1 / 4) * Real.exp (-(c * t)) := mul_le_mul h3 h4 (by positivity) (by norm_num)
    _ = Real.exp (-(c * t)) / 4 := by ring

/-- `κ_r √m = 2√(Am)`. -/
theorem coloredKappa_mul_sqrt (r : ℕ) {m : ℝ} (hm : 0 ≤ m) : coloredKappa r * √m = 2 * √(cA r *
    m) := by
  have hπ := Real.pi_pos
  rw [Real.sqrt_mul' _ hm]
  unfold coloredKappa cA
  have h1 : √((r : ℝ) * Real.pi ^ 2 / 6) = Real.pi * √((r : ℝ) / 6) := by
    rw [show (r : ℝ) * Real.pi ^ 2 / 6 = Real.pi ^ 2 * ((r : ℝ) / 6) by ring, Real.sqrt_mul
        (by positivity),
      Real.sqrt_sq hπ.le]
  have h2 : √(2 * (r : ℝ) / 3) = 2 * √((r : ℝ) / 6) := by
    rw [show 2 * (r : ℝ) / 3 = 2 ^ 2 * ((r : ℝ) / 6) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h1, h2]; ring

/-- Lower bound for the main term:
`c'_r besselInt((r+1)/2, z) ≥ c'_r e^{z−1} z^{−(r+2)}/((r+1)/2 + 1)`, `z ≥ 1`. -/
theorem main_lower (r : ℕ) (hr : 1 ≤ r) {z : ℝ} (hz : 1 ≤ z) :
    cPrime r * (Real.exp z / Real.exp 1 * ((z ^ (r + 2))⁻¹ / (((r : ℝ) + 1) / 2 + 1))) ≤
      cPrime r * besselInt (((r : ℝ) + 1) / 2) z := by
  have hz0 : 0 < z := by linarith
  refine mul_le_mul_of_nonneg_left ?_ (cPrime_pos hr).le
  refine le_trans ?_ (le_besselInt (by positivity) hz)
  rw [Real.exp_sub]
  gcongr
  rw [← inv_pow, ← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_ge (inv_pos.2 hz0) (inv_le_one_of_one_le₀ hz) ?_
  push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem term1_le (r : ℕ) {K P A a t : ℝ} (hK : 0 ≤ K) (hP : P ≤ (2 * r + 12) * (t ^ 2 / A)) :
    K * (Real.exp (3 / 2 * (a * t)) / Real.pi * P) ≤
      Real.exp (2 * a * t) * (K * (2 * r + 12) / (Real.pi * A) * t ^ 2 * Real.exp (-(a / 2 *
          t))) := by
  have hπ := Real.pi_pos
  calc K * (Real.exp (3 / 2 * (a * t)) / Real.pi * P)
      ≤ K * (Real.exp (3 / 2 * (a * t)) / Real.pi * ((2 * r + 12) * (t ^ 2 / A))) := by gcongr
    _ = _ := by
        rw [show 3 / 2 * (a * t) = 2 * a * t + -(a / 2 * t) by ring, Real.exp_add]
        ring

theorem term2_le (r : ℕ) {K A a t m : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hm1 : 1 ≤ m) (htm : t ^ 2 = m) :
    K * (m ^ (-((r : ℝ) / 2) - 1) * ((r + 2)! * (A * m + 1) ^ (r + 1) * Real.exp (-(2 * (a *
        t))))) ≤
      Real.exp (2 * a * t) * (K * (r + 2)! * (A + 1) ^ (r + 1) * t ^ (2 * r + 2) * Real.exp (-(4 *
          a * t))) := by
  have hp : m ^ (-((r : ℝ) / 2) - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by
    have := Nat.cast_nonneg (α := ℝ) r; linarith)
  have hq : A * m + 1 ≤ (A + 1) * t ^ 2 := by rw [htm]; nlinarith
  calc _ ≤ K * (1 * ((r + 2)! * ((A + 1) * t ^ 2) ^ (r + 1) * Real.exp (-(2 * (a * t))))) := by
        gcongr
    _ = _ := by
        rw [show -(2 * (a * t)) = 2 * a * t + -(4 * a * t) by ring, Real.exp_add, mul_pow, ←
            pow_mul]
        ring

theorem term3_le (r : ℕ) {K y a t : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (hy2 : y ≤ 1 / 2) (ha : 0 < a) (ht
    : 0 < t)
    (hyt : y = a / t) :
    (2 * Real.pi)⁻¹ * (K * ((√2 * y) ^ ((r : ℝ) / 2) * Real.exp (2 * (a * t))) *
        (r * 2 ^ r * (4 * Real.exp (-(2 * Real.pi ^ 2 / y)))) * (2 * y)) ≤
      Real.exp (2 * a * t) * ((2 * Real.pi)⁻¹ * K * (r * 2 ^ r * 4) * Real.exp (-(2 * Real.pi ^ 2 /
          a * t))) := by
  have hπ := Real.pi_pos
  have hs : (√2 * y) ^ ((r : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one (by positivity) ?_ (by positivity)
    have : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  have h2y : 2 * y ≤ 1 := by linarith
  have he : 2 * Real.pi ^ 2 / y = 2 * Real.pi ^ 2 / a * t := by rw [hyt]; field_simp
  rw [he]
  calc _ ≤ (2 * Real.pi)⁻¹ * (K * (1 * Real.exp (2 * (a * t))) *
        (r * 2 ^ r * (4 * Real.exp (-(2 * Real.pi ^ 2 / a * t)))) * 1) := by gcongr
    _ = _ := by ring_nf

theorem term4_eq (r : ℕ) {y a t : ℝ} (ha : 0 < a) (_ht : 0 < t) (hyt : y = a / t) :
    Real.exp (2 * (a * t) + r - r / (8 * y)) =
      Real.exp (2 * a * t) * (Real.exp r * Real.exp (-((r : ℝ) / (8 * a) * t))) := by
  rw [← Real.exp_add, ← Real.exp_add, hyt]; congr 1; field_simp; ring

theorem scale_le {C L e F t : ℝ} (j p : ℕ) (hL : 0 < L) (hE : C / L * t ^ (j + p) * e ≤ F / 4) :
    C * t ^ j * e * t ^ p ≤ L * (F / 4) := by
  have := mul_le_mul_of_nonneg_left hE hL.le
  calc C * t ^ j * e * t ^ p = L * (C / L * t ^ (j + p) * e) := by rw [pow_add]; field_simp
    _ ≤ _ := this

theorem main_lower' (r : ℕ) (hr : 1 ≤ r) {a t : ℝ} (ha : 0 < a) (_ht : 0 < t) (hz : 1 ≤ 2 * a * t) :
    cPrime r / (Real.exp 1 * (((r : ℝ) + 1) / 2 + 1) * (2 * a) ^ (r + 2)) * Real.exp (2 * a * t) ≤
      cPrime r * besselInt (((r : ℝ) + 1) / 2) (2 * a * t) * t ^ (r + 2) := by
  have hlow := main_lower r hr hz
  have htp : 0 < t ^ (r + 2) := by positivity
  have := mul_le_mul_of_nonneg_right hlow htp.le
  refine le_trans (le_of_eq ?_) this
  rw [mul_pow, mul_pow]
  field_simp
  ring

theorem sqrt_n_le {n : ℕ} {r : ℕ} (hn : (r : ℝ) ≤ n) : √(n : ℝ) / 2 ≤ √((n : ℝ) - r / 24) := by
  rw [show √(n : ℝ) / 2 = √((n : ℝ) / 4) by
    rw [Real.sqrt_div' _ (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq
        (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Absolute-relative form.** For `r ≥ 1` there is `c > 0` with, for all large `n`,
`‖C_r(n) − c'_r besselInt((r+1)/2, κ_r √(n − r/24))‖ ≤ c'_r besselInt(…) · e^{−c√n}`. -/
theorem coef_asymp_abs (r : ℕ) (hr : 1 ≤ r) : ∃ c > 0, ∀ᶠ n : ℕ in atTop,
    ‖coef r n - ((cPrime r * besselInt (((r : ℝ) + 1) / 2) (coloredKappa r * √((n : ℝ) - r / 24)) :
        ℝ) : ℂ)‖ ≤
      cPrime r * besselInt (((r : ℝ) + 1) / 2) (coloredKappa r * √((n : ℝ) - r /
          24)) * Real.exp (-(c * √n)) := by
  have hA : 0 < cA r := cA_pos hr
  have hπ := Real.pi_pos
  have ha : 0 < √(cA r) := Real.sqrt_pos.2 hA
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hK0 : 0 < (2 * Real.pi) ^ (-((r : ℝ) / 2)) := by positivity
  have hc' := cPrime_pos hr
  have hL : 0 < cPrime r / (Real.exp 1 * (((r : ℝ) + 1) / 2 + 1) * (2 * √(cA r)) ^ (r +
      2)) := by positivity
  set L := cPrime r / (Real.exp 1 * (((r : ℝ) + 1) / 2 + 1) * (2 * √(cA r)) ^ (r + 2)) with hLdef
  set c := min (min (√(cA r) / 2) (4 * √(cA r))) (min (2 * Real.pi ^ 2 / √(cA r)) ((r : ℝ) / (8 *
      √(cA r)))) / 2
    with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact half_pos (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity)
        (by positivity)))
  have hc1 : c ≤ √(cA r) / 2 / 2 := by
    have := min_le_left (min (√(cA r) / 2) (4 * √(cA r))) (min (2 * Real.pi ^ 2 / √(cA r)) ((r : ℝ)
        / (8 * √(cA r))))
    have := min_le_left (√(cA r) / 2) (4 * √(cA r)); rw [hcdef]; linarith
  have hc2 : c ≤ 4 * √(cA r) / 2 := by
    have := min_le_left (min (√(cA r) / 2) (4 * √(cA r))) (min (2 * Real.pi ^ 2 / √(cA r)) ((r : ℝ)
        / (8 * √(cA r))))
    have := min_le_right (√(cA r) / 2) (4 * √(cA r)); rw [hcdef]; linarith
  have hc3 : c ≤ 2 * Real.pi ^ 2 / √(cA r) / 2 := by
    have := min_le_right (min (√(cA r) / 2) (4 * √(cA r))) (min (2 * Real.pi ^ 2 / √(cA r)) ((r :
        ℝ) / (8 * √(cA r))))
    have := min_le_left (2 * Real.pi ^ 2 / √(cA r)) ((r : ℝ) / (8 * √(cA r))); rw [hcdef]; linarith
  have hc4 : c ≤ (r : ℝ) / (8 * √(cA r)) / 2 := by
    have := min_le_right (min (√(cA r) / 2) (4 * √(cA r))) (min (2 * Real.pi ^ 2 / √(cA r)) ((r :
        ℝ) / (8 * √(cA r))))
    have := min_le_right (2 * Real.pi ^ 2 / √(cA r)) ((r : ℝ) / (8 * √(cA r))); rw [hcdef]; linarith
  refine ⟨c / 2, half_pos hcpos, ?_⟩
  have E1 := ev_poly_exp ((2 * Real.pi) ^ (-((r : ℝ) / 2)) * (2 * r + 12) / (Real.pi * cA r) /
      L) (2 + (r + 2))
    (by positivity : 0 < √(cA r) / 2) hc1
  have E2 := ev_poly_exp ((2 * Real.pi) ^ (-((r : ℝ) / 2)) * (r + 2)! * (cA r + 1) ^ (r + 1) /
      L) (2 * r + 2 + (r + 2))
    (by positivity : 0 < 4 * √(cA r)) hc2
  have E3 := ev_poly_exp ((2 * Real.pi)⁻¹ * (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (r * 2 ^ r * 4) /
      L) (0 + (r + 2))
    (by positivity : 0 < 2 * Real.pi ^ 2 / √(cA r)) hc3
  have E4 := ev_poly_exp (Real.exp r / L) (0 + (r +
      2)) (by positivity : 0 < (r : ℝ) / (8 * √(cA r))) hc4
  set T0 : ℝ := 1 + 1 / (2 * √(cA r)) + (cA r + r / 2 + 2 + 4 * cA r + 1 / cA r) with hT0
  have hT : Tendsto (fun n : ℕ => √((n : ℝ) - r / 24)) atTop atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-((r : ℝ) /
        24)) tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually E1, hT.eventually E2, hT.eventually E3, hT.eventually E4,
    hT.eventually (eventually_ge_atTop T0), eventually_ge_atTop r] with n h1 h2 h3 h4 h5 hn
  set m : ℝ := (n : ℝ) - r / 24 with hmdef
  set t := √m with htdef
  have hnr : (r : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have htm : t ^ 2 = m := Real.sq_sqrt hm0.le
  have ht1 : 1 ≤ t := by
    have : 0 < 1 / (2 * √(cA r)) := by positivity
    have : 0 < 1 / cA r := by positivity
    linarith
  have ht0 : 0 < t := by linarith
  have htS : cA r + r / 2 + 2 + 4 * cA r + 1 / cA r ≤ m := by
    have : 0 < 1 / (2 * √(cA r)) := by positivity
    nlinarith
  have hm : cA r + r / 2 + 2 ≤ m := by
    have : 0 < 1 / cA r := (by positivity)
    linarith
  have hm4 : 4 * cA r ≤ m := by
    have : 0 < 1 / cA r := (by positivity)
    linarith
  have hAm : 1 ≤ cA r * m := by
    have h := mul_le_mul_of_nonneg_left (show 1 / cA r ≤ m by linarith) hA.le
    rwa [mul_one_div_cancel hA.ne'] at h
  have hz : 1 ≤ 2 * √(cA r) * t := by
    have h := mul_le_mul_of_nonneg_left (show 1 / (2 * √(cA r)) ≤ t by
      have : 0 < 1 / cA r := by positivity
      linarith) (by positivity : (0 : ℝ) ≤ 2 * √(cA r))
    rwa [mul_one_div_cancel (by positivity)] at h
  have hsAm : √(cA r * m) = √(cA r) * t := Real.sqrt_mul hA.le m
  have hsAdm : √(cA r / m) = √(cA r) / t := Real.sqrt_div hA.le m
  have hm1 : 1 ≤ m := by nlinarith
  rw [coloredKappa_mul_sqrt r hm0.le]
  have hb := coef_sub_main_le r n hr hm hm4 hAm
  rw [← hmdef] at hb
  -- the four terms, each `≤ e^{2√A t} D tʲ e^{−c₀ t}`
  set a := √(cA r) with hadef
  have haa : a ^ 2 = cA r := Real.sq_sqrt hA.le
  set y := √(cA r / m) with hydef
  have hy0 : 0 < y := Real.sqrt_pos.2 (div_pos hA hm0)
  have hy2 : y ≤ 1 / 2 := by
    rw [hydef, Real.sqrt_le_left (by norm_num), div_le_iff₀ hm0]; linarith
  have hyt : y = a / t := hsAdm
  have hY : y ^ (-(2 : ℝ)) = t ^ 2 / cA r := by
    rw [Real.rpow_neg hy0.le, Real.rpow_two, hyt, div_pow, haa]; field_simp
  rw [hsAm] at hb
  have hK0' := hK0.le
  have b1 := term1_le r (A := cA r) (a := a) (t := t) hK0' (Pr_le r hy0 hy2 |>.trans (le_of_eq
      (by rw [hY])))
  have b2 := term2_le r (A := cA r) (a := a) hK0' hA.le hm1 htm
  have b3 := term3_le r (a := a) hK0' hy0 hy2 (by positivity) ht0 hyt
  have b4 := term4_eq r (y := y) (by positivity : 0 < a) ht0 hyt
  have hsum := hb.trans (add_le_add (add_le_add (add_le_add b1 b2) b3) b4.le)
  -- the decay
  have hlow := main_lower r hr hz
  rw [show 2 * (a * t) = 2 * a * t by ring] at hsum
  rw [hsAm, show 2 * (a * t) = 2 * a * t by ring]
  have k1 := h1; have k2 := h2; have k3 := h3; have k4 := h4
  set F := Real.exp (-(c * t))
  have hF : 0 < F := Real.exp_pos _
  have q1 := scale_le 2 (r + 2) hL k1
  have q2 := scale_le (2 * r + 2) (r + 2) hL k2
  have q3 := scale_le 0 (r + 2) hL k3
  have q4 := scale_le 0 (r + 2) hL k4
  simp only [pow_zero, mul_one] at q3 q4
  have htp : 0 < t ^ (r + 2) := by positivity
  have hdec : F ≤ Real.exp (-(c / 2 * √n)) := by
    refine Real.exp_le_exp.2 ?_
    have hsq := sqrt_n_le (r := r) hnr
    rw [← htdef] at hsq
    have := mul_le_mul_of_nonneg_left hsq hcpos.le
    linarith
  set S := (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (2 * r + 12) / (Real.pi * cA
      r) * t ^ 2 * Real.exp (-(a / 2 * t)) +
      (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (r + 2)! * (cA r + 1) ^ (r + 1) * t ^ (2 * r +
          2) * Real.exp (-(4 * a * t)) +
      (2 * Real.pi)⁻¹ * (2 * Real.pi) ^ (-((r : ℝ) / 2)) * (r * 2 ^ r * 4) * Real.exp (-(2 *
          Real.pi ^ 2 / a * t)) +
      Real.exp r * Real.exp (-((r : ℝ) / (8 * a) * t))
  have hlow' := main_lower' r hr (by positivity : 0 < a) ht0 hz
  have hsmall : S * t ^ (r + 2) ≤ L * F := by
    simp only [S]
    rw [add_mul, add_mul, add_mul]
    linarith
  have hB : 0 ≤ cPrime r * besselInt (((r : ℝ) + 1) / 2) (2 * a * t) :=
    (mul_pos hc' (besselInt_pos (by positivity) _)).le
  calc _ ≤ Real.exp (2 * a * t) * S := by
        refine hsum.trans (le_of_eq ?_); simp only [S]; ring
    _ ≤ cPrime r * besselInt (((r : ℝ) + 1) / 2) (2 * a * t) * F := by
        rw [← mul_le_mul_iff_of_pos_right htp]
        calc Real.exp (2 * a * t) * S * t ^ (r + 2) = Real.exp (2 * a * t) * (S * t ^ (r +
            2)) := by ring
          _ ≤ Real.exp (2 * a * t) * (L * F) := by gcongr
          _ = L * Real.exp (2 * a * t) * F := by ring
          _ ≤ cPrime r * besselInt (((r : ℝ) + 1) / 2) (2 * a * t) * t ^ (r + 2) * F := by gcongr
          _ = _ := by ring
    _ ≤ _ := by gcongr

/-- **Asymptotic formula.** For `r ≥ 1` there is `c > 0` such that for all large `n`,
`C_r(n) = c'_r · besselInt((r+1)/2, κ_r √(n − r/24)) · (1 + ρ(n))` with `‖ρ(n)‖ ≤ e^{−c√n}`
(`c'_r > 0`: `cPrime_pos`). -/
theorem coef_asymp (r : ℕ) (hr : 1 ≤ r) : ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ ρ : ℂ,
    ‖ρ‖ ≤ Real.exp (-(c * √n)) ∧
      coef r n = ((cPrime r * besselInt (((r : ℝ) + 1) / 2) (coloredKappa r * √((n : ℝ) - r / 24))
          : ℝ) : ℂ) * (1 + ρ) := by
  obtain ⟨c, hc, hev⟩ := coef_asymp_abs r hr
  refine ⟨c, hc, hev.mono fun n hn => ?_⟩
  set M := cPrime r * besselInt (((r : ℝ) + 1) / 2) (coloredKappa r * √((n : ℝ) - r / 24))
  have hM : 0 < M := mul_pos (cPrime_pos hr) (besselInt_pos (by positivity) _)
  have hM' : (M : ℂ) ≠ 0 := ofReal_ne_zero.2 hM.ne'
  refine ⟨(coef r n - M) / M, ?_, by field_simp; ring⟩
  rw [norm_div, norm_real, Real.norm_of_nonneg hM.le, div_le_iff₀ hM]
  linarith

/-- The real part: `Re C_r(n) = c'_r besselInt(…) (1 + Re ρ(n))`, `|Re ρ(n)| ≤ e^{−c√n}`. -/
theorem coef_re_asymp (r : ℕ) (hr : 1 ≤ r) : ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ ρ : ℝ,
    |ρ| ≤ Real.exp (-(c * √n)) ∧
      (coef r n).re = cPrime r * besselInt (((r : ℝ) + 1) / 2) (coloredKappa r * √((n : ℝ) - r /
          24)) * (1 + ρ) := by
  obtain ⟨c, hc, hev⟩ := coef_asymp r hr
  refine ⟨c, hc, hev.mono fun n ⟨ρ, hρ, h⟩ => ⟨ρ.re, (Complex.abs_re_le_norm ρ).trans hρ, ?_⟩⟩
  rw [h, ← ofReal_one, ← ofReal_re 1, re_ofReal_mul]
  simp

end

end

end MetaMathlibExt.ColoredPartitionsJensen
