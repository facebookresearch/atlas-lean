/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.EntireOrder
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Binet's formula and Stirling's formula for the complex Gamma function

The Weierstrass product of `1 / Γ`, Binet's formula for `log Γ` with the sawtooth remainder
`∫₀^∞ (⌊u⌋ - u + 1/2) / (u + z) du`, Stirling's formula `log Γ(z) = (z - 1/2) log z - z +
½ log 2π + O(1 / ‖z‖)` uniformly in every sector `|arg z| ≤ π - δ`, and its consequence that
`1 / Γ` is an entire function of order of growth exactly `1`.

Since `log Γ` on the slit plane (the branch that is real on the positive reals) is not
`Complex.log ∘ Complex.Gamma`, the formulas for `log Γ` are stated after exponentiating, as
`Γ(z) = exp (…)`.

## Main statements

* `Complex.inv_Gamma_eq_exp_mul_tprod`: the Weierstrass product
  `1 / Γ(z) = e^{γ z} z ∏_{n ≥ 1} (1 + z / n) e^{-z / n}`.
* `Complex.Gamma_eq_exp_binet`: Binet's formula. For `z` in the slit plane, the improper integral
  `I = ∫₀^∞ (⌊u⌋ - u + 1/2) / (u + z) du` converges and
  `Γ(z) = exp ((z - 1/2) log z - z + ½ log 2π + I)`.
* `Complex.Gamma_eq_exp_stirling_sector`: Stirling's formula with an `O(1 / ‖z‖)` error, uniform in
  the sector `-π + δ ≤ arg z ≤ π - δ`.
* `Complex.hasGrowthOrder_inv_Gamma`: `1 / Γ` has order of growth `1`.
-/

@[expose] public section

open Filter Topology

namespace Complex

/-! ### The sawtooth integrand -/

/-- `|⌊u⌋ - u + 1/2| ≤ 1/2`, as a complex norm. -/
theorem norm_sawtooth_le (u : ℝ) : ‖((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ))‖ ≤ 1 / 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  have h1 := Int.floor_le u
  have h2 := Int.lt_floor_add_one u
  constructor <;> linarith

/-- The Binet integrand is bounded by `1/2 · ‖u + z‖⁻¹`. -/
theorem norm_sawtooth_div_ofReal_add_le (z : ℂ) (u : ℝ) :
    ‖((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + z))‖ ≤ 1 / 2 * ‖(u : ℂ) + z‖⁻¹ := by
  rw [div_eq_mul_inv, norm_mul, norm_inv]
  exact mul_le_mul_of_nonneg_right (norm_sawtooth_le u) (by positivity)

/-- **The Binet integrand is integrable.** If `u + z ≠ 0` for every `u ≥ 0`, then
`u ↦ (⌊u⌋ - u + 1/2) / (u + z)` is interval integrable on `[a, b]` for `a, b ≥ 0`. -/
theorem intervalIntegrable_sawtooth_div_ofReal_add {z : ℂ}
    (hne : ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ≠ 0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun u : ℝ => ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + z)))
      MeasureTheory.volume a b := by
  set g : ℝ → ℂ := fun u => ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + z)) with hg
  have hgmeas : Measurable g := by fun_prop
  have hc : ContinuousOn (fun u : ℝ => 1 / 2 * ‖(u : ℂ) + z‖⁻¹) (Set.uIcc a b) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu
    have : 0 ≤ u := by
      rcases Set.mem_uIcc.1 hu with h | h <;> linarith [h.1]
    exact norm_ne_zero_iff.2 (hne u this)
  refine (hc.intervalIntegrable).mono_fun hgmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  refine (norm_sawtooth_div_ofReal_add_le z u).trans (le_of_eq ?_)
  dsimp only
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]


/-! ### The Weierstrass product of `1 / Γ` -/

/-- **The Weierstrass product of `1 / Γ`.**
`1 / Γ(z) = e^{γ z} z ∏_{n ≥ 1} (1 + z / n) e^{-z / n}`, with `γ` the Euler–Mascheroni constant,
for every `z`; at the poles `z = -m` of `Γ` both sides vanish (Mathlib's `Γ(-m)` is `0`, so the left
side is `0⁻¹ = 0`). -/
theorem inv_Gamma_eq_exp_mul_tprod (z : ℂ) :
    (Complex.Gamma z)⁻¹ =
      Complex.exp (Real.eulerMascheroniConstant * z) * z *
        ∏' n : ℕ, (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) := by
  set F : ℕ → ℂ := fun n => (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) with hF
  -- multipliability
  have hmult : Multipliable F := by
    have key : ∀ w : ℂ, ‖w‖ ≤ 1 →
        ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
      intro w hw
      have h1 := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by simpa using hw)
      have e : (1 + w) * Complex.exp (-w) - 1
          = (1 + w) * (Complex.exp (-w) - 1 - -w) - w ^ 2 := by ring
      rw [e]
      calc ‖(1 + w) * (Complex.exp (-w) - 1 - -w) - w ^ 2‖
          ≤ ‖1 + w‖ * ‖Complex.exp (-w) - 1 - -w‖ + ‖w‖ ^ 2 := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_pow]
        _ ≤ 2 * ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
            have h2 : ‖1 + w‖ ≤ 2 := (norm_add_le _ _).trans (by simp; linarith)
            simp only [norm_neg] at h1
            have : ‖1 + w‖ * ‖Complex.exp (-w) - 1 - -w‖ ≤ 2 * ‖w‖ ^ 2 :=
              mul_le_mul h2 h1 (norm_nonneg _) (by norm_num)
            linarith
        _ = 3 * ‖w‖ ^ 2 := by ring
    have hs : Summable fun n : ℕ => 3 * ‖z‖ ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
    have hg : Summable fun n => F n - 1 := by
      refine hs.of_norm_bounded_eventually ?_
      rw [Nat.cofinite_eq_atTop]
      have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖z / ((n : ℂ) + 1)‖ ≤ 1 := by
        filter_upwards [Filter.eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
        have hn' : ‖z‖ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
        rw [norm_div, show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
          Complex.norm_natCast, div_le_one (by positivity)]
        push_cast
        linarith
      filter_upwards [hev] with n hle
      have hw : ‖z / (n + 1)‖ = ‖z‖ / ((n : ℝ) + 1) := by
        rw [norm_div]; congr 1
        rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        simp
      refine (key _ hle).trans (le_of_eq ?_)
      rw [hw]; push_cast; field_simp
    by_cases h0 : ∃ n, F n = 0
    · exact multipliable_of_exists_eq_zero h0
    push Not at h0
    have hlog : Summable fun n => Complex.log (F n) := by
      have hl : Summable fun n => (3 / 2 : ℝ) * ‖F n - 1‖ := hg.norm.mul_left _
      refine hl.of_norm_bounded_eventually ?_
      filter_upwards [hg.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with n hn
      have := Complex.norm_log_one_add_half_le_self hn
      simpa using this
    obtain ⟨a, ha⟩ := hlog
    have hcomp : (Complex.exp ∘ fun n => Complex.log (F n)) = F :=
      funext fun n => Complex.exp_log (h0 n)
    exact ⟨_, hcomp ▸ ha.cexp⟩
  -- the Euler limit, rewritten as a partial Weierstrass product
  have hprod : ∀ n : ℕ, ∏ j ∈ Finset.range (n + 1), (z + j)
      = z * (n.factorial : ℂ) * ∏ j ∈ Finset.range n, (1 + z / (j + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ih, Finset.prod_range_succ, Nat.factorial_succ]
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp
      ring
  have hid : ∀ n : ℕ, n ≠ 0 → (Complex.GammaSeq z n)⁻¹ =
      Complex.exp ((((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * z) * z *
        ∏ j ∈ Finset.range n, F j := by
    intro n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hH : (((harmonic n : ℝ) : ℂ)) * z = ∑ j ∈ Finset.range n, z / ((j : ℂ) + 1) := by
      simp [harmonic, div_eq_mul_inv, mul_comm, Finset.mul_sum]
    rw [Complex.GammaSeq, inv_div, hprod, Complex.cpow_def_of_ne_zero hn', ← Complex.natCast_log]
    simp only [hF, Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_neg_distrib]
    rw [← hH, Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_neg]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  have hR : Filter.Tendsto
      (fun n : ℕ => Complex.exp ((((harmonic n : ℝ) - Real.log n : ℝ) : ℂ) * z) * z *
        ∏ j ∈ Finset.range n, F j) Filter.atTop
      (nhds (Complex.exp (Real.eulerMascheroniConstant * z) * z * ∏' n, F n)) := by
    refine (((Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp
        Real.tendsto_harmonic_sub_log).mul_const z)).mul_const z).mul
      hmult.hasProd.tendsto_prod_nat
  have hL : Filter.Tendsto (fun n : ℕ => (Complex.GammaSeq z n)⁻¹) Filter.atTop
      (nhds (Complex.Gamma z)⁻¹) := by
    by_cases hg : Complex.Gamma z = 0
    · rw [hg, inv_zero]
      obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff z).1 hg
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop m] with n hn
      have : ∏ j ∈ Finset.range (n + 1), (z + j) = 0 :=
        Finset.prod_eq_zero (i := m) (by simp; omega) (by simp [hm])
      simp [Complex.GammaSeq, this]
    · exact (Complex.GammaSeq_tendsto_Gamma z).inv₀ hg
  refine tendsto_nhds_unique (hL.congr' ?_) hR
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn using hid n hn


/-! ### Binet's formula -/

/-- **Binet's formula for `log Γ`.** For `z` off the non-positive reals,
`log Γ(z) = (z - 1/2) log z - z + ½ log 2π + ∫₀^∞ (⌊u⌋ - u + 1/2) / (u + z) du`.

The integral converges only conditionally, so it is the limit `I` of `∫₀^N` as `N → ∞`, whose
existence is part of the statement. `log Γ` is the branch on the slit plane that is real on the
positive reals, so the identity is stated after exponentiating. `log z` is the principal
`Complex.log`. -/
theorem Gamma_eq_exp_binet (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    ∃ I : ℂ,
      Filter.Tendsto
          (fun N : ℝ => ∫ u in (0 : ℝ)..N,
            ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + z)))
          Filter.atTop (nhds I) ∧
        Complex.Gamma z =
          Complex.exp ((z - 1 / 2) * Complex.log z - z +
            1 / 2 * Complex.log (2 * Real.pi) + I) := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hslit : ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ∈ Complex.slitPlane := by
    intro u hu
    rw [Complex.mem_slitPlane_iff] at hz ⊢
    rcases hz with h | h
    · left; simp; linarith
    · right; simpa using h
  have hne : ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ≠ 0 :=
    fun u hu => Complex.slitPlane_ne_zero (hslit u hu)
  set g : ℝ → ℂ := fun u => ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + z)) with hg
  set L : ℝ → ℂ := fun u => Complex.log ((u : ℂ) + z) with hL
  have hgb : ∀ u : ℝ, ‖g u‖ ≤ 1 / 2 * ‖(u : ℂ) + z‖⁻¹ :=
    norm_sawtooth_div_ofReal_add_le z
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable g MeasureTheory.volume a b :=
    fun _ _ ha hb => intervalIntegrable_sawtooth_div_ofReal_add hne ha hb
  have hLd : ∀ u : ℝ, 0 ≤ u → HasDerivAt L (((u : ℂ) + z)⁻¹) u := by
    intro u hu
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := by
      simpa using (hasDerivAt_id u).ofReal_comp
    simpa [hL, one_div] using (hid.add_const z).clog_real (hslit u hu)
  have hunit : ∀ n : ℕ, ∫ u in (n : ℝ)..((n : ℝ) + 1), g u
      = ((n : ℂ) + 1 / 2 + z) * (L ((n : ℝ) + 1) - L n) - 1 := by
    intro n
    have hd : ∀ u ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1),
        HasDerivAt (fun u : ℝ => ((n : ℂ) + 1 / 2 + z) * L u - u) (g u) u := by
      intro u hu
      have hu0 : 0 ≤ u := by linarith [hu.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hfl : ⌊u⌋ = (n : ℤ) := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hu.1, hu.2]
      have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := by
        simpa using (hasDerivAt_id u).ofReal_comp
      have hd := (((hid.add_const z).clog_real (hslit u hu0)).const_mul
        ((n : ℂ) + 1 / 2 + z)).sub hid
      refine hd.congr_deriv ?_
      simp only [hg, hfl]
      have := hne u hu0
      field_simp
      push_cast
      ring
    have hcont : ContinuousOn (fun u : ℝ => ((n : ℂ) + 1 / 2 + z) * L u - u)
        (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
      intro u hu
      have hu0 : 0 ≤ u := by linarith [hu.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      exact ((((hLd u hu0).continuousAt.const_mul _).sub
        (Complex.continuous_ofReal.continuousAt))).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hd
      (hint _ _ (by positivity) (by positivity))]
    push_cast; ring
  have hS : ∀ m : ℕ, ∫ u in (0 : ℝ)..((m : ℝ) + 1), g u
      = ((m : ℂ) + 1 / 2 + z) * L ((m : ℝ) + 1) - (z + 1 / 2) * Complex.log z
        - ∑ j ∈ Finset.range m, L ((j : ℝ) + 1) - m - 1 := by
    intro m
    induction m with
    | zero =>
      have := hunit 0
      simp only [Nat.cast_zero] at this ⊢
      rw [this]
      simp [hL]
      ring
    | succ m ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := (m : ℝ) + 1)
        (hint _ _ le_rfl (by positivity)) (hint _ _ (by positivity) (by positivity)), ih]
      have := hunit (m + 1)
      push_cast at this ⊢
      rw [this, Finset.sum_range_succ]
      ring
  -- the terms `log (1 + w) - w` of the Weierstrass product
  set w : ℕ → ℂ := fun j => z / ((j : ℂ) + 1) with hw
  set a : ℕ → ℂ := fun j => Complex.log (1 + w j) - w j with ha
  have hnn : ∀ m : ℕ, ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
    intro m
    rw [show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  have hwn : ∀ j : ℕ, ‖w j‖ = ‖z‖ / ((j : ℝ) + 1) := by
    intro j
    simp only [hw, norm_div, hnn]
  have hwt : Filter.Tendsto (fun j => ‖w j‖) Filter.atTop (nhds 0) := by
    simp only [hwn, div_eq_mul_one_div ‖z‖]
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ‖z‖
  have hwev : ∀ᶠ j in Filter.atTop, ‖w j‖ ≤ 1 / 2 :=
    hwt.eventually (ge_mem_nhds (by norm_num))
  have hab : ∀ j, ‖w j‖ ≤ 1 / 2 → ‖a j‖ ≤ ‖w j‖ ^ 2 := by
    intro j hj
    have h := Complex.norm_log_one_add_sub_self_le (z := w j) (by linarith)
    have h1 : (1 - ‖w j‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖a j‖ ≤ ‖w j‖ ^ 2 * (1 - ‖w j‖)⁻¹ / 2 := h
      _ ≤ ‖w j‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖w j‖ ^ 2 := by ring
  have hsum : Summable a := by
    have hs : Summable fun n : ℕ => ‖z‖ ^ 2 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hwev] with j hj
    refine (hab j hj).trans (le_of_eq ?_)
    rw [hwn]; push_cast; field_simp
  set A := ∑' j, a j with hA
  -- splitting the logarithm
  have hsplit : ∀ j : ℕ, (((j : ℝ) + 1 : ℝ) : ℂ) + z = (((j : ℝ) + 1 : ℝ) : ℂ) * (1 + w j) := by
    intro j
    have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    simp only [hw]; push_cast; field_simp
  have hw1 : ∀ j : ℕ, 1 + w j ≠ 0 := by
    intro j h
    apply hne ((j : ℝ) + 1) (by positivity)
    rw [hsplit j, h, mul_zero]
  have hLs : ∀ j : ℕ, L ((j : ℝ) + 1)
      = ((Real.log ((j : ℝ) + 1) : ℝ) : ℂ) + Complex.log (1 + w j) := by
    intro j
    simp only [hL]
    rw [hsplit j, Complex.log_ofReal_mul (by positivity) (hw1 j)]
  -- the real Stirling part
  set r : ℕ → ℝ := fun m => ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 1)
    - Real.log (m.factorial : ℝ) - m - 1 with hr
  have hr_eq : ∀ m : ℕ,
      r m = -Real.log (Stirling.stirlingSeq (m + 1)) - 1 / 2 * Real.log 2 := by
    intro m
    have h := Stirling.log_stirlingSeq_formula (m + 1)
    have hm : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [Nat.factorial_succ] at h
    push_cast at h
    rw [Real.log_mul hm.ne' hf.ne', Real.log_mul (by norm_num) hm.ne',
      Real.log_div hm.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
    rw [h]
    ring
  have hr_t : Filter.Tendsto r Filter.atTop (nhds (-(1 / 2) * Real.log (2 * Real.pi))) := by
    have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.comp (Filter.tendsto_add_atTop_nat 1)
    have hl := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp hs
    have : -(1 / 2) * Real.log (2 * Real.pi)
        = -Real.log (Real.sqrt Real.pi) - 1 / 2 * Real.log 2 := by
      rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']; ring
    rw [this]
    refine Filter.Tendsto.congr (fun m => ?_) (hl.neg.sub_const _)
    rw [hr_eq]; rfl
  -- `(m + 1/2 + z) log (1 + z/(m+1)) → z`
  have hlog1 : Filter.Tendsto (fun m : ℕ => Complex.log (1 + w m)) Filter.atTop (nhds 0) := by
    have hw0 : Filter.Tendsto w Filter.atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.2 hwt
    have := (continuousAt_clog (by rw [add_zero]; exact Complex.one_mem_slitPlane)).tendsto.comp
      (hw0.const_add 1)
    rw [add_zero, Complex.log_one] at this
    exact this
  have hmain3 : Filter.Tendsto (fun m : ℕ => ((m : ℂ) + 1 / 2 + z) * Complex.log (1 + w m))
      Filter.atTop (nhds z) := by
    have h1 : Filter.Tendsto (fun m : ℕ => ((m : ℂ) + 1) * Complex.log (1 + w m) - z)
        Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm' (a := fun m : ℕ => ‖z‖ ^ 2 * (1 / ((m:ℝ) + 1)))
      · filter_upwards [hwev] with m hm
        have hj : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have hm1 : ((m : ℂ) + 1) * w m = z := by simp only [hw]; field_simp
        have : ((m : ℂ) + 1) * Complex.log (1 + w m) - z = ((m : ℂ) + 1) * a m := by
          simp only [ha]; rw [mul_sub, hm1]
        rw [this, norm_mul, hnn]
        calc ((m:ℝ) + 1) * ‖a m‖ ≤ ((m:ℝ) + 1) * ‖w m‖ ^ 2 := by gcongr; exact hab m hm
          _ = _ := by rw [hwn]; field_simp
      · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (‖z‖ ^ 2)
    have h2 := (h1.add_const z).add (hlog1.const_mul (z - 1 / 2))
    rw [show (0:ℂ) + z + (z - 1 / 2) * 0 = z by ring] at h2
    exact h2.congr (fun m => by ring)
  -- the integer partial integrals in closed form
  have hseq_id : ∀ m : ℕ, ∫ u in (0:ℝ)..((m:ℝ) + 1), g u
      = ((r m : ℝ) : ℂ) + z * (((Real.log ((m:ℝ) + 1) - harmonic m : ℝ)) : ℂ)
        + ((m:ℂ) + 1 / 2 + z) * Complex.log (1 + w m) - (z + 1 / 2) * Complex.log z
        - ∑ j ∈ Finset.range m, a j := by
    intro m
    have hH : z * ((harmonic m : ℝ) : ℂ) = ∑ j ∈ Finset.range m, w j := by
      simp [hw, harmonic, div_eq_mul_inv, Finset.mul_sum]
    have hF : Real.log (m.factorial : ℝ) = ∑ j ∈ Finset.range m, Real.log ((j:ℝ) + 1) := by
      rw [← Finset.prod_range_add_one_eq_factorial]; push_cast
      rw [Real.log_prod]; intro j _; positivity
    have h1 : ∑ j ∈ Finset.range m, L ((j:ℝ) + 1)
        = ((Real.log (m.factorial : ℝ) : ℝ) : ℂ) + z * ((harmonic m : ℝ) : ℂ)
          + ∑ j ∈ Finset.range m, a j := by
      rw [hH, hF]; push_cast
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hLs j]; simp only [ha]; ring
    rw [hS m, hLs m, h1]; simp only [hr]; push_cast; ring
  set I : ℂ := ((-(1 / 2) * Real.log (2 * Real.pi) : ℝ) : ℂ)
    + z * ((-Real.eulerMascheroniConstant : ℝ) : ℂ) + z - (z + 1 / 2) * Complex.log z - A with hI
  have hlimN : Filter.Tendsto (fun m : ℕ => ∫ u in (0:ℝ)..((m:ℝ) + 1), g u)
      Filter.atTop (nhds I) := by
    have hH : Filter.Tendsto (fun m : ℕ => Real.log ((m:ℝ) + 1) - harmonic m) Filter.atTop
        (nhds (-Real.eulerMascheroniConstant)) := by
      refine Real.tendsto_eulerMascheroniSeq.neg.congr (fun m => ?_)
      simp [Real.eulerMascheroniSeq]
    have h := (((((Complex.continuous_ofReal.tendsto _).comp hr_t).add
      (((Complex.continuous_ofReal.tendsto _).comp hH).const_mul z)).add hmain3).sub_const
        ((z + 1 / 2) * Complex.log z)).sub hsum.hasSum.tendsto_sum_nat
    refine h.congr (fun m => ?_)
    rw [hseq_id m]; rfl
  -- from integer to real upper limits
  have hlimR : Filter.Tendsto (fun N : ℝ => ∫ u in (0:ℝ)..N, g u) Filter.atTop (nhds I) := by
    have hnat : Filter.Tendsto (fun m : ℕ => ∫ u in (0:ℝ)..(m:ℝ), g u) Filter.atTop (nhds I) := by
      rw [← Filter.tendsto_add_atTop_iff_nat 1]
      refine hlimN.congr (fun m => ?_); push_cast; rfl
    have hfl := hnat.comp (tendsto_nat_floor_atTop (α := ℝ))
    have hdiff : Filter.Tendsto (fun N : ℝ => (∫ u in (0:ℝ)..N, g u)
        - ∫ u in (0:ℝ)..(⌊N⌋₊ : ℝ), g u) Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm' (a := fun N : ℝ => 1 / 2 * (N - 1 - ‖z‖)⁻¹)
      · filter_upwards [Filter.eventually_ge_atTop (2 + ‖z‖)] with N hN
        have hN0 : 0 ≤ N := by linarith [norm_nonneg z]
        have hpos : 0 < N - 1 - ‖z‖ := by linarith
        rw [intervalIntegral.integral_interval_sub_left (hint _ _ le_rfl hN0)
          (hint _ _ le_rfl (Nat.cast_nonneg _))]
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (⌊N⌋₊ : ℝ))
          (b := N) (f := g) (C := 1 / 2 * (N - 1 - ‖z‖)⁻¹) ?_
        · refine hb.trans ?_
          have h1 : |N - (⌊N⌋₊ : ℝ)| ≤ 1 := by
            rw [abs_le]; constructor <;> linarith [Nat.floor_le hN0, Nat.lt_floor_add_one N]
          have : 0 ≤ 1 / 2 * (N - 1 - ‖z‖)⁻¹ := by positivity
          calc 1 / 2 * (N - 1 - ‖z‖)⁻¹ * |N - (⌊N⌋₊ : ℝ)| ≤ 1 / 2 * (N - 1 - ‖z‖)⁻¹ * 1 := by gcongr
            _ = _ := by ring
        · intro u hu
          have hu1 : (⌊N⌋₊ : ℝ) < u := by
            rcases Set.mem_uIoc.1 hu with h | h
            · exact h.1
            · linarith [h.1, h.2, Nat.floor_le hN0]
          have hu2 : N - 1 < u := by linarith [Nat.lt_floor_add_one N]
          have hnorm : N - 1 - ‖z‖ ≤ ‖(u:ℂ) + z‖ := by
            have h1 : ‖(u:ℂ)‖ ≤ ‖(u:ℂ) + z‖ + ‖z‖ := by
              calc ‖(u:ℂ)‖ = ‖((u:ℂ) + z) - z‖ := by ring_nf
                _ ≤ _ := norm_sub_le _ _
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h1
            linarith
          exact (hgb u).trans (mul_le_mul_of_nonneg_left (inv_anti₀ hpos hnorm) (by norm_num))
      · have h : Filter.Tendsto (fun N : ℝ => N - 1 - ‖z‖) Filter.atTop Filter.atTop := by
          simpa [sub_eq_add_neg, add_assoc] using
            Filter.tendsto_atTop_add_const_right Filter.atTop (-1 + -‖z‖) Filter.tendsto_id
        have := (tendsto_inv_atTop_zero.comp h).const_mul (1 / 2 : ℝ)
        rw [mul_zero] at this
        exact this
    have := hfl.add hdiff
    rw [add_zero] at this
    exact this.congr (fun N => by simp only [Function.comp]; ring)
  refine ⟨I, hlimR, ?_⟩
  -- the Weierstrass product of `1 / Γ`
  have h12 := inv_Gamma_eq_exp_mul_tprod z
  have hFa : (fun n : ℕ => (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))))
      = Complex.exp ∘ a := by
    funext n
    simp only [Function.comp, ha, Complex.exp_sub, Complex.exp_log (hw1 n)]
    simp only [hw, Complex.exp_neg, div_eq_mul_inv]
  rw [hFa, (hsum.hasSum.cexp).tprod_eq,
    show Complex.exp (Real.eulerMascheroniConstant * z) * z * Complex.exp A
      = Complex.exp (Real.eulerMascheroniConstant * z + Complex.log z + A) by
        rw [Complex.exp_add, Complex.exp_add, Complex.exp_log hz0]] at h12
  have hlog2 : ((Real.log (2 * Real.pi) : ℝ) : ℂ) = Complex.log (2 * Real.pi) := by
    rw [Complex.ofReal_log (by positivity)]; push_cast; rfl
  rw [← inv_inv (Complex.Gamma z), h12, ← Complex.exp_neg]
  congr 1
  simp only [hI]
  push_cast
  rw [hlog2]
  ring


/-- **Stirling's formula in a sector.** For every `δ > 0` there is a constant `C` such that,
for all `z ≠ 0` with `-π + δ ≤ arg z ≤ π - δ`,
`Γ(z) = exp ((z - 1/2) log z - z + ½ log 2π + E(z))` with `‖E(z)‖ ≤ C / ‖z‖`.

Once `C / ‖z‖ < π`, this `E` is the unique logarithm in that disc, so it is the remainder of the
true `log Γ`. -/
theorem Gamma_eq_exp_stirling_sector (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → -Real.pi + δ ≤ Complex.arg z → Complex.arg z ≤ Real.pi - δ →
      ∃ E : ℂ, ‖E‖ ≤ C / ‖z‖ ∧
        Complex.Gamma z =
          Complex.exp ((z - 1 / 2) * Complex.log z - z +
            1 / 2 * Complex.log (2 * Real.pi) + E) := by
  by_cases hδπ : δ ≤ Real.pi
  swap
  · refine ⟨0, fun z _ h1 h2 => ?_⟩
    exfalso; linarith
  set m : ℝ := (1 - Real.cos δ) / 2 with hm
  have hcosδ : Real.cos δ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδπ hδ
    simpa using h
  have hm0 : 0 < m := by rw [hm]; linarith
  set K : ℝ := 1 / (8 * m) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K, fun z hz0 h1 h2 => ?_⟩
  set a : ℝ := ‖z‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 hz0
  -- the sector bound
  have hre : -(a * Real.cos δ) ≤ z.re := by
    have hc : Real.cos (Real.pi - δ) ≤ Real.cos (Complex.arg z) := by
      rw [← Real.cos_abs (Complex.arg z)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
      rw [abs_le]; constructor <;> linarith
    rw [Real.cos_pi_sub, Complex.cos_arg hz0] at hc
    rw [← ha] at hc
    have := (le_div_iff₀ ha0).1 hc
    linarith
  have hsec : ∀ u : ℝ, 0 ≤ u → m * (u + a) ^ 2 ≤ ‖(u : ℂ) + z‖ ^ 2 := by
    intro u hu
    have hn : ‖(u : ℂ) + z‖ ^ 2 = (u + z.re) ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
    have ha2 : a ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [ha, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hn, hm]
    have hc1 : -1 ≤ Real.cos δ := Real.neg_one_le_cos δ
    nlinarith [mul_le_mul_of_nonneg_left hre (by linarith : (0:ℝ) ≤ 2 * u),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 + Real.cos δ) (sq_nonneg (u - a))]
  have hslit : z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, hz0⟩
    intro h; rw [h] at h2; linarith
  have hne : ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ≠ 0 := by
    intro u hu h
    have := hsec u hu
    rw [h, norm_zero] at this
    nlinarith [mul_pos hm0 (pow_pos ha0 2), sq_nonneg u, mul_nonneg hu ha0.le]
  obtain ⟨I, hlim, hG⟩ := Gamma_eq_exp_binet z hslit
  refine ⟨I, ?_, hG⟩
  set g : ℝ → ℂ := fun u => ((((⌊u⌋ : ℝ) - u + 1 / 2 : ℝ) : ℂ) / ((u : ℂ) + z)) with hg
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable g MeasureTheory.volume a b :=
    fun _ _ ha hb => intervalIntegrable_sawtooth_div_ofReal_add hne ha hb
  -- one unit interval
  have hunit : ∀ n : ℕ, ‖∫ u in (n : ℝ)..((n : ℝ) + 1), g u‖
      ≤ K * (1 / ((n : ℝ) + a) - 1 / ((n : ℝ) + 1 + a)) := by
    intro n
    set q : ℝ → ℂ := fun u => ((u : ℂ) - n - ((u : ℂ) - n) ^ 2) / 2 with hq
    set p : ℝ → ℂ := fun u => ((n : ℂ) + 1 / 2 - u) / ((u : ℂ) + z) with hp
    set h : ℝ → ℂ := fun u => q u / ((u : ℂ) + z) ^ 2 with hh
    have hcont : ∀ f : ℝ → ℂ, ContinuousOn f (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) →
        IntervalIntegrable f MeasureTheory.volume (n : ℝ) ((n : ℝ) + 1) :=
      fun f hf => hf.intervalIntegrable
    have hnn : ∀ u ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), 0 ≤ u := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      linarith [hu.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hpc : ContinuousOn p (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu; exact hne u (hnn u hu)
    have hhc : ContinuousOn h (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu; exact pow_ne_zero 2 (hne u (hnn u hu))
    -- `g = p` on the open interval
    have hgp : ∫ u in (n : ℝ)..((n : ℝ) + 1), g u = ∫ u in (n : ℝ)..((n : ℝ) + 1), p u := by
      rw [intervalIntegral.integral_of_le (by linarith),
        intervalIntegral.integral_of_le (by linarith),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
      have hfl : ⌊u⌋ = (n : ℤ) := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [hu.1, hu.2]
      simp only [hg, hp, hfl]
      push_cast; ring
    -- integration by parts
    have hibp : ∫ u in (n : ℝ)..((n : ℝ) + 1), (p u - h u) = 0 := by
      have hd : ∀ u ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1),
          HasDerivAt (fun u : ℝ => q u / ((u : ℂ) + z)) (p u - h u) u := by
        intro u hu
        have hu0 : 0 ≤ u := by linarith [hu.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
        have hz' := hne u hu0
        have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := by
          simpa using (hasDerivAt_id u).ofReal_comp
        have hqd : HasDerivAt q ((1 - 2 * ((u : ℂ) - n) * 1) / 2) u := by
          refine (((hid.sub_const (n : ℂ)).sub
            ((hid.sub_const (n : ℂ)).pow 2)).div_const 2).congr_deriv ?_
          push_cast; ring
        have hden : HasDerivAt (fun y : ℝ => (y : ℂ) + z) 1 u := hid.add_const z
        refine (hqd.div hden hz').congr_deriv ?_
        simp only [hp, hh, hq]
        field_simp
        ring
      have hc : ContinuousOn (fun u : ℝ => q u / ((u : ℂ) + z))
          (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro u hu
        exact hne u (by linarith [hu.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hc hd
        ((hcont _ hpc).sub (hcont _ hhc))]
      simp only [hq]
      push_cast
      ring
    have hgh : ∫ u in (n : ℝ)..((n : ℝ) + 1), g u = ∫ u in (n : ℝ)..((n : ℝ) + 1), h u := by
      rw [intervalIntegral.integral_sub (hcont _ hpc) (hcont _ hhc)] at hibp
      rw [hgp]; exact sub_eq_zero.1 hibp
    rw [hgh]
    have hbd : ∀ u ∈ Set.uIoc (n : ℝ) ((n : ℝ) + 1), ‖h u‖ ≤ K / (u + a) ^ 2 := by
      intro u hu
      rw [Set.uIoc_of_le (by linarith)] at hu
      have hu0 : 0 ≤ u := by linarith [hu.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hqr : q u = (((u - n - (u - n) ^ 2) / 2 : ℝ) : ℂ) := by
        simp only [hq]; push_cast; ring
      have hq8 : |(u - n - (u - n) ^ 2) / 2| ≤ 1 / 8 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u - n - 1 / 2), hu.1, hu.2]
      have hpos : 0 < (u + a) ^ 2 := by positivity
      have hs := hsec u hu0
      simp only [hh]
      rw [norm_div, norm_pow, hqr, Complex.norm_real, Real.norm_eq_abs]
      have hn2 : 0 < ‖(u : ℂ) + z‖ ^ 2 := by
        have := hne u hu0; positivity
      rw [div_le_div_iff₀ hn2 hpos, hK]
      calc |(u - n - (u - n) ^ 2) / 2| * (u + a) ^ 2 ≤ 1 / 8 * (u + a) ^ 2 := by gcongr
        _ = 1 / (8 * m) * (m * (u + a) ^ 2) := by field_simp
        _ ≤ 1 / (8 * m) * ‖(u : ℂ) + z‖ ^ 2 := by gcongr
    have hKc : ContinuousOn (fun u : ℝ => K / (u + a) ^ 2) (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro u hu; have := hnn u hu; positivity
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Filter.Eventually.of_forall fun u hu => hbd u (by
        rw [Set.uIoc_of_le (by linarith)]; exact hu)) hKc.intervalIntegrable).trans (le_of_eq ?_)
    have h0 : (0 : ℝ) ∉ Set.uIcc ((n : ℝ) + a) ((n : ℝ) + 1 + a) := by
      rw [Set.uIcc_of_le (by linarith)]
      intro h; linarith [h.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hne' : ∀ u ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), u + a ≠ 0 := by
      intro u hu; have := hnn u hu; positivity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => -K / (u + a))]
    · have h1 : (n : ℝ) + a ≠ 0 := by positivity
      have h2 : (n : ℝ) + 1 + a ≠ 0 := by positivity
      field_simp
      ring
    · intro u hu
      have hu' := hne' u hu
      have hd := (((hasDerivAt_id u).add_const a).inv hu').const_mul (-K)
      convert hd using 1
      · funext y
        simp [div_eq_mul_inv]
      · simp only [id_eq]
        field_simp
    · exact hKc.intervalIntegrable
  -- summing the unit intervals
  have hsum : ∀ n : ℕ, ‖∫ u in (0 : ℝ)..(n : ℝ), g u‖ ≤ K * (1 / a - 1 / ((n : ℝ) + a)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ))
        (hint _ _ le_rfl (by positivity)) (hint _ _ (by positivity) (by positivity))]
      push_cast
      refine (norm_add_le _ _).trans ?_
      have := hunit n
      linarith
  have hlimn := (continuous_norm.tendsto I).comp (hlim.comp tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlimn (fun n => ?_)
  simp only [Function.comp]
  refine (hsum n).trans ?_
  have : 0 < 1 / ((n : ℝ) + a) := by positivity
  rw [mul_sub, div_eq_mul_one_div K a]
  nlinarith


/-! ### The order of `1 / Γ` -/

/-- **`1 / Γ` has order of growth `1`.** It is `O(exp (‖z‖ ^ (1 + ε)))` for every `ε > 0`
(Stirling's formula on the right half-plane and the reflection formula on the left), and it has
order at most no `ρ < 1`, since along `z = 1/2 - n` it grows like `n! / 2ⁿ`. That `1 / Γ` is
entire is `Complex.differentiable_one_div_Gamma`. -/
theorem hasGrowthOrder_inv_Gamma : HasGrowthOrder (fun z => (Complex.Gamma z)⁻¹) 1 := by
  -- Stirling on the right half-plane: both `Γ` and `1/Γ` are `≤ exp (G ‖w‖)`
  obtain ⟨C, hC⟩ := Gamma_eq_exp_stirling_sector (Real.pi / 2) (by positivity)
  set K : ℝ := ‖(1 / 2 : ℂ) * Complex.log (2 * Real.pi)‖ + |C| with hK
  have hK0 : 0 ≤ K := by positivity
  set G : ℝ → ℝ := fun r => (r + 1 / 2) * (Real.log r + Real.pi) + r + K with hG
  have hstir : ∀ w : ℂ, 0 ≤ w.re → 1 ≤ ‖w‖ →
      ‖Complex.Gamma w‖ ≤ Real.exp (G ‖w‖) ∧ ‖Complex.Gamma w‖⁻¹ ≤ Real.exp (G ‖w‖) := by
    intro w hre hw
    have hw0 : w ≠ 0 := by
      rintro rfl; simp at hw; linarith
    have harg := Complex.abs_arg_le_pi_div_two_iff.mpr hre
    obtain ⟨E, hE, hΓ⟩ := hC w hw0 (by linarith [(abs_le.mp harg).1])
      (by linarith [(abs_le.mp harg).2])
    set X : ℂ := (w - 1 / 2) * Complex.log w - w + 1 / 2 * Complex.log (2 * Real.pi) + E
      with hX
    have hlog : ‖Complex.log w‖ ≤ Real.log ‖w‖ + Real.pi := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log w)
      rw [Complex.log_re, Complex.log_im] at h1
      have h2 := Complex.abs_arg_le_pi w
      have h3 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw
      rw [abs_of_nonneg h3] at h1
      linarith
    have hw12 : ‖w - 1 / 2‖ ≤ ‖w‖ + 1 / 2 := by
      calc ‖w - 1 / 2‖ ≤ ‖w‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖w‖ + 1 / 2 := by norm_num
    have hEC : ‖E‖ ≤ |C| := by
      calc ‖E‖ ≤ C / ‖w‖ := hE
        _ ≤ |C| / ‖w‖ := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hw
    have hXn : ‖X‖ ≤ G ‖w‖ := by
      have h1 : ‖X‖ ≤ ‖w - 1 / 2‖ * ‖Complex.log w‖ + ‖w‖ +
          ‖(1 / 2 : ℂ) * Complex.log (2 * Real.pi)‖ + ‖E‖ := by
        calc ‖X‖ ≤ ‖(w - 1 / 2) * Complex.log w - w + 1 / 2 * Complex.log (2 * Real.pi)‖
              + ‖E‖ := norm_add_le _ _
          _ ≤ ‖(w - 1 / 2) * Complex.log w - w‖ + ‖(1 / 2 : ℂ) * Complex.log (2 * Real.pi)‖
              + ‖E‖ := by gcongr; exact norm_add_le _ _
          _ ≤ ‖(w - 1 / 2) * Complex.log w‖ + ‖w‖ + ‖(1 / 2 : ℂ) * Complex.log (2 * Real.pi)‖
              + ‖E‖ := by gcongr; exact norm_sub_le _ _
          _ = _ := by rw [norm_mul]
      have h2 : ‖w - 1 / 2‖ * ‖Complex.log w‖ ≤ (‖w‖ + 1 / 2) * (Real.log ‖w‖ + Real.pi) :=
        mul_le_mul hw12 hlog (norm_nonneg _) (by positivity)
      simp only [hG, hK]
      linarith
    have hΓn : ‖Complex.Gamma w‖ = Real.exp X.re := by rw [hΓ, Complex.norm_exp]
    have hre1 : |X.re| ≤ ‖X‖ := Complex.abs_re_le_norm X
    refine ⟨?_, ?_⟩
    · rw [hΓn]; exact Real.exp_le_exp.mpr (by linarith [le_abs_self X.re])
    · rw [hΓn, ← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith [neg_abs_le X.re])
  have hGmono : ∀ s t : ℝ, 1 ≤ s → s ≤ t → G s ≤ G t := by
    intro s t hs hst
    have h1 : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
    have h2 : 0 ≤ Real.log s := Real.log_nonneg hs
    have h3 : (s + 1 / 2) * (Real.log s + Real.pi) ≤ (t + 1 / 2) * (Real.log t + Real.pi) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    simp only [hG]; linarith
  have hsin : ∀ x : ℂ, ‖Complex.sin x‖ ≤ Real.exp ‖x‖ := by
    intro x
    have e1 : ‖Complex.exp (-x * Complex.I)‖ ≤ Real.exp ‖x‖ := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      calc (-x * Complex.I).re ≤ ‖-x * Complex.I‖ := Complex.re_le_norm _
        _ = ‖x‖ := by simp
    have e2 : ‖Complex.exp (x * Complex.I)‖ ≤ Real.exp ‖x‖ := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      calc (x * Complex.I).re ≤ ‖x * Complex.I‖ := Complex.re_le_norm _
        _ = ‖x‖ := by simp
    have : Complex.sin x =
        (Complex.exp (-x * Complex.I) - Complex.exp (x * Complex.I)) * Complex.I / 2 := rfl
    rw [this, norm_div, norm_mul]
    have := norm_sub_le (Complex.exp (-x * Complex.I)) (Complex.exp (x * Complex.I))
    simp only [Complex.norm_I, mul_one, Complex.norm_ofNat]
    linarith
  -- pointwise bound for `‖z‖ ≥ 2`
  have hpt : ∀ z : ℂ, 2 ≤ ‖z‖ →
      ‖(Complex.Gamma z)⁻¹‖ ≤ Real.exp (G (2 * ‖z‖) + Real.pi * ‖z‖) := by
    intro z hz
    by_cases hre : 0 ≤ z.re
    · rw [norm_inv]
      refine ((hstir z hre (by linarith)).2).trans (Real.exp_le_exp.mpr ?_)
      have := hGmono ‖z‖ (2 * ‖z‖) (by linarith) (by linarith)
      have : 0 ≤ Real.pi * ‖z‖ := by positivity
      linarith
    · rw [not_le] at hre
      have hre1 : 0 ≤ (1 - z).re := by simp; linarith
      have hn1 : 1 ≤ ‖1 - z‖ := by
        have := Complex.re_le_norm (1 - z); simp at this ⊢; linarith
      have hn2 : ‖1 - z‖ ≤ 2 * ‖z‖ := by
        calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ 2 * ‖z‖ := by simp; linarith
      have hΓ1 : Complex.Gamma (1 - z) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
      have hrefl := Complex.Gamma_mul_Gamma_one_sub z
      have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have heq : (Complex.Gamma z)⁻¹ =
          Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
        by_cases hg : Complex.Gamma z = 0
        · rw [hg, zero_mul] at hrefl
          have hs : Complex.sin (Real.pi * z) = 0 := by
            rcases div_eq_zero_iff.mp hrefl.symm with h | h
            · exact absurd h hπ0
            · exact h
          rw [hg, hs]; simp
        · have hs : Complex.sin (Real.pi * z) ≠ 0 := by
            intro hs; rw [hs, div_zero] at hrefl
            exact mul_ne_zero hg hΓ1 hrefl
          rw [eq_div_iff hs] at hrefl
          rw [eq_div_iff hπ0]
          calc (Complex.Gamma z)⁻¹ * Real.pi
              = (Complex.Gamma z)⁻¹ *
                  (Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (Real.pi * z)) := by
                rw [hrefl]
            _ = _ := by field_simp
      rw [heq, norm_div, norm_mul]
      have hA := (hstir (1 - z) hre1 hn1).1
      have hB := hsin (Real.pi * z)
      have hπz : ‖(Real.pi : ℂ) * z‖ = Real.pi * ‖z‖ := by
        rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
      rw [hπz] at hB
      have hGm := hGmono _ _ hn1 hn2
      have hπn : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
      rw [hπn, Real.exp_add]
      have hpi1 : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
      have hA' : ‖Complex.Gamma (1 - z)‖ ≤ Real.exp (G (2 * ‖z‖)) :=
        hA.trans (Real.exp_le_exp.mpr hGm)
      rw [div_le_iff₀ Real.pi_pos]
      calc ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (Real.pi * z)‖
          ≤ Real.exp (G (2 * ‖z‖)) * Real.exp (Real.pi * ‖z‖) :=
            mul_le_mul hA' hB (norm_nonneg _) (by positivity)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hpi1
  -- `G (2r) + π r ≤ r (3 log r + B)` for `r ≥ 2`
  have hlin : ∀ r : ℝ, 2 ≤ r →
      G (2 * r) + Real.pi * r ≤ r * (3 * Real.log r + (21 + K)) := by
    intro r hr
    have hl2 : Real.log (2 * r) = Real.log 2 + Real.log r :=
      Real.log_mul (by norm_num) (by linarith)
    have hlog2 := Real.log_two_lt_d9
    have hpi4 := Real.pi_le_four
    have hlr : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
    have h1 : (2 * r + 1 / 2) * (Real.log (2 * r) + Real.pi) ≤
        (3 * r) * (Real.log r + 5) := by
      rw [hl2]
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have h2 : K ≤ K * r := le_mul_of_one_le_right hK0 (by linarith)
    have h3 : Real.pi * r ≤ 4 * r := by nlinarith
    simp only [hG]
    nlinarith
  refine ⟨fun ε hε => ?_, fun b' hb' hb => ?_⟩
  · -- order at most `1`
    have hlo := (isLittleO_log_rpow_atTop hε).bound (show (0 : ℝ) < 1 / 6 by norm_num)
    have htend := (tendsto_rpow_atTop hε).eventually_ge_atTop (2 * (21 + K))
    have hev : ∀ᶠ r : ℝ in Filter.atTop, G (2 * r) + Real.pi * r ≤ r ^ (1 + ε) := by
      filter_upwards [hlo, htend, Filter.eventually_ge_atTop (2 : ℝ)] with r h1 h2 h3
      have hr0 : 0 < r := by linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 ε)] at h1
      have h4 : Real.log r ≤ 1 / 6 * r ^ ε := (le_abs_self _).trans h1
      rw [Real.rpow_add hr0, Real.rpow_one]
      refine (hlin r h3).trans ?_
      apply mul_le_mul_of_nonneg_left _ hr0.le
      linarith
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually hev,
      tendsto_norm_cobounded_atTop.eventually (Filter.eventually_ge_atTop (2 : ℝ))]
      with z h1 h2
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hpt z h2).trans (Real.exp_le_exp.mpr h1)
  · -- order at least `1`: along `1/2 - n`, `1/Γ` grows like `n!/2ⁿ`
    set c : ℝ := b' + (1 - b') / 2 with hc
    have hc1 : c ≤ 1 := by rw [hc]; linarith
    obtain ⟨M, hM⟩ := (hb ((1 - b') / 2) (by linarith)).bound
    set z : ℕ → ℂ := fun n => 1 / 2 - (n : ℂ) with hz
    set a : ℕ → ℝ := fun n => ‖(Complex.Gamma (z n))⁻¹‖ with ha
    have hzn : ∀ n : ℕ, 1 ≤ n → ‖z n‖ = n - 1 / 2 := by
      intro n hn
      have : z n = (((1 / 2 : ℝ) - n : ℝ) : ℂ) := by simp [hz]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
      · ring
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
    have hstep : ∀ n : ℕ, a (n + 1) = (n + 1 / 2) * a n := by
      intro n
      set s : ℂ := z (n + 1) with hs
      have hs1 : s + 1 = z n := by simp [hs, hz]; ring
      have hsn : ‖s‖ = n + 1 / 2 := by
        rw [hs, hzn (n + 1) (by omega)]; push_cast; ring
      have hs0 : s ≠ 0 := by
        intro h; rw [h, norm_zero] at hsn; have : (0 : ℝ) ≤ n := by positivity
        linarith
      have h := Complex.Gamma_add_one s hs0
      rw [hs1] at h
      change ‖(Complex.Gamma s)⁻¹‖ = (n + 1 / 2) * ‖(Complex.Gamma (z n))⁻¹‖
      rw [h, mul_inv, norm_mul, norm_inv s, hsn]
      have : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
      field_simp
    have ha0 : 0 < a 0 := by
      simp only [ha, hz]
      rw [norm_inv]
      apply inv_pos.mpr (norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos _))
      norm_num
    have hfac : ∀ n : ℕ, (n.factorial : ℝ) * a 0 ≤ a n * 2 ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hstep, Nat.factorial_succ]
        have han : 0 ≤ a n := norm_nonneg _
        push_cast
        have h2n : 0 ≤ a n * 2 ^ n := by positivity
        have := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ n + 1 by positivity)
        rw [pow_succ]
        nlinarith
    -- `z n → ∞`
    have hzt : Filter.Tendsto z Filter.atTop (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      refine Filter.tendsto_atTop_mono' Filter.atTop ?_
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := -(1 / 2 : ℝ))))
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [hzn n hn]; linarith
    set e : ℝ := Real.exp 1 with he
    have he0 : 0 < e := Real.exp_pos 1
    have hev1 := hzt.eventually hM
    have hev2 := tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 * e ^ 2)
    have hev3 := (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < 2 by norm_num)).eventually_gt_atTop (M * e / a 0)
    obtain ⟨n, h1, h2, h3, h4⟩ :=
      (hev1.and (hev2.and (hev3.and (Filter.eventually_ge_atTop 2)))).exists
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h4
    have hzn' := hzn n (by omega)
    -- `a n ≤ M e^{n+1}`
    have hup : a n ≤ M * e ^ n * e := by
      have hnorm1 : 1 ≤ ‖z n‖ := by rw [hzn']; linarith
      have hpow : ‖z n‖ ^ (b' + (1 - b') / 2) ≤ (n : ℝ) + 1 := by
        calc ‖z n‖ ^ (b' + (1 - b') / 2) ≤ ‖z n‖ ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnorm1 hc1
          _ ≤ _ := by rw [Real.rpow_one, hzn']; linarith
      have hexp : Real.exp ((n : ℝ) + 1) = e ^ n * e := by
        rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
      have hM0 : 0 ≤ M := by
        by_contra hneg
        have := h1.trans' (norm_nonneg _)
        have : 0 < ‖Real.exp (‖z n‖ ^ (b' + (1 - b') / 2))‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_pos _
        nlinarith
      calc a n ≤ M * ‖Real.exp (‖z n‖ ^ (b' + (1 - b') / 2))‖ := h1
        _ ≤ M * Real.exp ((n : ℝ) + 1) := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) hM0
        _ = M * e ^ n * e := by rw [hexp]; ring
    -- `nⁿ ≤ eⁿ n!`
    have hst : (n : ℝ) ^ n ≤ e ^ n * n.factorial := by
      have := Real.pow_div_factorial_le_exp (n : ℝ) (by positivity) n
      have hen : Real.exp n = e ^ n := by rw [he, ← Real.exp_nat_mul, mul_one]
      rw [div_le_iff₀ (by positivity), hen] at this
      exact this
    have hbig : (4 * e ^ 2) ^ n ≤ (n : ℝ) ^ n := pow_le_pow_left₀ (by positivity) h2 n
    set Q : ℝ := (2 * e ^ 2) ^ n with hQ
    have hQ0 : 0 < Q := by positivity
    have hsplit : (4 * e ^ 2) ^ n = 2 ^ n * Q := by
      rw [hQ, ← mul_pow]; ring
    have hen : e ^ n * 2 ^ n * e ^ n = Q := by
      rw [hQ, ← mul_pow, ← mul_pow]; ring
    have hchain : a 0 * 2 ^ n * Q ≤ M * e * Q := by
      have h5 : a 0 * (n : ℝ) ^ n ≤ e ^ n * (a n * 2 ^ n) := by
        calc a 0 * (n : ℝ) ^ n ≤ a 0 * (e ^ n * n.factorial) :=
              mul_le_mul_of_nonneg_left hst ha0.le
          _ = e ^ n * (n.factorial * a 0) := by ring
          _ ≤ e ^ n * (a n * 2 ^ n) := mul_le_mul_of_nonneg_left (hfac n) (by positivity)
      have h6 : e ^ n * (a n * 2 ^ n) ≤ e ^ n * (M * e ^ n * e * 2 ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hup (by positivity))
          (by positivity)
      have h7 : a 0 * (2 ^ n * Q) ≤ a 0 * (n : ℝ) ^ n := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left hbig ha0.le
      calc a 0 * 2 ^ n * Q = a 0 * (2 ^ n * Q) := by ring
        _ ≤ e ^ n * (M * e ^ n * e * 2 ^ n) := h7.trans (h5.trans h6)
        _ = M * e * (e ^ n * 2 ^ n * e ^ n) := by ring
        _ = M * e * Q := by rw [hen]
    have h8 := le_of_mul_le_mul_right hchain hQ0
    rw [div_lt_iff₀ ha0] at h3
    linarith


end Complex
