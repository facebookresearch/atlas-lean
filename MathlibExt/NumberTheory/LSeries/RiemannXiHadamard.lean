/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.HadamardProduct
public import MathlibExt.NumberTheory.LSeries.RiemannXi
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import MathlibExt.NumberTheory.LSeries.CompletedLFunctionGrowth
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ZetaValues

/-!
# The Hadamard product of the Riemann xi function

The Riemann xi function `ξ(s) = s (s - 1) / 2 · Λ₀(s) + 1 / 2` is an entire function of order
exactly `1` whose zeros are the nontrivial zeros of `ζ`. Hence it has a Hadamard product
`ξ(s) = exp (A + B s) ∏_ρ (1 - s / ρ) exp (s / ρ)`, and `ζ` has infinitely many zeros in the
critical strip.

## Main statements

* `RiemannXi.exists_norm_riemannXi_lt_exp`: `‖ξ(s)‖ < exp (c ‖s‖ log ‖s‖)` for large `‖s‖`.
* `RiemannXi.hasGrowthOrder_riemannXi`: `ξ` has order of growth exactly `1`.
* `riemannZetaNontrivialZeros_infinite`: `ζ` has infinitely many zeros in `0 ≤ Re s ≤ 1`.
* `RiemannXi.exists_riemannXi_eq_exp_mul_tprod`: the Hadamard product of `ξ`.
* `RiemannXi.exists_eq_neg_log_two_of_riemannXi_eq_exp_mul_tprod`: its constant term is
  `A ≡ -log 2 (mod 2πi)`.
* `RiemannXi.hasSum_re_one_div_of_riemannXi_eq_exp_mul_tprod`: `∑_ρ Re (1 / ρ) = -Re B`.
* `RiemannXi.neg_logDeriv_riemannZeta_eq`: the expansion
  `-ζ'/ζ(s) = 1/(s-1) - B - (log π)/2 + ψ(s/2+1)/2 - ∑_ρ (1/(s-ρ) + 1/ρ)`.
-/

@[expose] public section

open Filter Asymptotics Bornology ComplexConjugate

namespace RiemannXi

@[simp]
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]

@[simp]
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

/-- `ξ` commutes with complex conjugation. -/
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  rcases eq_or_ne s 0 with rfl | h0
  · simp [map_ofNat]
  rcases eq_or_ne s 1 with rfl | h1
  · simp [map_ofNat]
  have h0' : conj s ≠ 0 := by simpa using h0
  have h1' : conj s ≠ 1 := by intro h; apply h1; simpa using congrArg conj h
  rw [riemannXi_eq_mul_completedRiemannZeta h0' h1', riemannXi_eq_mul_completedRiemannZeta h0 h1,
    completedRiemannZeta_conj]
  simp [map_div₀, map_ofNat]

/-- `ξ(s) = conj (ξ (1 - conj s))`: the functional equation combined with conjugation. -/
theorem riemannXi_eq_conj_one_sub_conj (s : ℂ) :
    riemannXi s = conj (riemannXi (1 - conj s)) := by
  rw [← riemannXi_conj, map_sub, map_one, Complex.conj_conj, riemannXi_one_sub]

/-- `ξ` is of factorial type: `‖ξ(s)‖ ≤ A Bᴺ N!` whenever `‖s‖ + 1 ≤ N`. -/
theorem exists_norm_riemannXi_le_mul_pow_mul_factorial :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (s : ℂ) (N : ℕ),
      ‖s‖ + 1 ≤ N → ‖riemannXi s‖ ≤ A * B ^ N * N.factorial := by
  obtain ⟨A, B, hA, hB, h⟩ :=
    HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_mul_pow_mul_factorial 0
  refine ⟨A + 1, 4 * B, by positivity, by linarith, fun s N hN => ?_⟩
  have hΛ : ‖completedRiemannZeta₀ s‖ ≤ A * B ^ N * N.factorial := h s N hN
  have hs : ‖s‖ ≤ N := by linarith
  have hs1 : ‖s - 1‖ ≤ N := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hN2 : (N : ℝ) ^ 2 ≤ 4 ^ N := by
    have h2 : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc (N : ℝ) ^ 2 ≤ (2 ^ N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 2
      _ = 4 ^ N := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hBN : 1 ≤ B ^ N := one_le_pow₀ hB
  have hfac : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h4N : (1 : ℝ) ≤ 4 ^ N := one_le_pow₀ (by norm_num)
  calc ‖riemannXi s‖ ≤ ‖s‖ * ‖s - 1‖ / 2 * ‖completedRiemannZeta₀ s‖ + 1 / 2 := by
        unfold riemannXi
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_div, norm_mul]
        simp
    _ ≤ (N : ℝ) * N / 2 * (A * B ^ N * N.factorial) + 1 / 2 := by gcongr
    _ ≤ (A + 1) * (4 * B) ^ N * N.factorial := by
        rw [mul_pow]
        have h1 : (N : ℝ) * N / 2 * (A * B ^ N * N.factorial) ≤
            A * (4 ^ N * B ^ N) * N.factorial := by
          have : (N : ℝ) * N / 2 ≤ 4 ^ N := by nlinarith
          calc (N : ℝ) * N / 2 * (A * B ^ N * N.factorial)
              ≤ 4 ^ N * (A * B ^ N * N.factorial) := by gcongr
            _ = _ := by ring
        have h2 : (1 / 2 : ℝ) ≤ 4 ^ N * B ^ N * N.factorial := by
          have : (1 : ℝ) ≤ 4 ^ N * B ^ N * N.factorial := by
            have := mul_le_mul h4N hBN zero_le_one (by positivity)
            have := mul_le_mul this hfac zero_le_one (by positivity)
            simpa using this
          linarith
        nlinarith

/-- `‖ξ(s)‖ ≤ exp (4 ‖s‖ log ‖s‖)` for large `‖s‖`. -/
theorem eventually_norm_riemannXi_le_exp :
    ∀ᶠ s in cobounded ℂ, ‖riemannXi s‖ ≤ Real.exp (4 * ‖s‖ * Real.log ‖s‖) := by
  obtain ⟨A, B, -, hB, h⟩ := exists_norm_riemannXi_le_mul_pow_mul_factorial
  filter_upwards [eventually_norm_le_rpow_of_le_mul_pow_mul_factorial (by linarith) h,
    tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with s hs hs0
  rwa [Real.rpow_def_of_pos hs0, show Real.log ‖s‖ * (4 * ‖s‖) = 4 * ‖s‖ * Real.log ‖s‖ by
    ring] at hs

/-- **Growth of `ξ`.** For some constant `c`, `‖ξ(s)‖ < exp (c ‖s‖ log ‖s‖)` for all large
`‖s‖`. -/
theorem exists_norm_riemannXi_lt_exp :
    ∃ c : ℝ, ∀ᶠ s in cobounded ℂ, ‖riemannXi s‖ < Real.exp (c * ‖s‖ * Real.log ‖s‖) := by
  refine ⟨5, ?_⟩
  filter_upwards [eventually_norm_riemannXi_le_exp,
    tendsto_norm_cobounded_atTop.eventually_gt_atTop 1] with s hs hs1
  refine hs.trans_lt (Real.exp_lt_exp.mpr ?_)
  have := Real.log_pos hs1
  have : 0 < ‖s‖ * Real.log ‖s‖ := by positivity
  linarith

/-- `ξ` has order of growth at most `1`. -/
theorem hasGrowthOrderLE_riemannXi : Complex.HasGrowthOrderLE riemannXi 1 :=
  Complex.hasGrowthOrderLE_one_of_eventually_norm_le_exp_mul_log eventually_norm_riemannXi_le_exp

/-- `ξ` grows factorially along the even integers: `‖ξ(2(n+1))‖ ≥ n! / π^(n+1)`. -/
theorem factorial_div_pi_pow_le_norm_riemannXi (n : ℕ) :
    (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤ ‖riemannXi ((2 * (n + 1) : ℕ) : ℂ)‖ := by
  set k : ℕ := 2 * (n + 1) with hk
  have hk2 : 2 ≤ k := by omega
  set s : ℂ := ((k : ℕ) : ℂ) with hs
  have hs0 : s ≠ 0 := by rw [hs]; exact_mod_cast (show k ≠ 0 by omega)
  have hs1 : s ≠ 1 := by rw [hs]; exact_mod_cast (show k ≠ 1 by omega)
  have hsre : 0 < s.re := by rw [hs]; simp; omega
  have hζ := riemannZeta_def_of_ne_zero hs0
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hxi : riemannXi s = 1 / 2 * s * (s - 1) * (Complex.Gammaℝ s * riemannZeta s) := by
    rw [hζ, mul_div_cancel₀ _ hG, riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
    ring
  have hGv : Complex.Gammaℝ s = ((Real.pi ^ (n + 1))⁻¹ * n.factorial : ℝ) := by
    rw [Complex.Gammaℝ_def]
    have : s / 2 = ((n : ℂ) + 1) := by rw [hs, hk]; push_cast; ring
    rw [this, Complex.Gamma_nat_eq_factorial]
    have : -s / 2 = ((-(n + 1 : ℕ) : ℤ) : ℂ) := by rw [hs, hk]; push_cast; ring
    rw [this, Complex.cpow_intCast]
    push_cast
    norm_cast
  set Z : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ k with hZ
  have hZ1 : 1 ≤ Z := by
    have hsum : Summable (fun m : ℕ => 1 / (m : ℝ) ^ k) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    have := hsum.le_tsum 1 (fun m _ => by positivity)
    simpa [hZ, one_div] using this
  have hζv : riemannZeta s = (Z : ℂ) := by
    rw [hs, zeta_nat_eq_tsum_of_gt_one (by omega), hZ, Complex.ofReal_tsum]
    push_cast; rfl
  rw [hxi, hGv, hζv, hs]
  have hr : (1 / 2 * (k : ℂ) * ((k : ℂ) - 1) * (((Real.pi ^ (n + 1))⁻¹ * n.factorial : ℝ) *
      (Z : ℂ))) = ((1 / 2 * (k : ℝ) * ((k : ℝ) - 1) * ((Real.pi ^ (n + 1))⁻¹ *
      n.factorial * Z)) : ℝ) := by push_cast; ring
  rw [hr, Complex.norm_real, Real.norm_eq_abs]
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hpos : 0 < (Real.pi ^ (n + 1))⁻¹ * n.factorial := by positivity
  have h1 : 1 ≤ 1 / 2 * (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
  rw [abs_of_pos (by positivity), div_eq_inv_mul]
  calc (Real.pi ^ (n + 1))⁻¹ * n.factorial
      = 1 * (((Real.pi ^ (n + 1))⁻¹ * n.factorial) * 1) := by ring
    _ ≤ 1 / 2 * (k : ℝ) * ((k : ℝ) - 1) * ((Real.pi ^ (n + 1))⁻¹ * n.factorial * Z) := by
      gcongr

/-- `ξ` is not of exponential type. -/
theorem not_isBigO_riemannXi_exp_mul_norm (b : ℝ) :
    ¬ riemannXi =O[cobounded ℂ] fun s => Real.exp (b * ‖s‖) := by
  refine Complex.not_isBigO_exp_mul_norm_of_factorial_le (s := fun n => ((2 * (n + 1) : ℕ) : ℂ))
    (a := 2) (C := Real.pi) (K := Real.pi) ?_
    (fun n => by rw [Complex.norm_natCast]; push_cast; rfl) ?_ b
  · rw [← tendsto_norm_atTop_iff_cobounded]
    simp only [Complex.norm_natCast]
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun n => show n ≤ 2 * (n + 1) by omega) tendsto_id)
  · refine Eventually.of_forall fun n => ?_
    have h := factorial_div_pi_pow_le_norm_riemannXi n
    rw [div_le_iff₀ (by positivity)] at h
    calc (n.factorial : ℝ) ≤ _ := h
      _ = Real.pi * Real.pi ^ n * ‖riemannXi ((2 * (n + 1) : ℕ) : ℂ)‖ := by ring

/-- **`ξ` has order `1`.** -/
theorem hasGrowthOrder_riemannXi : Complex.HasGrowthOrder riemannXi 1 := by
  refine Complex.hasGrowthOrder_one_of_not_isBigO_exp_norm hasGrowthOrderLE_riemannXi ?_
  simpa using not_isBigO_riemannXi_exp_mul_norm 1

/-- **The Hadamard product of `ξ`.** For any family `z` listing the zeros of `ξ` with
multiplicity (that is, the nontrivial zeros of `ζ`), there are constants `A`, `B` with
`ξ(s) = exp (A + B s) ∏ₙ (1 - s / zₙ) exp (s / zₙ)`. -/
theorem exists_riemannXi_eq_exp_mul_tprod {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    ∃ A B : ℂ, ∀ s, riemannXi s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n) :=
  Complex.exists_eq_exp_mul_tprod_of_hasGrowthOrderLE_one differentiable_riemannXi
    hasGrowthOrderLE_riemannXi (by simp) hz

/-- The constant term of the Hadamard product of `ξ` is `A ≡ -log 2 (mod 2πi)`, since
`exp A = ξ(0) = 1 / 2`. -/
theorem exists_eq_neg_log_two_of_riemannXi_eq_exp_mul_tprod {ι : Type*} {z : ι → ℂ} {A B : ℂ}
    (hAB : ∀ s, riemannXi s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n)) :
    ∃ k : ℤ, A = -(Real.log 2 : ℂ) + 2 * Real.pi * Complex.I * k := by
  have h0 := Complex.exp_eq_apply_zero_of_eq_exp_mul_tprod hAB
  rw [riemannXi_zero] at h0
  have he : Complex.exp A = Complex.exp (-(Real.log 2 : ℂ)) := by
    rw [h0, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    push_cast; ring
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  exact ⟨k, by rw [hk]; ring⟩

/-- In the Hadamard product of `ξ`, `∑_ρ Re (1 / ρ) = -Re B`, the sum running over the nontrivial
zeros of `ζ` with multiplicity. -/
theorem hasSum_re_one_div_of_riemannXi_eq_exp_mul_tprod {ι : Type*} {z : ι → ℂ} {A B : ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w)
    (hAB : ∀ s, riemannXi s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n)) :
    HasSum (fun n => (1 / z n).re) (-B.re) :=
  Complex.hasSum_re_one_div_of_eq_exp_mul_tprod differentiable_riemannXi
    hasGrowthOrderLE_riemannXi (by simp) hz (ε := 1)
    (fun s => by rw [one_mul, riemannXi_eq_conj_one_sub_conj])
    (fun w hw => by
      have := riemannXi_mem_strip hw
      exact ⟨this.1.le, this.2.le⟩) hAB

/-- A family listing the zeros of `ξ` with multiplicity consists of nonzero points. -/
theorem ne_zero_of_card_eq_analyticOrderAt {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) (n : ι) : z n ≠ 0 :=
  fun h => by simpa [h] using Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz n

/-- A family listing the zeros of `ξ` with multiplicity satisfies `∑ ‖zₙ‖⁻² < ∞`. -/
theorem summable_norm_rpow_neg_two {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) :
    Summable fun n => ‖z n‖ ^ (-2 : ℝ) :=
  Complex.summable_norm_rpow_neg_two_of_hasGrowthOrderLE_one differentiable_riemannXi
    hasGrowthOrderLE_riemannXi (by simp) hz

/-- **The zero-sum expansion of `-ζ'/ζ`.** With `B` the linear coefficient of the Hadamard
product of `ξ`, for `s ≠ 1` with `ζ(s) ≠ 0`,
`-ζ'(s)/ζ(s) = 1/(s-1) - B - (log π)/2 + ψ(s/2+1)/2 - ∑_ρ (1/(s-ρ) + 1/ρ)`,
the sum running over the nontrivial zeros of `ζ` with multiplicity, each zero's two terms kept
paired. Here `ψ = Γ'/Γ` is `Complex.digamma`. -/
theorem neg_logDeriv_riemannZeta_eq {ι : Type*} {z : ι → ℂ}
    (hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) {A B : ℂ}
    (hAB : ∀ s, riemannXi s =
      Complex.exp (A + B * s) * ∏' n, (1 - s / z n) * Complex.exp (s / z n))
    {s : ℂ} (hs1 : s ≠ 1) (hs : riemannZeta s ≠ 0) :
    -logDeriv riemannZeta s = 1 / (s - 1) - B - (Real.log Real.pi : ℂ) / 2
      + Complex.digamma (s / 2 + 1) / 2 - ∑' n, (1 / (s - z n) + 1 / z n) := by
  classical
  have hzero := Complex.apply_eq_zero_of_card_eq_analyticOrderAt hz
  have hz0 := ne_zero_of_card_eq_analyticOrderAt hz
  -- `ζ = ξ / D` off `1`
  set D : ℂ → ℂ := fun w => (w - 1) * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1)
    with hD
  have hζ : ∀ w, w ≠ 1 → riemannZeta w = riemannXi w / D w := by
    intro w hw1
    rcases eq_or_ne w 0 with rfl | hw0
    · simp [hD, riemannZeta_zero]
      norm_num
    · have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
      have hG : Complex.Gamma (w / 2 + 1) = w / 2 * Complex.Gamma (w / 2) :=
        Complex.Gamma_add_one _ (div_ne_zero hw0 two_ne_zero)
      have hDw : D w = (w * (w - 1) / 2) * Complex.Gammaℝ w := by
        simp only [hD, hG, Complex.Gammaℝ_def]; ring
      rw [riemannZeta_def_of_ne_zero hw0, hDw, riemannXi_eq_mul_completedRiemannZeta hw0 hw1,
        mul_div_mul_left _ _ (div_ne_zero (mul_ne_zero hw0 hw1') two_ne_zero)]
  have hGs : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
    intro m hm
    apply hs
    have : s = -2 * ((m : ℂ) + 1) := by linear_combination 2 * hm
    rw [this]; exact riemannZeta_neg_two_mul_nat_add_one m
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDs : D s ≠ 0 := by
    simp only [hD]
    refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hs1) ?_) (Complex.Gamma_ne_zero hGs)
    simp [Complex.cpow_eq_zero_iff, hpi]
  have hxis : riemannXi s ≠ 0 := by
    intro h; apply hs; rw [hζ s hs1, h, zero_div]
  have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2 + 1)) s :=
    (Complex.differentiableAt_Gamma _ hGs).comp s (by fun_prop)
  have hcd : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h1 : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    exact h1.const_cpow (Or.inl hpi)
  have hDd : DifferentiableAt ℂ D s :=
    ((differentiableAt_id.sub_const 1).mul hcd.differentiableAt).mul hΓ
  have hev : riemannZeta =ᶠ[nhds s] fun w => riemannXi w / D w := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with w hw using hζ w hw
  have hL1 : logDeriv riemannZeta s = logDeriv riemannXi s - logDeriv D s := by
    rw [← logDeriv_fun_div s hxis hDs (differentiable_riemannXi s) hDd, logDeriv_apply,
      logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hL2 : logDeriv D s =
      1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2 := by
    have hc0 : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hpi]
    rw [show D = fun w => (fun w : ℂ => (w - 1) * (Real.pi : ℂ) ^ (-w / 2)) w *
        (fun w : ℂ => Complex.Gamma (w / 2 + 1)) w from rfl,
      logDeriv_fun_mul (f := fun w : ℂ => (w - 1) * (Real.pi : ℂ) ^ (-w / 2))
        (g := fun w : ℂ => Complex.Gamma (w / 2 + 1)) s
        (mul_ne_zero (sub_ne_zero.mpr hs1) hc0) (Complex.Gamma_ne_zero hGs)
        ((differentiableAt_id.sub_const 1).mul hcd.differentiableAt) hΓ,
      logDeriv_fun_mul (f := fun w : ℂ => w - 1) (g := fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s
        (sub_ne_zero.mpr hs1) hc0 (differentiableAt_id.sub_const 1) hcd.differentiableAt]
    have e1 : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
      rw [logDeriv_apply]; simp
    have e2 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s =
        -(Real.log Real.pi : ℂ) / 2 := by
      rw [logDeriv_apply, hcd.deriv, ← Complex.ofReal_log Real.pi_pos.le]
      field_simp
    have e3 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2 + 1)) s =
        Complex.digamma (s / 2 + 1) / 2 := by
      have hg : HasDerivAt (fun w : ℂ => w / 2 + 1) (1 / 2) s := by
        simpa using ((hasDerivAt_id s).div_const 2).add_const 1
      rw [show (fun w : ℂ => Complex.Gamma (w / 2 + 1)) =
          Complex.Gamma ∘ (fun w : ℂ => w / 2 + 1) from rfl,
        logDeriv_comp (g := fun w : ℂ => w / 2 + 1) (Complex.differentiableAt_Gamma _ hGs)
          hg.differentiableAt, hg.deriv, Complex.digamma_def]
      ring
    rw [e1, e2, e3]; ring
  have hL3 := Complex.logDeriv_eq_add_tsum_of_eq_exp_mul_tprod hz0
    (summable_norm_rpow_neg_two hz) hAB hzero (differentiable_riemannXi s) hxis
  rw [hL1, hL3, hL2]
  ring

end RiemannXi

open RiemannXi in
/-- **`ζ` has infinitely many zeros in the critical strip.** -/
theorem riemannZetaNontrivialZeros_infinite : riemannZetaNontrivialZeros.Infinite := by
  have h := Complex.setOf_eq_zero_infinite_of_hasGrowthOrderLE_one differentiable_riemannXi
    hasGrowthOrderLE_riemannXi (by simp) not_isBigO_riemannXi_exp_mul_norm
  convert h using 1
  ext s
  exact (riemannXi_eq_zero_iff s).symm
