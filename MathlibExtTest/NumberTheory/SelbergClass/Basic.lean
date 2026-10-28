/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
public import MathlibExt.NumberTheory.LSeries.RiemannXiHadamard
public import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for the Selberg class

Non-vacuity of `ArithmeticFunction.selbergClass`: the constant function `1` and the Riemann zeta
function (coefficients `ζ n = 1` for `n ≥ 1`) belong to `𝒮`, while `2 ζ` (wrong normalisation)
and `1 + 6^{-s}` (no Euler product) do not.

The membership proof for `ζ` is exported as `SelbergClassTest.zeta_mem_selbergClass`, together
with the functional equation `SelbergClassTest.zetaFE` of degree `1`, for use in the other
Selberg-class test files.
-/

open Complex ArithmeticFunction SelbergClass Filter Asymptotics Bornology

@[expose] public section

namespace SelbergClassTest

/-! ### `IsLSeriesContinuation`, `IsEulerLog`, `FunctionalEquation` for the function `1` -/

/-- The trivial functional equation of the constant function `1`: no Gamma factors,
`Q = 1`, `w = 1`. -/
noncomputable def oneFE : FunctionalEquation (fun _ : ℂ => (1 : ℂ)) where
  d := 0
  Q := 1
  α := fun i => i.elim0
  r := fun i => i.elim0
  w := 1
  Q_pos := one_pos
  α_pos := fun i => i.elim0
  r_re_nonneg := fun i => i.elim0
  norm_w := by simp
  eqn := fun s _ _ => by simp

example : oneFE.degree = 0 := by
  unfold FunctionalEquation.degree
  rw [Finset.sum_eq_zero fun i _ => i.elim0, mul_zero]

theorem isLSeriesContinuation_one :
    IsLSeriesContinuation (1 : ArithmeticFunction ℂ) (fun _ => 1) := by
  refine ⟨fun s _ => ?_, differentiableOn_const _⟩
  have h : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
    funext n
    simp [one_apply, LSeries.delta]
  rw [h, LSeries_delta]
  rfl

theorem isEulerLog_one : IsEulerLog (1 : ArithmeticFunction ℂ) 0 := by
  refine ⟨fun n h => absurd rfl h, fun s hs => ⟨LSeriesSummable_zero, ?_⟩⟩
  rw [isLSeriesContinuation_one.1 s hs |>.symm]
  simp [LSeries_zero]

/-- **The constant function `1` is in the Selberg class.** -/
theorem one_mem_selbergClass : (1 : ArithmeticFunction ℂ) ∈ selbergClass := by
  refine ⟨one_one, ⟨fun _ => 1, isLSeriesContinuation_one,
    ⟨0, fun _ => 1, 0, differentiable_const _, hasGrowthOrderLE_const _ _, fun s _ => by simp⟩,
    ⟨oneFE⟩⟩, ⟨0, 0, by norm_num, isEulerLog_one, 0, fun n => by simp⟩, ?_⟩
  intro ε hε
  refine ⟨1, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  · have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hn) hε.le
    by_cases hn1 : n = 1
    · subst hn1; simp
    · simp [one_apply, hn1]; linarith

/-! ### The Riemann zeta function -/

/-- The coefficients of `ζ(s) = ∑ n^{-s}`, as a complex arithmetic function. -/
noncomputable abbrev zetaC : ArithmeticFunction ℂ := (ArithmeticFunction.zeta : ArithmeticFunction ℂ)

theorem zetaC_apply (n : ℕ) : zetaC n = if n = 0 then 0 else 1 := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zetaC, natCoe_apply, zeta_apply, *]

example : zetaC 0 = 0 := by simp
example : zetaC 1 = 1 := by simp
example : zetaC 12 = 1 := by simp

theorem zetaC_ne_one : zetaC ≠ 1 := by
  intro h
  have := congrArg (fun f : ArithmeticFunction ℂ => f 2) h
  simp [one_apply] at this

theorem isLSeriesContinuation_zeta : IsLSeriesContinuation zetaC riemannZeta := by
  refine ⟨fun s hs => ?_, fun s hs =>
    (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt⟩
  rw [← LSeries_zeta_eq_riemannZeta hs]
  rfl

/-- `ζ` has no continuation equal to `0`: the continuation is pinned down on `Re s > 1`. -/
example : ¬ IsLSeriesContinuation zetaC (fun _ => 0) := by
  intro h
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have e1 := h.1 2 h2
  rw [isLSeriesContinuation_zeta.1 2 h2 |>.symm] at e1
  exact riemannZeta_ne_zero_of_one_lt_re h2 e1.symm

/-- The Euler logarithm of `ζ`: `b n = Λ n / log n`. -/
noncomputable def zetaLog (n : ℕ) : ℂ := (Λ n : ℂ) / (Real.log n : ℂ)

theorem norm_zetaLog_le_one (n : ℕ) : ‖zetaLog n‖ ≤ 1 := by
  rw [zetaLog, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
    abs_of_nonneg (Real.log_natCast_nonneg n)]
  exact div_le_one_of_le₀ vonMangoldt_le_log (Real.log_natCast_nonneg n)

theorem zetaLog_zero : zetaLog 0 = 0 := by simp [zetaLog]

theorem norm_zetaLog_le_rpow {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ‖zetaLog n‖ ≤ 1 * (n : ℝ) ^ ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zetaLog_zero, Real.zero_rpow hε.ne']
  · rw [one_mul]
    exact (norm_zetaLog_le_one n).trans (Real.one_le_rpow (by exact_mod_cast hn) hε.le)

theorem isEulerLog_zeta : IsEulerLog zetaC zetaLog := by
  refine ⟨fun n h => vonMangoldt_ne_zero_iff.mp fun h0 => h (by simp [zetaLog, h0]),
    fun s hs => ⟨LSeriesSummable_of_forall_norm_le_mul_rpow
      (fun ε hε => ⟨1, norm_zetaLog_le_rpow hε⟩) hs, ?_⟩⟩
  rw [← isLSeriesContinuation_zeta.1 s hs, ← riemannZeta_eq_exp_LSeries hs]
  rfl

/-- At prime powers the Euler logarithm of `ζ` is `1 / k`. -/
theorem zetaLog_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    zetaLog (p ^ k) = 1 / k := by
  have hlog : Real.log p ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
    (by exact_mod_cast hp.pos) (by exact_mod_cast hp.one_lt.ne')
  rw [zetaLog, vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have : (Real.log p : ℂ) ≠ 0 := by exact_mod_cast hlog
  push_cast
  field_simp
  rw [div_self]
  rw [← Complex.natCast_log]
  exact this

/-- `IsEulerLog.apply_prime` at `ζ`: `b p = a p = 1`. -/
example : zetaLog 7 = 1 := by
  simpa using zetaLog_prime_pow (p := 7) (k := 1) (by norm_num) one_ne_zero

/-- The Riemann functional equation in Selberg form: `d = 1`, `Q = π^{-1/2}`, `α = 1/2`,
`r = 0`, `w = 1`, so that `Φ(s) = Γℝ(s) ζ(s)` is the completed zeta function. -/
theorem cpow_pi_neg_half (s : ℂ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) ^ s = (Real.pi : ℂ) ^ (-s / 2) := by
  rw [ofReal_cpow Real.pi_pos.le, ← cpow_mul]
  · congr 1; push_cast; ring
  · rw [← ofReal_log Real.pi_pos.le]; simp; positivity
  · rw [← ofReal_log Real.pi_pos.le]; simp; positivity

theorem completed_eq (s : ℂ) (hs : 0 < s.re) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) ^ s *
        (∏ _i : Fin 1, Gamma (((1 / 2 : ℝ) : ℂ) * s + 0)) * riemannZeta s =
      completedRiemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [cpow_pi_neg_half, riemannZeta_def_of_ne_zero hs0, Fin.prod_univ_one]
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [Gammaℝ_def] at hG
  have : ((1 / 2 : ℝ) : ℂ) * s + 0 = s / 2 := by push_cast; ring
  rw [this, Gammaℝ_def]
  have hG' : Gamma (s / 2) ≠ 0 := right_ne_zero_of_mul hG
  field_simp

/-- The functional equation of `ζ`, of degree `1`. -/
noncomputable def zetaFE : FunctionalEquation riemannZeta where
  d := 1
  Q := Real.pi ^ (-(1 / 2 : ℝ))
  α := fun _ => 1 / 2
  r := fun _ => 0
  w := 1
  Q_pos := by positivity
  α_pos := fun _ => by norm_num
  r_re_nonneg := fun _ => by simp
  norm_w := by simp
  eqn := fun s h0 h1 => by
    have h1' : 0 < (1 - starRingEnd ℂ s).re := by simp; linarith
    rw [completed_eq s h0, completed_eq _ h1', completedRiemannZeta_one_sub,
      completedRiemannZeta_conj, Complex.conj_conj, one_mul]

theorem zetaFE_degree : zetaFE.degree = 1 := by
  show 2 * ∑ _i : Fin 1, (1 / 2 : ℝ) = 1
  norm_num

/-! #### Finite order of `(s - 1) ζ(s)` -/

theorem hasGrowthOrderLE_comp_half_add_one {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : HasGrowthOrderLE f ρ) : HasGrowthOrderLE (fun z => f (z / 2 + 1)) ρ := by
  intro ε hε
  have hlow : ∀ z : ℂ, ‖z‖ / 2 - 1 ≤ ‖z / 2 + 1‖ := by
    intro z
    have h := norm_sub_le (z / 2 + 1) 1
    simp only [add_sub_cancel_right, norm_div, norm_one, Complex.norm_ofNat] at h
    linarith
  have ht : Tendsto (fun z : ℂ => z / 2 + 1) (cobounded ℂ) (cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine tendsto_atTop_mono hlow ?_
    exact tendsto_atTop_add_const_right _ _
      (tendsto_norm_cobounded_atTop.atTop_div_const two_pos)
  refine ((hf ε hε).comp_tendsto ht).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop 2] with z hz
  simp only [Function.comp_apply, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  gcongr
  have h := norm_add_le (z / 2) 1
  simp only [norm_div, norm_one, Complex.norm_ofNat] at h
  linarith

theorem hasGrowthOrderLE_pi_cpow :
    HasGrowthOrderLE (fun s : ℂ => (Real.pi : ℂ) ^ (s / 2)) 1 := by
  refine hasGrowthOrderLE_one_of_isBigO_exp_mul_norm (A := 2) (IsBigO.of_bound 1 ?_)
  refine Eventually.of_forall fun s => ?_
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Real.rpow_def_of_pos Real.pi_pos, Real.exp_le_exp]
  have hl0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hl3 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  have hre : (s / 2).re ≤ ‖s‖ / 2 := by
    simp only [div_ofNat_re]; linarith [Complex.re_le_norm s]
  nlinarith [norm_nonneg s]

/-- The entire function `ξ(s) π^{s/2} / Γ(s/2 + 1)`, equal to `(s - 1) ζ(s)` off `s = 1`. -/
noncomputable def zetaG (s : ℂ) : ℂ :=
  RiemannXi.riemannXi s * (Real.pi : ℂ) ^ (s / 2) * (1 / Gamma (s / 2 + 1))

theorem differentiable_zetaG : Differentiable ℂ zetaG := by
  have h1 := RiemannXi.differentiable_riemannXi
  have h2 : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ (s / 2) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h3 : Differentiable ℂ fun s : ℂ => 1 / Gamma (s / 2 + 1) := by
    simpa [Function.comp_def] using
      differentiable_one_div_Gamma.comp ((differentiable_id.div_const 2).add_const 1)
  exact (h1.mul h2).mul h3

theorem hasGrowthOrderLE_zetaG : HasGrowthOrderLE zetaG 1 := by
  have h3 : HasGrowthOrderLE (fun s : ℂ => 1 / Gamma (s / 2 + 1)) 1 := by
    have := hasGrowthOrderLE_comp_half_add_one zero_le_one hasGrowthOrder_inv_Gamma.1
    simpa only [one_div] using this
  exact (RiemannXi.hasGrowthOrderLE_riemannXi.mul hasGrowthOrderLE_pi_cpow).mul h3

theorem zetaG_eq (s : ℂ) (hs1 : s ≠ 1) : zetaG s = (s - 1) ^ 1 * riemannZeta s := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [zetaG, RiemannXi.riemannXi_zero, riemannZeta_zero]
    norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hP : (Real.pi : ℂ) ^ (s / 2) ≠ 0 := by
    rw [cpow_def_of_ne_zero hpi]; exact exp_ne_zero _
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  rw [zetaG, RiemannXi.riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0, Gammaℝ_def, Gamma_add_one _ hs2, neg_div, cpow_neg, pow_one]
  by_cases hG : Gamma (s / 2) = 0
  · simp [hG]
  · field_simp

/-- **The Riemann zeta function is in the Selberg class.** -/
theorem zeta_mem_selbergClass : zetaC ∈ selbergClass := by
  refine ⟨by simp, ⟨riemannZeta, isLSeriesContinuation_zeta,
    ⟨1, zetaG, 1, differentiable_zetaG, hasGrowthOrderLE_zetaG, zetaG_eq⟩, ⟨zetaFE⟩⟩,
    ⟨zetaLog, 0, by norm_num, isEulerLog_zeta, 1, fun n => by
      simpa using norm_zetaLog_le_one n⟩, fun ε hε => ⟨1, fun n => ?_⟩⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  · simpa [hn.ne'] using Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε.le

/-! ### Non-members -/

/-- Wrong normalisation: `2 ζ` is not in `𝒮` since its first coefficient is `2`. -/
example : (2 : ℂ) • zetaC ∉ selbergClass := fun h => by
  have := h.1
  simp at this

theorem not_isPrimePow_six : ¬ IsPrimePow 6 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, hpk⟩
  have h2 : 2 ∣ p ^ k := hpk ▸ (by norm_num : 2 ∣ 6)
  have h3 : 3 ∣ p ^ k := hpk ▸ (by norm_num : 3 ∣ 6)
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

/-- `F(s) = 1 + 6^{-s}`: entire, coefficients bounded, but not multiplicative. -/
def oneAddSix : ArithmeticFunction ℂ := ⟨fun n => if n = 1 ∨ n = 6 then 1 else 0, by simp⟩

/-- `1 + 6^{-s}` has no Euler logarithm (hence is not in `𝒮`): comparing coefficients of
`log n · a n = ((log · b) ⍟ a) n` at `n = 6` gives `log 6 = 0`. -/
theorem not_isEulerLog_oneAddSix (b : ℕ → ℂ) : ¬ IsEulerLog oneAddSix b := by
  intro hb
  have haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => oneAddSix n) s :=
    fun s hs => LSeriesSummable_of_forall_norm_le_mul_rpow (fun ε hε => ⟨1, fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [Real.zero_rpow hε.ne']
      · have := Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε.le
        show ‖(if n = 1 ∨ n = 6 then (1 : ℂ) else 0)‖ ≤ _
        split_ifs <;> simp <;> linarith⟩) hs
  have h := hb.logMul_eq_convolution haS (n := 6) (by norm_num)
  have h6 : b 6 = 0 := by
    by_contra h0
    exact not_isPrimePow_six (hb.1 6 h0)
  have hd : Nat.divisorsAntidiagonal 6 = {(1, 6), (2, 3), (3, 2), (6, 1)} := by decide
  rw [LSeries.convolution_def] at h
  beta_reduce at h
  rw [hd] at h
  simp [LSeries.logMul, oneAddSix, h6, Finset.sum_insert, Finset.sum_singleton] at h
  have : Real.log 6 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  exact this (by exact_mod_cast h)

example : oneAddSix ∉ selbergClass := fun h => by
  obtain ⟨b, -, -, hb, -⟩ := h.2.2.1
  exact not_isEulerLog_oneAddSix b hb

/-! ### API -/

/-- `IsEulerLog.unique`: the Euler logarithm of `ζ` is `Λ / log`. -/
example (b : ℕ → ℂ) (hb : IsEulerLog zetaC b) : b = zetaLog :=
  IsEulerLog.unique (by simp) (fun _ hs => LSeriesSummable_of_mem
    zeta_mem_selbergClass hs) hb isEulerLog_zeta

/-- `IsLSeriesContinuation.eqOn_compl_one` -/
example (F : ℂ → ℂ) (hF : IsLSeriesContinuation zetaC F) (s : ℂ) (hs : s ≠ 1) :
    F s = riemannZeta s :=
  hF.eqOn_compl_one isLSeriesContinuation_zeta s hs

/-- `meromorphicAt_one` at `ζ`. -/
example : MeromorphicAt riemannZeta 1 :=
  meromorphicAt_one zeta_mem_selbergClass isLSeriesContinuation_zeta

/-- `FunctionalEquation.eq_of_re_lt_one` at `ζ`, `s = -1`. -/
example : riemannZeta (-1) = (zetaFE.Q : ℂ) ^ (-(-1 : ℂ)) *
      (∏ i, (Gamma (zetaFE.α i * (-1) + zetaFE.r i))⁻¹) *
      (zetaFE.w * starRingEnd ℂ ((zetaFE.Q : ℂ) ^ (1 - starRingEnd ℂ (-1)) *
        (∏ i, Gamma (zetaFE.α i * (1 - starRingEnd ℂ (-1)) + zetaFE.r i)) *
          riemannZeta (1 - starRingEnd ℂ (-1)))) :=
  zetaFE.eq_of_re_lt_one isLSeriesContinuation_zeta.2 _ (by norm_num) (by norm_num)

example : (1 : ArithmeticFunction ℂ) ≠ zetaC := zetaC_ne_one.symm

end SelbergClassTest
