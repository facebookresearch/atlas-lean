/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
public import MathlibExt.NumberTheory.SelbergClass.Primitive
public import MathlibExt.NumberTheory.SelbergClass.RankinSelberg
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet
import MathlibExt.NumberTheory.LSeries.RiemannXiHadamard
import MathlibExt.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.SelbergClass.Degree
import MathlibExt.NumberTheory.SelbergClass.Factorization

/-!
# The Riemann zeta function in the Selberg class

The Riemann zeta function, with coefficients `ζ n = 1` for `n ≥ 1`, is the basic member of the
Selberg class: its Euler logarithm is `Λ n / log n`, its functional equation has one Gamma factor
`Γ(s/2)` (so degree `1`), and `(s - 1) ζ(s) = ξ(s) π^{s/2} / Γ(s/2 + 1)` is entire of order `1`.
Being of degree `1`, it is primitive; and since `ζ ⊗ ζ̄ = ζ`, it is `⊗`-simple.

## Main definitions

* `SelbergClass.zetaLog`: the Euler logarithm `Λ n / log n` of `ζ`.
* `SelbergClass.FunctionalEquation.riemannZeta`: the functional equation of `ζ`, with
  `Q = π^{-1/2}`, one Gamma factor `Γ(s/2)` and `w = 1`.

## Main statements

* `SelbergClass.FunctionalEquation.degree_riemannZeta`: it has degree `1`.
* `ArithmeticFunction.zeta_mem_selbergClass`: `ζ` is in the Selberg class.
* `ArithmeticFunction.isSelbergPrimitive_zeta`: `ζ` is primitive.
* `ArithmeticFunction.isTensorSimple_zeta`: `ζ` is `⊗`-simple.
-/

open Complex Filter Asymptotics Bornology
open scoped ArithmeticFunction.zeta

@[expose] public section

namespace Complex

/-- Composing a function of order at most `ρ` with the affine map `z ↦ z / 2 + 1` keeps the
order at most `ρ`. -/
theorem HasGrowthOrderLE.comp_div_two_add_one {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
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

end Complex

namespace ArithmeticFunction

/-- The complex coefficients of `ζ` are not those of the constant function `1`. -/
theorem natCoe_zeta_ne_one : (ζ : ArithmeticFunction ℂ) ≠ 1 := by
  intro h
  have := congrArg (fun f : ArithmeticFunction ℂ => f 2) h
  simp at this

/-- `riemannZeta` is the continuation of the Dirichlet series `∑ n^{-s}`. -/
theorem isLSeriesContinuation_zeta :
    IsLSeriesContinuation (ζ : ArithmeticFunction ℂ) riemannZeta := by
  refine ⟨fun s hs => ?_, fun s hs =>
    (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt⟩
  rw [← LSeries_zeta_eq_riemannZeta hs]
  rfl

end ArithmeticFunction

namespace SelbergClass

open ArithmeticFunction

/-- The Euler logarithm of `ζ`: `zetaLog n = Λ n / log n`. -/
noncomputable def zetaLog (n : ℕ) : ℂ := (Λ n : ℂ) / (Real.log n : ℂ)

theorem zetaLog_zero : zetaLog 0 = 0 := by simp [zetaLog]

theorem norm_zetaLog_le_one (n : ℕ) : ‖zetaLog n‖ ≤ 1 := by
  rw [zetaLog, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
    abs_of_nonneg (Real.log_natCast_nonneg n)]
  exact div_le_one_of_le₀ vonMangoldt_le_log (Real.log_natCast_nonneg n)

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

private theorem norm_zetaLog_le_rpow {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ‖zetaLog n‖ ≤ 1 * (n : ℝ) ^ ε := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [zetaLog_zero, Real.zero_rpow hε.ne']
  · rw [one_mul]
    exact (norm_zetaLog_le_one n).trans (Real.one_le_rpow (by exact_mod_cast hn) hε.le)

/-- The Rankin–Selberg logarithm of `ζ ⊗ ζ̄` is that of `ζ`: `k · (1/k) · (1/k) = 1/k`. -/
theorem tensorLog_zetaLog_conj :
    tensorLog zetaLog (fun n => starRingEnd ℂ (zetaLog n)) = zetaLog := by
  funext n
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hn
    rw [tensorLog_prime_pow _ _ hp hk.ne', zetaLog_prime_pow hp hk.ne']
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [map_div₀, map_one, map_natCast]
    field_simp
  · rw [tensorLog_of_not_isPrimePow _ _ hn, eq_comm, zetaLog, div_eq_zero_iff]
    left
    exact_mod_cast vonMangoldt_eq_zero_iff.mpr hn

/-! ### The functional equation -/

private theorem cpow_pi_neg_half (s : ℂ) :
    (((Real.pi ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) ^ s = (Real.pi : ℂ) ^ (-s / 2) := by
  rw [ofReal_cpow Real.pi_pos.le, ← cpow_mul]
  · congr 1; push_cast; ring
  · rw [← ofReal_log Real.pi_pos.le, ← ofReal_mul, ofReal_im]; linarith [Real.pi_pos]
  · rw [← ofReal_log Real.pi_pos.le, ← ofReal_mul, ofReal_im]; exact Real.pi_pos.le

private theorem completed_eq (s : ℂ) (hs : 0 < s.re) :
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

/-- **The functional equation of `ζ`** in Selberg form: `Q = π^{-1/2}`, one Gamma factor with
`α = 1/2` and `r = 0`, and `w = 1`, so that `Φ(s) = Γℝ(s) ζ(s)` is the completed zeta
function. -/
noncomputable def FunctionalEquation.riemannZeta : FunctionalEquation _root_.riemannZeta where
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

/-- The functional equation of `ζ` has degree `1`. -/
theorem FunctionalEquation.degree_riemannZeta : FunctionalEquation.riemannZeta.degree = 1 := by
  change 2 * ∑ _i : Fin 1, (1 / 2 : ℝ) = 1
  norm_num

/-! ### Finite order of `(s - 1) ζ(s)` -/

private theorem hasGrowthOrderLE_pi_cpow :
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
private noncomputable def zetaG (s : ℂ) : ℂ :=
  RiemannXi.riemannXi s * (Real.pi : ℂ) ^ (s / 2) * (1 / Gamma (s / 2 + 1))

private theorem differentiable_zetaG : Differentiable ℂ zetaG := by
  have h1 := RiemannXi.differentiable_riemannXi
  have h2 : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ (s / 2) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h3 : Differentiable ℂ fun s : ℂ => 1 / Gamma (s / 2 + 1) := by
    simpa [Function.comp_def] using
      differentiable_one_div_Gamma.comp ((differentiable_id.div_const 2).add_const 1)
  exact (h1.mul h2).mul h3

private theorem hasGrowthOrderLE_zetaG : HasGrowthOrderLE zetaG 1 := by
  have h3 : HasGrowthOrderLE (fun s : ℂ => 1 / Gamma (s / 2 + 1)) 1 := by
    have := hasGrowthOrder_inv_Gamma.hasGrowthOrderLE.comp_div_two_add_one zero_le_one
    simpa only [one_div] using this
  exact (RiemannXi.hasGrowthOrderLE_riemannXi.mul hasGrowthOrderLE_pi_cpow).mul h3

private theorem zetaG_eq (s : ℂ) (hs1 : s ≠ 1) : zetaG s = (s - 1) ^ 1 * _root_.riemannZeta s := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp [zetaG, RiemannXi.riemannXi_zero, riemannZeta_zero]
    norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs2 : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  rw [zetaG, RiemannXi.riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0, Gammaℝ_def, Gamma_add_one _ hs2, neg_div, cpow_neg, pow_one]
  by_cases hG : Gamma (s / 2) = 0
  · simp [hG]
  · field_simp

end SelbergClass

namespace ArithmeticFunction

open SelbergClass

/-- The Euler logarithm of `ζ` is `Λ n / log n`. -/
theorem isEulerLog_zeta : IsEulerLog (ζ : ArithmeticFunction ℂ) zetaLog := by
  refine ⟨fun n h => vonMangoldt_ne_zero_iff.mp fun h0 => h (by simp [zetaLog, h0]),
    fun s hs => ⟨LSeriesSummable.of_forall_norm_le_mul_rpow
      (fun ε hε => ⟨1, norm_zetaLog_le_rpow hε⟩) hs, ?_⟩⟩
  rw [← isLSeriesContinuation_zeta.1 s hs, ← riemannZeta_eq_exp_LSeries hs]
  rfl

/-- **The Riemann zeta function is in the Selberg class.** -/
theorem zeta_mem_selbergClass : (ζ : ArithmeticFunction ℂ) ∈ selbergClass := by
  refine ⟨by simp, ⟨riemannZeta, isLSeriesContinuation_zeta,
    ⟨1, zetaG, 1, differentiable_zetaG, hasGrowthOrderLE_zetaG, zetaG_eq⟩,
      ⟨FunctionalEquation.riemannZeta⟩⟩,
    ⟨zetaLog, 0, by norm_num, isEulerLog_zeta, 1, fun n => by
      simpa using norm_zetaLog_le_one n⟩, fun ε hε => ⟨1, fun n => ?_⟩⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  · simpa [hn.ne'] using Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε.le

/-- **`ζ` is primitive.** A factorisation `ζ = b c` with `b, c ≠ 1` would give
`1 = deg ζ = deg b + deg c ≥ 2`. -/
theorem isSelbergPrimitive_zeta : IsSelbergPrimitive (ζ : ArithmeticFunction ℂ) := by
  refine ⟨zeta_mem_selbergClass, natCoe_zeta_ne_one, fun b hb c hc h => ?_⟩
  by_contra hbc
  push Not at hbc
  obtain ⟨_, ⟨Fb, hFb, _, ⟨Db⟩⟩, _⟩ := id hb
  obtain ⟨_, ⟨Fc, hFc, _, ⟨Dc⟩⟩, _⟩ := id hc
  have hF : IsLSeriesContinuation (b * c) riemannZeta := h ▸ isLSeriesContinuation_zeta
  have hdeg := FunctionalEquation.degree_eq_add_of_mul b c hb hc Fb Fc riemannZeta hFb hFc hF
    Db Dc FunctionalEquation.riemannZeta
  have h1 := one_le_degree_of_ne_one hb hbc.1 hFb Db
  have h2 := one_le_degree_of_ne_one hc hbc.2 hFc Dc
  rw [FunctionalEquation.degree_riemannZeta] at hdeg
  linarith

/-- **`ζ` is `⊗`-simple**, since `ζ ⊗ ζ̄ = ζ` has a simple pole at `s = 1`. -/
theorem isTensorSimple_zeta : IsTensorSimple (ζ : ArithmeticFunction ℂ) := by
  refine ⟨zeta_mem_selbergClass, zetaLog, isEulerLog_zeta, riemannZeta, fun s hs => ?_, ?_,
    meromorphicOrderAt_riemannZeta_one⟩
  · rw [tensor, tensorLog_zetaLog_conj, ← (isEulerLog_zeta.2 s hs).2,
      isLSeriesContinuation_zeta.1 s hs]
  · exact (isLSeriesContinuation_zeta.2.analyticOnNhd isOpen_compl_singleton).mono
      fun s hs => hs.2

end ArithmeticFunction
