/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
public import MathlibExt.NumberTheory.SelbergClass.RiemannZeta
public import MathlibExt.Analysis.SpecialFunctions.Gamma.Binet
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the Selberg class

Non-vacuity of `ArithmeticFunction.selbergClass`: the constant function `1` and the Riemann zeta
function (coefficients `ζ n = 1` for `n ≥ 1`) belong to `𝒮`, while `2 ζ` (wrong normalisation)
and `1 + 6^{-s}` (no Euler product) do not.

The membership of `ζ` and its functional equation live in
`MathlibExt.NumberTheory.SelbergClass.RiemannZeta`; here they are only instantiated.
-/

open Complex ArithmeticFunction SelbergClass

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

theorem oneFE_degree : oneFE.degree = 0 := by
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
noncomputable abbrev zetaC : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ)

theorem zetaC_apply (n : ℕ) : zetaC n = if n = 0 then 0 else 1 := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zetaC, natCoe_apply, zeta_apply, *]

example : zetaC 0 = 0 := by simp
example : zetaC 1 = 1 := by simp
example : zetaC 12 = 1 := by simp

theorem not_isPrimePow_six : ¬ IsPrimePow 6 := by
  rw [isPrimePow_nat_iff]
  rintro ⟨p, k, hp, hk, hpk⟩
  have h2 : 2 ∣ p ^ k := hpk ▸ (by norm_num : 2 ∣ 6)
  have h3 : 3 ∣ p ^ k := hpk ▸ (by norm_num : 3 ∣ 6)
  have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow h2)
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem zetaC_ne_one : zetaC ≠ 1 := natCoe_zeta_ne_one

/-- `ζ` has no continuation equal to `0`: the continuation is pinned down on `Re s > 1`. -/
example : ¬ IsLSeriesContinuation zetaC (fun _ => 0) := by
  intro h
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have e1 := h.1 2 h2
  rw [isLSeriesContinuation_zeta.1 2 h2 |>.symm] at e1
  exact riemannZeta_ne_zero_of_one_lt_re h2 e1.symm

example (n : ℕ) : ‖zetaLog n‖ ≤ 1 := norm_zetaLog_le_one n

/-- `IsEulerLog.apply_prime` at `ζ`: `b p = a p = 1`. -/
example : zetaLog 7 = 1 := by
  simpa using zetaLog_prime_pow (p := 7) (k := 1) (by norm_num) one_ne_zero

example : zetaLog 8 = 1 / 3 := by
  simpa using zetaLog_prime_pow (p := 2) (k := 3) Nat.prime_two (by norm_num)

example : zetaLog 6 = 0 := by
  simp [zetaLog, vonMangoldt_eq_zero_iff.mpr not_isPrimePow_six]

/-- The functional equation `FunctionalEquation.riemannZeta` of `ζ`, abbreviated for the tests. -/
noncomputable abbrev zetaFE : FunctionalEquation riemannZeta := FunctionalEquation.riemannZeta

theorem zetaFE_degree : zetaFE.degree = 1 := FunctionalEquation.degree_riemannZeta

/-- The functional equation of `ζ` has one Gamma factor `Γ(s/2)` and `w = 1`. -/
example : zetaFE.d = 1 ∧ zetaFE.Q = Real.pi ^ (-(1 / 2 : ℝ)) ∧ zetaFE.w = 1 ∧
    ∀ i, zetaFE.α i = 1 / 2 ∧ zetaFE.r i = 0 :=
  ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- **The Riemann zeta function is in the Selberg class.** -/
example : zetaC ∈ selbergClass := zeta_mem_selbergClass

/-- `Complex.HasGrowthOrderLE.comp_div_two_add_one` at `1 / Γ`. -/
example : Complex.HasGrowthOrderLE (fun z => (Gamma (z / 2 + 1))⁻¹) 1 :=
  Complex.hasGrowthOrder_inv_Gamma.hasGrowthOrderLE.comp_div_two_add_one zero_le_one

/-! ### Non-members -/

/-- Wrong normalisation: `2 ζ` is not in `𝒮` since its first coefficient is `2`. -/
example : (2 : ℂ) • zetaC ∉ selbergClass := fun h => by
  have := h.1
  simp at this

/-- `F(s) = 1 + 6^{-s}`: entire, coefficients bounded, but not multiplicative. -/
def oneAddSix : ArithmeticFunction ℂ := ⟨fun n => if n = 1 ∨ n = 6 then 1 else 0, by simp⟩

/-- `1 + 6^{-s}` has no Euler logarithm (hence is not in `𝒮`): comparing coefficients of
`log n · a n = ((log · b) ⍟ a) n` at `n = 6` gives `log 6 = 0`. -/
theorem not_isEulerLog_oneAddSix (b : ℕ → ℂ) : ¬ IsEulerLog oneAddSix b := by
  intro hb
  have haS : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => oneAddSix n) s :=
    fun s hs => LSeriesSummable.of_forall_norm_le_mul_rpow (fun ε hε => ⟨1, fun n => by
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
