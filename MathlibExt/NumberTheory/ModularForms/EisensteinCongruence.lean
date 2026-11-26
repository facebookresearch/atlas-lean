/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo.lean`,
`Theorems/Thm_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo.lean`,
`Theorems/Thm_CuspForm_dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo.lean`,
`Theorems/Thm_CuspForm_exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo.lean`,
`Theorems/Thm_ModularForm_levelOne_weight_four_qCoeff_one.lean`,
`Theorems/Thm_ModularForm_levelOne_weight_six_qCoeff_one.lean`,
`P2M/Sol/S_CuspForm_not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo.lean`,
`P2M/Sol/S_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo.lean`,
`P2M/Sol/S_CuspForm_dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo.lean`,
`P2M/Sol/S_CuspForm_exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo.lean`,
`P2M/Sol/S_ModularForm_levelOne_weight_four_qCoeff_one.lean` and
`P2M/Sol/S_ModularForm_levelOne_weight_six_qCoeff_one.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.EisensteinTwoGamma0
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.QExpansion
import MathlibExt.NumberTheory.ModularForms.FrickeGamma0
import MathlibExt.NumberTheory.ModularForms.HeckeOperator
import MathlibExt.NumberTheory.ModularForms.LevelOneTrace
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

/-!
# Weight-two cusp forms congruent to the Eisenstein series of level `Γ₀(p)`

Let `p` be a prime and `f` a weight-two cusp form on `Γ₀(p)` with integral
`q`-coefficients `a n`. Suppose that for some `m ≥ 2` and all `n ≥ 1`,
`a n ≡ σ'_p(n) a 1 (mod m)`, where `σ'_p(n)` is the sum of the divisors of `n`
prime to `p`. Subtracting `24 f` from `a 1` times the weight-two Eisenstein form on
`Γ₀(p)` gives a modular form whose non-constant coefficients are divisible by `24 m`.
Multiplying it with its Fricke transform (in weights four and six) and taking the
trace to level one, the level-one identities `a₁ = 240 a₀` (weight four) and
`a₁ = -504 a₀` (weight six) give

* `24 m ∣ 240 (a 1)² (p - 1)² (p + 1)` and
* `24 m ∣ 504 (a 1)³ (p - 1)³ (p² - 1)`.

When `a 1` is prime to `m`, these force `p ∤ m`
(`CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo`).

## References

* B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977), 33–186,
  Chapter II, §5: the Eisenstein series of (5.1) and (5.2), and Proposition (5.12), which shows
  for primes `N ≥ 5`, with a different argument, that `∑ σ'(n) qⁿ` is not a holomorphic modular
  form of weight two on `Γ₀(N)` modulo `N`.
-/

@[expose] public section

open CongruenceSubgroup UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularForm

/-- A level-one modular form of weight four has first `q`-coefficient `240` times its
constant term. -/
theorem levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) :
    qCoeff ⇑Y 1 = 240 * qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • E₄ = Y :=
    (finrank_eq_one_iff_of_ne_zero' E₄ (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) Y
  have hq : qExpansion 1 ⇑Y = c • qExpansion 1 ⇑E₄ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c E₄,
      show (c • ⇑E₄) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (qExpansion 1 ⇑E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  rw [qCoeff_eq, qCoeff_eq, hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul,
    smul_eq_mul, h0, E₄_qExpansion_coeff_one]
  ring

/-- A level-one modular form of weight six has first `q`-coefficient `-504` times its
constant term. -/
theorem levelOne_weight_six_qCoeff_one (Y : ModularForm 𝒮ℒ 6) :
    qCoeff ⇑Y 1 = -504 * qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • E₆ = Y :=
    (finrank_eq_one_iff_of_ne_zero' E₆ (EisensteinSeries.E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_six_rank_one) Y
  have hq : qExpansion 1 ⇑Y = c • qExpansion 1 ⇑E₆ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c E₆,
      show (c • ⇑E₆) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (qExpansion 1 ⇑E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  rw [qCoeff_eq, qCoeff_eq, hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul,
    smul_eq_mul, h0, E₆_qExpansion_coeff_one]
  ring

namespace EisensteinCongruence

variable {p : ℕ}

private theorem hΓ0 (p : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  one_mem_strictPeriods_Gamma0 p

/-- `f` has integral `q`-coefficients with constant term `a₀`, all others divisible
by `M`. -/
private def IntCoeffs (f : ℍ → ℂ) (M a₀ : ℤ) : Prop :=
  ∃ a : ℕ → ℤ, (∀ n, (a n : ℂ) = qCoeff f n) ∧ a 0 = a₀ ∧ ∀ n, n ≠ 0 → M ∣ a n

private theorem IntCoeffs.mul {a b : ℤ} {X : ModularForm (Gamma0 p) a}
    {Z : ModularForm (Gamma0 p) b} {M x₀ z₀ : ℤ} (hX : IntCoeffs X M x₀)
    (hZ : IntCoeffs Z M z₀) : IntCoeffs (X.mul Z) M (x₀ * z₀) := by
  obtain ⟨aX, haX, hX0, hXd⟩ := hX
  obtain ⟨aZ, haZ, hZ0, hZd⟩ := hZ
  refine ⟨fun n => ∑ ij ∈ Finset.antidiagonal n, aX ij.1 * aZ ij.2, fun n => ?_, ?_,
    fun n hn => Finset.dvd_sum fun ij hij => ?_⟩
  · rw [qCoeff_eq, ModularForm.qExpansion_mul one_pos (hΓ0 p), PowerSeries.coeff_mul]
    push_cast
    simp only [haX, haZ, qCoeff_eq]
  · simp [hX0, hZ0]
  · rw [Finset.mem_antidiagonal] at hij
    by_cases h1 : ij.1 = 0
    · exact dvd_mul_of_dvd_right (hZd _ fun h2 => hn (by rw [← hij, h1, h2])) _
    · exact dvd_mul_of_dvd_left (hXd _ h1) _

private theorem IntCoeffs.mcast {a b : ℤ} (h : a = b) {X : ModularForm (Gamma0 p) a}
    {M x₀ : ℤ} (hX : IntCoeffs X M x₀) : IntCoeffs (ModularForm.mcast h X rfl) M x₀ :=
  hX

variable [Fact p.Prime]

private theorem hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

private instance : NeZero p := ⟨hp0⟩

/-- Slashing the Fricke transform of a weight-two form by the Fricke matrix gives the
form back. -/
private theorem fricke_slash (X : ModularForm (Gamma0 p) 2) :
    ⇑(fricke p 2 X) ∣[(2 : ℤ)] frickeGL p = ⇑X := by
  rw [coe_fricke_slash_frickeGL]
  norm_num

/-- In weight two, `X ∣ W_p + U_p X` is a level-one form of weight two, hence zero. -/
private theorem heckeU_eq_neg_fricke (X : ModularForm (Gamma0 p) 2) :
    heckeU 2 p ⇑X = -⇑(fricke p 2 X) := by
  obtain ⟨Y, hY⟩ := exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p 2
    (fricke p 2 X) (frickeGL p) (val_frickeGL p)
  have hY0 : Y = 0 := rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero Y
  rw [hY0, fricke_slash, sub_self, zpow_zero, one_smul] at hY
  exact eq_neg_of_add_eq_zero_right (by simpa using hY.symm)

private theorem qCoeff_fricke (X : ModularForm (Gamma0 p) 2) (n : ℕ) :
    qCoeff ⇑(fricke p 2 X) n = -qCoeff ⇑X (n * p) := by
  have h1 := qCoeff_heckeU X (hΓ0 p) (hp0 (p := p)) n
  rw [coeffHeckeU_apply, heckeU_eq_neg_fricke, qCoeff_eq, qCoeff_eq] at h1
  rw [qCoeff_eq, qCoeff_eq, ← h1, UpperHalfPlane.qExpansion_neg
    (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos (hΓ0 p)), map_neg, neg_neg]

private theorem IntCoeffs.fricke {X : ModularForm (Gamma0 p) 2} {M x₀ : ℤ}
    (hX : IntCoeffs X M x₀) : IntCoeffs (fricke p 2 X) M (-x₀) := by
  obtain ⟨a, ha, h0, hd⟩ := hX
  refine ⟨fun n => -a (n * p), fun n => ?_, by simp [h0], fun n hn =>
    dvd_neg.mpr (hd _ (mul_ne_zero hn hp0))⟩
  push_cast
  rw [ha, qCoeff_fricke]

/-- The trace to level one of `H` with `H ∣ W_p = c • L`. -/
private theorem exists_levelOne_qCoeff {k : ℤ} (H L : ModularForm (Gamma0 p) k) (c : ℂ)
    (hHW : ⇑H ∣[k] frickeGL p = c • ⇑L) :
    ∃ Y : ModularForm 𝒮ℒ k, ∀ n : ℕ,
      qCoeff ⇑Y n = (p : ℂ) ^ (k - 2) * qCoeff ⇑H n + c * qCoeff ⇑L (n * p) := by
  obtain ⟨Y, hY⟩ := exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p k H
    (frickeGL p) (val_frickeGL p)
  refine ⟨Y, fun n => ?_⟩
  have hlaw := qCoeff_heckeU (c • L) (hΓ0 p) (hp0 (p := p)) n
  rw [coeffHeckeU_apply] at hlaw
  have hU : heckeU k p ⇑(c • L) = ⇑Y - (p : ℂ) ^ (k - 2) • ⇑H := by
    rw [hY, hHW, FunLike.coe_smul]
    abel
  rw [hU] at hlaw
  have hYa := ModularFormClass.analyticAt_cuspFunction_zero Y one_pos one_mem_strictPeriods_SL
  have hsHa : AnalyticAt ℂ (cuspFunction 1 ((p : ℂ) ^ (k - 2) • ⇑H)) 0 := by
    have h := ModularFormClass.analyticAt_cuspFunction_zero ((p : ℂ) ^ (k - 2) • H) one_pos
      (hΓ0 p)
    rwa [FunLike.coe_smul] at h
  have hHa := ModularFormClass.analyticAt_cuspFunction_zero H one_pos (hΓ0 p)
  have e1 : qExpansion 1 (⇑Y - (p : ℂ) ^ (k - 2) • ⇑H)
      = qExpansion 1 ⇑Y - (p : ℂ) ^ (k - 2) • qExpansion 1 ⇑H := by
    rw [UpperHalfPlane.qExpansion_sub hYa hsHa, UpperHalfPlane.qExpansion_smul hHa]
  have e2 : qExpansion 1 ⇑(c • L) = c • qExpansion 1 ⇑L := by
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (hΓ0 p)]
  rw [qCoeff_eq, qCoeff_eq, e1, e2] at hlaw
  simp only [map_sub, map_smul, smul_eq_mul] at hlaw
  rw [qCoeff_eq, qCoeff_eq, qCoeff_eq]
  linear_combination hlaw

private theorem mul_slash_frickeGL {a b : ℤ} (f g : ℍ → ℂ) :
    (f * g) ∣[a + b] frickeGL p = (p : ℂ) • (f ∣[a] frickeGL p * g ∣[b] frickeGL p) := by
  rw [mul_slash, det_frickeGL, Nat.abs_cast]
  ext τ
  simp

end EisensteinCongruence

end ModularForm

namespace CuspForm

open ModularForm ModularForm.EisensteinCongruence

/-- Let `p` be prime and `f` a weight-two cusp form on `Γ₀(p)` whose `q`-coefficients `a n` are
integers. If `a n ≡ σ'_p(n) a 1 (mod m)` for all `n ≥ 1`, where `σ'_p(n)` is the sum of the
divisors of `n` not divisible by `p`, then some weight-two modular form on `Γ₀(p)` has integral
`q`-coefficients, constant term `a 1 (p - 1)`, and all other coefficients divisible by
`24 m`. -/
theorem exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime]
    (f : CuspForm (Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    ∃ (F : ModularForm (Gamma0 p) 2) (aF : ℕ → ℤ), (∀ n : ℕ, (aF n : ℂ) = qCoeff F n) ∧
      aF 0 = af 1 * ((p : ℤ) - 1) ∧ ∀ n : ℕ, n ≠ 0 → ((24 * m : ℕ) : ℤ) ∣ aF n := by
  obtain ⟨EE, hEE⟩ := exists_modularForm_qCoeff_eq_eisensteinTwoCoeff p
  have hΓ := one_mem_strictPeriods_Gamma0 p
  have haf0 : af 0 = 0 := by
    have h0 : qCoeff f 0 = 0 := by
      rw [qCoeff_eq]
      exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
    have h1 := haf 0
    rw [h0] at h1
    exact_mod_cast h1
  have hq : ∀ n : ℕ, qCoeff ⇑((af 1 : ℂ) • EE - (24 : ℂ) • (f : ModularForm (Gamma0 p) 2)) n
      = (af 1 : ℂ) * qCoeff EE n - 24 * qCoeff f n := by
    intro n
    have hA : AnalyticAt ℂ (cuspFunction 1 ((af 1 : ℂ) • (EE : ℍ → ℂ))) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero ((af 1 : ℂ) • EE) one_pos hΓ
    have hB : AnalyticAt ℂ (cuspFunction 1 ((24 : ℂ) • (f : ℍ → ℂ))) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero
        ((24 : ℂ) • (f : ModularForm (Gamma0 p) 2)) one_pos hΓ
    have hE0 := ModularFormClass.analyticAt_cuspFunction_zero EE one_pos hΓ
    have hf0 : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
      ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
    change (qExpansion 1 ((af 1 : ℂ) • (EE : ℍ → ℂ) - (24 : ℂ) • (f : ℍ → ℂ))).coeff n
      = (af 1 : ℂ) * qCoeff EE n - 24 * qCoeff f n
    rw [UpperHalfPlane.qExpansion_sub hA hB, UpperHalfPlane.qExpansion_smul hE0,
      UpperHalfPlane.qExpansion_smul hf0, qCoeff_eq, qCoeff_eq]
    simp [smul_eq_mul]
  refine ⟨(af 1 : ℂ) • EE - (24 : ℂ) • (f : ModularForm (Gamma0 p) 2),
    fun n => af 1 * eisensteinTwoCoeff p n - 24 * af n, fun n => ?_, ?_, fun n hn => ?_⟩
  · rw [hq n, hEE n, ← haf n]
    push_cast
    ring
  · simp only [eisensteinTwoCoeff_zero, haf0]
    ring
  · obtain ⟨c, hc⟩ := hcongr n hn
    refine ⟨-c, ?_⟩
    beta_reduce
    rw [eisensteinTwoCoeff_of_ne_zero p hn]
    push_cast
    linear_combination (-24 : ℤ) * hc

private theorem intCoeffs_of_qCoeff_congr (p m : ℕ) [Fact p.Prime]
    (f : CuspForm (Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    ∃ F : ModularForm (Gamma0 p) 2, IntCoeffs F (24 * m) (af 1 * ((p : ℤ) - 1)) := by
  obtain ⟨F, aF, haF, h0, hd⟩ :=
    exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo p m f af haf hcongr
  exact ⟨F, aF, haF, h0, fun n hn => by exact_mod_cast hd n hn⟩

/-- Let `p` be prime, `m ≥ 2`, and `f` a weight-two cusp form on `Γ₀(p)` whose `q`-coefficients
`a n` are integers. If `a n ≡ σ'_p(n) a 1 (mod m)` for all `n ≥ 1`, where `σ'_p(n)` is the sum of
the divisors of `n` not divisible by `p`, then `24 m` divides `240 (a 1)² (p - 1)² (p + 1)`. -/
theorem dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (f : CuspForm (Gamma0 p) 2) (af : ℕ → ℤ)
    (haf : ∀ n : ℕ, (af n : ℂ) = qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    (24 * m : ℤ) ∣ 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) := by
  have _ := hm
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨F, hF⟩ := intCoeffs_of_qCoeff_congr p m f af haf hcongr
  set G := fricke p 2 F
  set H := ModularForm.mcast (by norm_num : (2 : ℤ) + 2 = 4) (F.mul G) rfl
  obtain ⟨aH, haH, haH0, hdH⟩ := (hF.mul hF.fricke).mcast (by norm_num : (2 : ℤ) + 2 = 4)
  have hHW : ⇑H ∣[(4 : ℤ)] frickeGL p = (p : ℂ) • ⇑H := by
    change (⇑F * ⇑G) ∣[(2 : ℤ) + 2] frickeGL p = (p : ℂ) • (⇑F * ⇑G)
    rw [mul_slash_frickeGL, fricke_slash, mul_comm]
    rfl
  obtain ⟨Y, hY⟩ := exists_levelOne_qCoeff H H _ hHW
  have hWL := levelOne_weight_four_qCoeff_one Y
  rw [hY 1, hY 0, one_mul, zero_mul, ← haH 1, ← haH p, ← haH 0,
    show (4 : ℤ) - 2 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at hWL
  have hZ : (p : ℤ) ^ 2 * aH 1 + (p : ℤ) * aH p
      = 240 * ((p : ℤ) ^ 2 * aH 0 + (p : ℤ) * aH 0) := by
    exact_mod_cast hWL
  rw [haH0] at hZ
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hT : 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1)
      = -((p : ℤ) * aH 1 + aH p) := by
    refine mul_left_cancel₀ hpZ ?_
    linear_combination hZ
  rw [hT]
  exact dvd_neg.mpr (dvd_add (dvd_mul_of_dvd_right (hdH 1 one_ne_zero) _) (hdH p hp0))

/-- Let `p` be prime, `m ≥ 2`, and `f` a weight-two cusp form on `Γ₀(p)` whose `q`-coefficients
`a n` are integers. If `a n ≡ σ'_p(n) a 1 (mod m)` for all `n ≥ 1`, where `σ'_p(n)` is the sum of
the divisors of `n` not divisible by `p`, then `24 m` divides `504 (a 1)³ (p - 1)³ (p² - 1)`. -/
theorem dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (f : CuspForm (Gamma0 p) 2) (af : ℕ → ℤ)
    (haf : ∀ n : ℕ, (af n : ℂ) = qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    (24 * m : ℤ) ∣ 504 * (af 1) ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1) := by
  have _ := hm
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨F, hF⟩ := intCoeffs_of_qCoeff_congr p m f af haf hcongr
  set G := fricke p 2 F
  have h6 : (2 : ℤ) + 2 + 2 = 6 := by norm_num
  set K := ModularForm.mcast h6 ((F.mul F).mul G) rfl
  set L := ModularForm.mcast h6 ((F.mul G).mul G) rfl
  obtain ⟨aK, haK, haK0, hdK⟩ := ((hF.mul hF).mul hF.fricke).mcast h6
  obtain ⟨aL, haL, haL0, hdL⟩ := ((hF.mul hF.fricke).mul hF.fricke).mcast h6
  have hKW : ⇑K ∣[(6 : ℤ)] frickeGL p = ((p : ℂ) ^ 2) • ⇑L := by
    change (⇑F * ⇑F * ⇑G) ∣[(2 : ℤ) + 2 + 2] frickeGL p = ((p : ℂ) ^ 2) • (⇑F * ⇑G * ⇑G)
    rw [mul_slash_frickeGL, mul_slash_frickeGL, fricke_slash, ← coe_fricke]
    ext τ
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  obtain ⟨Y, hY⟩ := exists_levelOne_qCoeff K L _ hKW
  have hWL := levelOne_weight_six_qCoeff_one Y
  rw [hY 1, hY 0, one_mul, zero_mul, ← haK 1, ← haL p, ← haK 0, ← haL 0,
    show (6 : ℤ) - 2 = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at hWL
  have hZ : (p : ℤ) ^ 4 * aK 1 + (p : ℤ) ^ 2 * aL p
      = -504 * ((p : ℤ) ^ 4 * aK 0 + (p : ℤ) ^ 2 * aL 0) := by
    exact_mod_cast hWL
  rw [haK0, haL0] at hZ
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hT : 504 * (af 1) ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1)
      = (p : ℤ) ^ 2 * aK 1 + aL p := by
    refine mul_left_cancel₀ hp2 ?_
    linear_combination -hZ
  rw [hT]
  exact dvd_add (dvd_mul_of_dvd_right (hdK 1 one_ne_zero) _) (hdL p hp0)

private theorem false_of_isCoprime_of_prime_dvd (p : ℕ) (hp : p.Prime) (a1 : ℤ)
    (h1 : IsCoprime a1 (p : ℤ))
    (h4 : 24 * (p : ℤ) ∣ 240 * a1 ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1))
    (h6 : 24 * (p : ℤ) ∣ 504 * a1 ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1)) :
    False := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hunit : ∀ {x : ℤ}, (p : ℤ) ∣ x → (p : ℤ) ∣ x - 1 → False := fun hx hx1 =>
    hpz.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_sub hx hx1))
  have ha1 : ¬ (p : ℤ) ∣ a1 := fun h => hpz.not_isUnit (h1.isUnit_of_dvd' h dvd_rfl)
  have hm1 : ¬ (p : ℤ) ∣ (p : ℤ) - 1 := hunit dvd_rfl
  have hp1 : ¬ (p : ℤ) ∣ (p : ℤ) + 1 := fun h => hunit h (by simp)
  have hsq : ¬ (p : ℤ) ∣ (p : ℤ) ^ 2 - 1 := hunit (dvd_pow_self _ two_ne_zero)
  have h4' : (p : ℤ) ∣ 10 * a1 ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) := by
    rw [show (240 : ℤ) * a1 ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1)
        = 24 * (10 * a1 ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1)) by ring] at h4
    exact (mul_dvd_mul_iff_left (by norm_num : (24 : ℤ) ≠ 0)).mp h4
  have h6' : (p : ℤ) ∣ 21 * a1 ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1) := by
    rw [show (504 : ℤ) * a1 ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1)
        = 24 * (21 * a1 ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1)) by ring] at h6
    exact (mul_dvd_mul_iff_left (by norm_num : (24 : ℤ) ≠ 0)).mp h6
  have h10 : (p : ℤ) ∣ 10 := by
    rcases hpz.2.2 _ _ h4' with h | h
    · rcases hpz.2.2 _ _ h with h | h
      · rcases hpz.2.2 _ _ h with h | h
        · exact h
        · exact absurd (hpz.dvd_of_dvd_pow h) ha1
      · exact absurd (hpz.dvd_of_dvd_pow h) hm1
    · exact absurd h hp1
  have h21 : (p : ℤ) ∣ 21 := by
    rcases hpz.2.2 _ _ h6' with h | h
    · rcases hpz.2.2 _ _ h with h | h
      · rcases hpz.2.2 _ _ h with h | h
        · exact h
        · exact absurd (hpz.dvd_of_dvd_pow h) ha1
      · exact absurd (hpz.dvd_of_dvd_pow h) hm1
    · exact absurd h hsq
  exact hpz.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_sub (dvd_sub h21 h10) h10))

/-- Let `p` be prime, `m ≥ 2`, and `f` a weight-two cusp form on `Γ₀(p)` whose `q`-coefficients
`a n` are integers, with `a 1` prime to `m`. If `a n ≡ σ'_p(n) a 1 (mod m)` for all `n ≥ 1`, where
`σ'_p(n)` is the sum of the divisors of `n` not divisible by `p`, then `p` does not divide
`m`. -/
theorem not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m)
    (f : CuspForm (Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = qCoeff f n)
    (h1 : IsCoprime (af 1) (m : ℤ))
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    ¬ (p ∣ m) := by
  intro hpm
  have h4 := dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr
  have h6 := dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr
  have hcast : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
  have hdvd : 24 * (p : ℤ) ∣ 24 * (m : ℤ) := mul_dvd_mul_left 24 hcast
  exact false_of_isCoprime_of_prime_dvd p Fact.out (af 1) (h1.of_isCoprime_of_dvd_right hcast)
    (hdvd.trans h4) (hdvd.trans h6)

end CuspForm
