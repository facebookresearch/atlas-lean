/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.EisensteinCongruence
public import MathlibExt.NumberTheory.ModularForms.FrickeGamma0
public import MathlibExt.NumberTheory.ModularForms.LevelOneTrace

@[expose] public section

open scoped MatrixGroups ModularForm

/-- Consumer with the original binders: the Eisenstein congruence forces `p ∤ m`. -/
private theorem exactSource (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m)
    (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ)
    (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n)
    (h1 : IsCoprime (af 1) (m : ℤ))
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (ModularForm.sigmaPrimeTo p n : ℤ) * af 1) :
    ¬ (p ∣ m) :=
  CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf h1 hcongr

/-- Consumer with the original binders: the weight-four divisibility. -/
example (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2)
    (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (ModularForm.sigmaPrimeTo p n : ℤ) * af 1) :
    (24 * m : ℤ) ∣ 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) :=
  CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr

/-- Consumer with the original binders: the weight-six divisibility. -/
example (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2)
    (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (ModularForm.sigmaPrimeTo p n : ℤ) * af 1) :
    (24 * m : ℤ) ∣ 504 * (af 1) ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1) :=
  CuspForm.dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr

/-- Consumer with the original binders: the level-one trace through `U_p` and Fricke. -/
example (p : ℕ) [Fact p.Prime] (k : ℤ) (X : ModularForm (CongruenceSubgroup.Gamma0 p) k)
    (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![0, -1; (p : ℝ), 0]) :
    ∃ Y : ModularForm 𝒮ℒ k, ⇑Y = (p : ℂ) ^ (k - 2) • ⇑X + ModularForm.heckeU k p (⇑X ∣[k] W) :=
  ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p k X W hW

/-- Consumer with the original binders: the weight-two Eisenstein form on `Γ₀(p)`. -/
example (p : ℕ) [Fact p.Prime] :
    ∃ E : ModularForm (CongruenceSubgroup.Gamma0 p) 2, ∀ n : ℕ,
      ModularFormClass.qCoeff E n = (ModularForm.eisensteinTwoCoeff p n : ℂ) :=
  ModularForm.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff p

/-- Boundary example for `σ'_p`: the divisors `2` and `6` of `6` are dropped for `p = 2`,
so `σ'_2(6) = 1 + 3`, not `σ(6) = 12`. -/
example : ModularForm.sigmaPrimeTo 2 6 = 4 := by decide

/-- Boundary example: the constant term `p - 1` is not `24 σ'_p(0) = 0`. -/
example : ModularForm.eisensteinTwoCoeff 5 0 = 4 ∧ ModularForm.eisensteinTwoCoeff 5 5 = 24 := by
  refine ⟨by simp [ModularForm.eisensteinTwoCoeff_zero], ?_⟩
  rw [ModularForm.eisensteinTwoCoeff_of_ne_zero 5 (by norm_num)]
  decide

/-- The Fricke operator on weight-two forms is an involution. -/
example (N : ℕ) [NeZero N] (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) :
    ⇑(ModularForm.fricke N 2 f) ∣[(2 : ℤ)] ModularForm.frickeGL N = ⇑f := by
  rw [ModularForm.coe_fricke_slash_frickeGL]
  norm_num
