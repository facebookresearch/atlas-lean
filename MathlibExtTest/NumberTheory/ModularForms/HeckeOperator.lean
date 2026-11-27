/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

@[expose] public section

open ModularForm

/-! The `p = 0` convention: the matrices are the identity, `U_0 = 0` and `T_0 = id`. -/

example (j : ℕ) : heckeUpperMatrix 0 j = 1 := by simp [heckeUpperMatrix]

example (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by simp [heckeU]

example (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by simp [heckeT, heckeU]

/-! Values on explicit functions: `U_p f τ = p⁻¹ ∑_{j < p} f ((τ + j) / p)` and
`T_p f τ = U_p f τ + p ^ (k - 1) f (p τ)`. -/

/-- `U_3` of the coordinate function `τ ↦ τ` in weight two. -/
example (τ : UpperHalfPlane) :
    heckeU 2 3 (fun z : UpperHalfPlane => (z : ℂ)) τ = (τ : ℂ) / 3 + 1 / 3 := by
  simp only [heckeU_apply 2 three_ne_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    coe_heckeUpperMatrix_smul three_ne_zero]
  push_cast
  ring

/-- `T_2` of the coordinate function in weight two: `(τ + 1/2) / 2 + 2 * (2 τ)`. -/
example (τ : UpperHalfPlane) :
    heckeT 2 2 (fun z : UpperHalfPlane => (z : ℂ)) τ = 9 / 2 * (τ : ℂ) + 1 / 4 := by
  simp only [heckeT_apply 2 two_ne_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    coe_heckeUpperMatrix_smul two_ne_zero, coe_heckeDiagMatrix_smul two_ne_zero]
  push_cast
  norm_num
  ring

/-- `T_2` of the constant `1` in weight four is `1 + 2 ^ 3`. -/
example (τ : UpperHalfPlane) : heckeT 4 2 (fun _ : UpperHalfPlane => (1 : ℂ)) τ = 9 := by
  simp only [heckeT_apply 4 two_ne_zero, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! The coefficient formulas, on the coefficients `a n = n`:
`coeffHeckeT k p a n = a (n p) + [p ∣ n] p ^ (k - 1) a (n / p)` and
`coeffHeckeU p a n = a (n p)`. -/

example : coeffHeckeT 2 3 (fun n => (n : ℂ)) 3 = 12 := by norm_num [coeffHeckeT]

example : coeffHeckeT 2 3 (fun n => (n : ℂ)) 2 = 6 := by norm_num [coeffHeckeT]

example : coeffHeckeT 4 2 (fun n => (n : ℂ)) 2 = 12 := by norm_num [coeffHeckeT]

example : coeffHeckeU 3 (fun n => (n : ℂ)) 2 = 6 := by norm_num [coeffHeckeU]

/-! The `q`-expansion coefficients of `T_p f` and `U_p f`, for a cusp form `f` on `Γ₀(N)`. -/

/-- The first coefficient of `T_p f` is the `p`-th coefficient of `f`, for a prime `p`. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) :
    ModularFormClass.qCoeff (heckeT k p ⇑f) 1 = ModularFormClass.qCoeff ⇑f p := by
  rw [ModularFormClass.qCoeff_heckeT f (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
    hp.ne_zero, coeffHeckeT_of_not_dvd k hp.not_dvd_one, one_mul]

/-- The `p`-th coefficient of `T_p f` is `a (p * p) + p ^ (k - 1) * a 1`. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) :
    ModularFormClass.qCoeff (heckeT k p ⇑f) p
      = ModularFormClass.qCoeff ⇑f (p * p) + (p : ℂ) ^ (k - 1) * ModularFormClass.qCoeff ⇑f 1 := by
  rw [ModularFormClass.qCoeff_heckeT f (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
    hp.ne_zero, coeffHeckeT_of_dvd k dvd_rfl, Nat.div_self hp.pos]

/-- The `n`-th coefficient of `U_p f` is the `n * p`-th coefficient of `f`. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p ≠ 0)
    (n : ℕ) : ModularFormClass.qCoeff (heckeU k p ⇑f) n = ModularFormClass.qCoeff ⇑f (n * p) :=
  ModularFormClass.qCoeff_heckeU f (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) hp n

/-! Regularity at `i∞` of `T_p f` and `U_p f`, for a cusp form `f` on `Γ₀(N)`, through the
public lemmas of `HeckeOperator`. -/

example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (p : ℕ) :
    Function.Periodic (heckeT k p ⇑f ∘ UpperHalfPlane.ofComplex) 1 :=
  periodic_heckeT_comp_ofComplex k p (SlashInvariantFormClass.periodic_comp_ofComplex f
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N))

example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (p : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (heckeU k p ⇑f) :=
  have : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)⟩
  isBoundedAtImInfty_heckeU k p (ModularFormClass.bdd_at_infty f)

/-- Translating by `1` permutes the points `(τ + j) / 3`, `j < 3`, up to a translate by `1`,
which a `1`-periodic function does not see. -/
example {f : UpperHalfPlane → ℂ}
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range 3, f (heckeUpperMatrix 3 j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range 3, f (heckeUpperMatrix 3 j • τ) :=
  sum_heckeUpperMatrix_smul_vadd three_ne_zero hf τ

/-! The Hecke operators on cusp forms act by `heckeT` and `heckeU` on the underlying
functions. -/

example {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ⇑(CuspForm.heckeTLin 2 hp hpN f) = heckeT 2 p ⇑f := rfl

example {N p : ℕ} [NeZero N] (hpN : p ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ⇑(CuspForm.heckeULin 2 hpN f) = heckeU 2 p ⇑f := rfl
