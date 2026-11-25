/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.PeriodMapHecke

@[expose] public section

/-- The weight-two period map intertwines the analytic Hecke operator `T_ℓ`
with the cohomological Hecke operator, for a prime `ℓ` not dividing the
level. This is the statement of `ModularCurve.periodMap_heckeTLin` with its
source form preserved. -/
private theorem exactSource {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) :=
  ModularCurve.periodMap_heckeTLin hℓ hℓN f

/-- The same intertwining identity stated as a plain equation, with the
`NeZero ℓ` instance supplied by the caller. -/
example {N : ℕ} {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) :=
  ModularCurve.periodMap_heckeTLin hℓ hℓN f

open ModularForm

/-! The `p = 0` convention: the matrices are the identity, `U_0 = 0` and `T_0 = id`. -/

example (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

example (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by simp [heckeU]

example (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by simp [heckeT, heckeU]

/-! Values on explicit functions: `U_p f τ = p⁻¹ ∑_{j < p} f ((τ + j) / p)` and
`T_p f τ = U_p f τ + p ^ (k - 1) f (p τ)`. -/

/-- `U_3` of the coordinate function `τ ↦ τ` in weight two. -/
example (τ : UpperHalfPlane) :
    heckeU 2 3 (fun z : UpperHalfPlane => (z : ℂ)) τ = (τ : ℂ) / 3 + 1 / 3 := by
  simp only [heckeU_apply 2 three_ne_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    coe_heckeMatrix_smul three_ne_zero]
  push_cast
  ring

/-- `T_2` of the coordinate function in weight two: `(τ + 1/2) / 2 + 2 * (2 τ)`. -/
example (τ : UpperHalfPlane) :
    heckeT 2 2 (fun z : UpperHalfPlane => (z : ℂ)) τ = 9 / 2 * (τ : ℂ) + 1 / 4 := by
  simp only [heckeT_apply 2 two_ne_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    coe_heckeMatrix_smul two_ne_zero, coe_heckeDiagMatrix_smul two_ne_zero]
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

/-! The Hecke operators on cusp forms act by `heckeT` and `heckeU` on the underlying
functions. -/

example {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ⇑(CuspForm.heckeTLin 2 hp hpN f) = heckeT 2 p ⇑f := rfl

example {N p : ℕ} [NeZero N] (hpN : p ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ⇑(CuspForm.heckeULin 2 hpN f) = heckeU 2 p ⇑f := rfl
