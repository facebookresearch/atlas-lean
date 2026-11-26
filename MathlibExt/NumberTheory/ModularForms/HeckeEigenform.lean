/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_finiteDimensional_Gamma0.lean`,
`Theorems/Thm_CuspForm_qCoeff_zero.lean`,
`Theorems/Thm_ModularFormClass_heckeT_eq_smul_iff.lean`,
`Theorems/Thm_ModularFormClass_heckeU_eq_smul_iff.lean`,
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean`,
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeT.lean`,
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin.lean`,
`Theorems/Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean`,
`Theorems/Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean`,
`Theorems/Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean`,
`Theorems/Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul.lean`,
`P2M/Sol/S_CuspForm_finiteDimensional_Gamma0.lean`,
`P2M/Sol/S_CuspForm_qCoeff_zero.lean`,
`P2M/Sol/S_ModularFormClass_heckeT_eq_smul_iff.lean`,
`P2M/Sol/S_ModularFormClass_heckeU_eq_smul_iff.lean`,
`P2M/Sol/S_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean`,
`P2M/Sol/S_CuspForm_isNormalizedEigenform_iff_heckeT.lean`,
`P2M/Sol/S_CuspForm_isNormalizedEigenform_iff_heckeTLin.lean`,
`P2M/Sol/S_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean`,
`P2M/Sol/S_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean`,
`P2M/Sol/S_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean`, and
`P2M/Sol/S_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.NumberTheory.ModularForms.PeriodMapHecke

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector
import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0
import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0

/-!
# Normalized Hecke eigenforms of weight two on `Γ₀(N)`

This file shows that the space of cusp forms on `Γ₀(N)` is finite-dimensional, characterizes
normalized Hecke eigenforms of weight two through their Hecke eigenvalues, and shows that a
nonzero weight-two cusp form that is an eigenvector of the Hecke operators `T_ℓ` for almost all
primes `ℓ ∤ N` gives rise to a normalized eigenform with the same eigenvalues.

## Main statements

* `CuspForm.finiteDimensional_Gamma0`: cusp forms on `Γ₀(N)`, `N ≠ 0`, form a
  finite-dimensional complex vector space.
* `ModularFormClass.heckeT_eq_smul_iff`, `ModularFormClass.heckeU_eq_smul_iff`: being a Hecke
  eigenvector is a condition on `q`-coefficients.
* `CuspForm.isNormalizedEigenform_iff_coeffHecke`, `CuspForm.isNormalizedEigenform_iff_heckeT`,
  `CuspForm.isNormalizedEigenform_iff_heckeTLin`: normalized eigenforms are the cusp forms with
  first coefficient `1` that are eigenvectors of every `T_p` and `U_p`, with eigenvalue `a_p`.
* `ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one`,
  `ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero`: eigenvalues of a coefficient
  sequence, and vanishing when its first coefficient vanishes.
* `CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul`: a nonzero simultaneous
  eigenvector of almost all `T_ℓ` yields a normalized eigenform with the same eigenvalues.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane Function
open scoped MatrixGroups ModularForm Manifold

/-! ### Finite dimensionality -/

namespace CuspForm

private def truncC (N : ℕ) (k : ℤ) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ]
      (Fin ((k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 + 1) → ℂ) where
  toFun f i := (qExpansion 1 (f : ℍ → ℂ)).coeff i
  map_add' f g := by
    funext i
    simp only [FunLike.coe_add, Pi.add_apply]
    rw [ModularForm.qExpansion_add one_pos
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) f g, map_add]
  map_smul' c f := by
    funext i
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [ModularForm.qExpansion_smul one_pos
      (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) c f, map_smul, smul_eq_mul]

private theorem truncC_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (truncC N k) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  have hmf : (ModularFormClass.modularForm f :
      ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 N _ fun n hn ↦ ?_
    have hcoeff := congrFun hf ⟨n, Nat.lt_succ_of_le hn⟩
    simpa [truncC] using hcoeff
  have hcoe : (f : ℍ → ℂ) = 0 := by
    have harg := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) k ↦
      (F : ℍ → ℂ)) hmf
    simpa using harg
  exact DFunLike.coe_injective (hcoe.trans (FunLike.coe_zero).symm)

/-- Cusp forms of weight `k` on `Γ₀(N)`, `N ≠ 0`, form a finite-dimensional complex vector
space: by the Sturm bound a cusp form is determined by finitely many `q`-coefficients. -/
instance finiteDimensional_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  FiniteDimensional.of_injective (truncC N k) (truncC_injective N k)

end CuspForm

/-! ### Hecke eigenvectors through `q`-coefficients -/

namespace ModularFormClass

open ModularForm

/-- A modular form `f` for a group with `1` as a strict period satisfies `T_p f = c • f`, for
`p ≠ 0`, exactly when its `q`-coefficients satisfy the corresponding eigenvalue equations. -/
theorem heckeT_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeT k p ⇑f = c • ⇑f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n
        = c * ModularFormClass.qCoeff f n := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hhol := ModularFormClass.holo f
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hbdd := bdd_at_infty f
  have hsmul (n : ℕ) : qCoeff (c • ⇑f) n = c * qCoeff f n := by
    simp [qCoeff_eq, ModularForm.qExpansion_smul one_pos hΓ c f]
  refine ⟨fun h n ↦ by rw [← ModularFormClass.qCoeff_heckeT f hΓ hp n, h, hsmul], fun h ↦ ?_⟩
  have hcper : Periodic ((c • ⇑f) ∘ ofComplex) 1 := hper.smul c
  have hTper := periodic_heckeT_comp_ofComplex k p hper
  have hThol := mdifferentiable_heckeT hhol k p
  have hTbdd := isBoundedAtImInfty_heckeT k p hbdd
  refine sub_eq_zero.mp ((qExpansion_eq_zero_iff (f := heckeT k p ⇑f - c • ⇑f) one_pos
    (by simpa using hTper.sub hcper) (hThol.sub (hhol.const_smul c))
    (hTbdd.sub (hbdd.const_smul_left c))).mp ?_)
  rw [qExpansion_sub (analyticAt_cuspFunction_zero one_pos hTper hThol hTbdd)
    (analyticAt_cuspFunction_zero one_pos hcper (hhol.const_smul c) (hbdd.const_smul_left c)),
    sub_eq_zero]
  refine PowerSeries.ext fun n ↦ ?_
  rw [← qCoeff_eq, ← qCoeff_eq, ModularFormClass.qCoeff_heckeT f hΓ hp n, h n, hsmul]

/-- A modular form `f` for a group with `1` as a strict period satisfies `U_p f = c • f`, for
`p ≠ 0`, exactly when its `q`-coefficients satisfy the corresponding eigenvalue equations. -/
theorem heckeU_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeU k p ⇑f = c • ⇑f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n
        = c * ModularFormClass.qCoeff f n := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hhol := ModularFormClass.holo f
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hbdd := bdd_at_infty f
  have hsmul (n : ℕ) : qCoeff (c • ⇑f) n = c * qCoeff f n := by
    simp [qCoeff_eq, ModularForm.qExpansion_smul one_pos hΓ c f]
  refine ⟨fun h n ↦ by rw [← ModularFormClass.qCoeff_heckeU f hΓ hp n, h, hsmul], fun h ↦ ?_⟩
  have hcper : Periodic ((c • ⇑f) ∘ ofComplex) 1 := hper.smul c
  have hUper := periodic_heckeU_comp_ofComplex k p hper
  have hUhol := mdifferentiable_heckeU hhol k p
  have hUbdd := isBoundedAtImInfty_heckeU k p hbdd
  refine sub_eq_zero.mp ((qExpansion_eq_zero_iff (f := heckeU k p ⇑f - c • ⇑f) one_pos
    (by simpa using hUper.sub hcper) (hUhol.sub (hhol.const_smul c))
    (hUbdd.sub (hbdd.const_smul_left c))).mp ?_)
  rw [qExpansion_sub (analyticAt_cuspFunction_zero one_pos hUper hUhol hUbdd)
    (analyticAt_cuspFunction_zero one_pos hcper (hhol.const_smul c) (hbdd.const_smul_left c)),
    sub_eq_zero]
  refine PowerSeries.ext fun n ↦ ?_
  rw [← qCoeff_eq, ← qCoeff_eq, ModularFormClass.qCoeff_heckeU f hΓ hp n, h n, hsmul]

end ModularFormClass

/-! ### Normalized eigenforms through Hecke eigenvalues -/

namespace CuspForm

open ModularForm

section Arithmetic

variable (a : ℕ → ℂ)

private theorem coeffHeckeT_two (p n : ℕ) :
    coeffHeckeT 2 p a n = a (n * p) + if p ∣ n then (p : ℂ) * a (n / p) else 0 := by
  rw [coeffHeckeT_apply, show (p : ℂ) ^ ((2 : ℤ) - 1) = p by norm_num]

private theorem coprime_pow_of_not_dvd {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (k : ℕ) :
    (p ^ k).Coprime m :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)

private theorem heckeT_eigen_of_rec {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r)) (n : ℕ) :
    coeffHeckeT 2 p a n = a p * a n := by
  rw [coeffHeckeT_two]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  cases r with
  | zero =>
    have hpm : ¬ p ∣ p ^ 0 * m := by simpa using hm
    rw [ite_eq_right hpm, add_zero, pow_zero, one_mul, hmul m p
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)), mul_comm]
  | succ s =>
    have hpn : p ∣ p ^ (s + 1) * m :=
      dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
    have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
      rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [ite_eq_left hpn, hdiv, show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 2)), hmul _ _ (coprime_pow_of_not_dvd hp hm s),
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 1)), hrec s]
    ring

private theorem heckeU_eigen_of_rec {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0) (h1 : a 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1))) (n : ℕ) :
    coeffHeckeU p a n = a p * a n := by
  rw [coeffHeckeU_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hstep : a (p ^ (r + 1)) = a p * a (p ^ r) := by
    cases r with
    | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
    | succ s => exact hrec s
  rw [show p ^ r * m * p = p ^ (r + 1) * m by ring,
    hmul _ _ (coprime_pow_of_not_dvd hp hm (r + 1)), hmul _ _ (coprime_pow_of_not_dvd hp hm r),
    hstep]
  ring

private theorem rec_of_heckeT_eigen {p : ℕ} (hp : p.Prime)
    (hT : ∀ n : ℕ, coeffHeckeT 2 p a n = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r) := by
  have h := hT (p ^ (r + 1))
  have hpn : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
  have hdiv : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ', Nat.mul_div_cancel_left _ hp.pos]
  rw [coeffHeckeT_two, ite_eq_left hpn, hdiv, ← pow_succ] at h
  linear_combination h

private theorem rec_of_heckeU_eigen {p : ℕ} (hU : ∀ n : ℕ, coeffHeckeU p a n = a p * a n)
    (r : ℕ) : a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) := by
  have h := hU (p ^ (r + 1))
  rwa [coeffHeckeU_apply, ← pow_succ] at h

private theorem pow_mul_of_heckeT_eigen {p : ℕ} (hp : p.Prime) (h1 : a 1 = 1)
    (hT : ∀ n : ℕ, coeffHeckeT 2 p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro m hm
    match r, ih with
    | 0, _ => rw [pow_zero, one_mul, h1, one_mul]
    | 1, _ =>
      have h := hT m
      rw [coeffHeckeT_two, ite_eq_right hm, add_zero] at h
      rw [pow_one, mul_comm p m, h]
    | s + 2, ih =>
      have h := hT (p ^ (s + 1) * m)
      have hpn : p ∣ p ^ (s + 1) * m :=
        dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
      have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
        rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
      rw [coeffHeckeT_two, ite_eq_left hpn, hdiv,
        show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
        ih (s + 1) (by omega) m hm, ih s (by omega) m hm] at h
      rw [rec_of_heckeT_eigen a hp hT s]
      linear_combination h

private theorem pow_mul_of_heckeU_eigen {p : ℕ} (h1 : a 1 = 1)
    (hU : ∀ n : ℕ, coeffHeckeU p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r with
  | zero => intro m _; rw [pow_zero, one_mul, h1, one_mul]
  | succ s ih =>
    intro m hm
    have h := hU (p ^ s * m)
    rw [coeffHeckeU_apply, show p ^ s * m * p = p ^ (s + 1) * m by ring, ih m hm] at h
    have hstep : a (p ^ (s + 1)) = a p * a (p ^ s) := by
      cases s with
      | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
      | succ t => exact rec_of_heckeU_eigen a hU t
    rw [h, hstep]
    ring

private theorem mul_of_coprime_of_pow_mul (h1 : a 1 = 1)
    (hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [Nat.coprime_zero_left] at hmn
        subst hmn
        rw [mul_one, h1, mul_one]
      · rw [one_mul, h1, one_mul]
    · have hm0 : m ≠ 0 := by omega
      have hm1 : m ≠ 1 := by omega
      set p := m.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      obtain ⟨r, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
      have hr : r ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hmeq
        exact hm' (hmeq ▸ hpm)
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero (fun h0 => hm0 (by rw [hmeq, h0, mul_zero]))
      have hm'lt : m' < m := by
        have hpr : 2 ≤ p ^ r := by
          calc 2 ≤ p := hp.two_le
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hr)
        calc m' = 1 * m' := (one_mul _).symm
          _ < p ^ r * m' := Nat.mul_lt_mul_of_pos_right (by omega) hm'pos
          _ = m := hmeq.symm
      have hpn : ¬ p ∣ n := fun hdvd =>
        hp.ne_one (Nat.eq_one_of_dvd_coprimes hmn hpm hdvd)
      have hm'n : m'.Coprime n :=
        Nat.Coprime.coprime_dvd_left (⟨p ^ r, by rw [hmeq]; ring⟩ : m' ∣ m) hmn
      have hpm'n : ¬ p ∣ m' * n := fun hdvd =>
        (hp.dvd_mul.mp hdvd).elim hm' hpn
      rw [hmeq, show p ^ r * m' * n = p ^ r * (m' * n) by ring, hpow p hp r (m' * n) hpm'n,
        ih m' hm'lt n hm'n, hpow p hp r m' hm']
      ring

end Arithmetic

open ModularFormClass in
/-- A weight-two cusp form on `Γ₀(N)` is a normalized eigenform exactly when its first
`q`-coefficient is `1` and its coefficient sequence is an eigenvector of the coefficient Hecke
operators `T_p` (for `p ∤ N`) and `U_p` (for `p ∣ N`), with eigenvalue `a_p`. -/
theorem isNormalizedEigenform_iff_coeffHecke {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔
      (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
        ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n
            = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧
          (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n
            = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n))) := by
  have h0 : qCoeff f 0 = 0 := CuspFormClass.qExpansion_coeff_zero f one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
  constructor
  · intro hf
    refine ⟨hf.qCoeff_one, fun p hp => ⟨fun hpN n => ?_, fun hpN n => ?_⟩⟩
    · exact heckeT_eigen_of_rec (qCoeff f) hp h0 hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_not_dvd p r hp hpN) n
    · exact heckeU_eigen_of_rec (qCoeff f) hp h0 hf.qCoeff_one hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_dvd p r hp hpN) n
  · rintro ⟨h1, hE⟩
    have hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m →
        qCoeff f (p ^ r * m) = qCoeff f (p ^ r) * qCoeff f m := by
      intro p hp
      by_cases hpN : p ∣ N
      · exact pow_mul_of_heckeU_eigen (qCoeff f) h1 ((hE p hp).2 hpN)
      · exact pow_mul_of_heckeT_eigen (qCoeff f) hp h1 ((hE p hp).1 hpN)
    exact
      { qCoeff_one := h1
        qCoeff_mul_of_coprime := mul_of_coprime_of_pow_mul (qCoeff f) h1 hpow
        qCoeff_prime_pow_of_not_dvd := fun p r hp hpN =>
          rec_of_heckeT_eigen (qCoeff f) hp ((hE p hp).1 hpN) r
        qCoeff_prime_pow_of_dvd := fun p r hp hpN =>
          rec_of_heckeU_eigen (qCoeff f) ((hE p hp).2 hpN) r }

/-- For `N ≠ 0`, a weight-two cusp form on `Γ₀(N)` is a normalized eigenform exactly when its
first `q`-coefficient is `1` and, for every prime `p`, `T_p f = a_p • f` if `p ∤ N` and
`U_p f = a_p • f` if `p ∣ N`, as functions on the upper half-plane. -/
theorem isNormalizedEigenform_iff_heckeT {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔
      (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
        ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧
          (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) := by
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N
  rw [isNormalizedEigenform_iff_coeffHecke]
  refine and_congr_right fun _ ↦ forall_congr' fun p ↦ forall_congr' fun hp ↦ ?_
  rw [ModularFormClass.heckeT_eq_smul_iff f hΓ hp.ne_zero,
    ModularFormClass.heckeU_eq_smul_iff f hΓ hp.ne_zero]

/-- For `N ≠ 0`, a weight-two cusp form on `Γ₀(N)` is a normalized eigenform exactly when its
first `q`-coefficient is `1` and, for every prime `p`, it is an eigenvector with eigenvalue `a_p`
of the linear Hecke operator `T_p` if `p ∤ N` and `U_p` if `p ∣ N`. -/
theorem isNormalizedEigenform_iff_heckeTLin {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
      ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
      ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f)) := by
  rw [isNormalizedEigenform_iff_heckeT]
  simp only [DFunLike.ext'_iff (f := CuspForm.heckeTLin 2 _ _ f),
    DFunLike.ext'_iff (f := CuspForm.heckeULin 2 _ f), CuspForm.coe_heckeTLin_apply,
    CuspForm.coe_heckeULin_apply, FunLike.coe_smul]

end CuspForm

/-! ### Eigenvalues of coefficient sequences -/

namespace ModularForm

/-- If a coefficient sequence `a` with `a 1 = 0` is an eigenvector of the coefficient Hecke
operators `T_p` (for `p ∤ N`) and `U_p` (for `p ∣ N`), then `a n = 0` for every `n ≠ 0`. -/
theorem eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      exact h1
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmlt : m < p * m := by nlinarith [hp.two_le]
      have ham : a m = 0 := ih m hmlt hm0
      by_cases hpN : p ∣ N
      · have h := hU p hp hpN m
        rw [ModularForm.coeffHeckeU_apply, ham, mul_zero, mul_comm m p] at h
        exact h
      · have h := hT p hp hpN m
        rw [ModularForm.coeffHeckeT_apply, ham, mul_zero, mul_comm m p] at h
        by_cases hpm : p ∣ m
        · obtain ⟨q, rfl⟩ := hpm
          have hq0 : q ≠ 0 := by rintro rfl; simp at hm0
          have hqlt : q < p * (p * q) := by
            have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
            nlinarith [hp.two_le]
          have haq : a q = 0 := ih q hqlt hq0
          rw [ite_eq_left (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos, haq, mul_zero,
            add_zero] at h
          exact h
        · rw [ite_eq_right hpm, add_zero] at h
          exact h

/-- If a coefficient sequence `a` with `a 1 = 1` is an eigenvector of the coefficient Hecke
operators `T_p` (for `p ∤ N`) and `U_p` (for `p ∣ N`) with eigenvalues `c p`, then
`c p = a p` for every prime `p`. -/
theorem coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p := by
  intro p hp
  by_cases hpN : p ∣ N
  · have h := hU p hp hpN 1
    rw [ModularForm.coeffHeckeU_apply, one_mul, h1, mul_one] at h
    exact h.symm
  · have h := hT p hp hpN 1
    rw [ModularForm.coeffHeckeT_apply, ite_eq_right hp.not_dvd_one, add_zero, one_mul, h1,
      mul_one] at h
    exact h.symm

end ModularForm

/-! ### Normalized eigenforms from simultaneous eigenvectors -/

namespace CuspForm

/-- For `N ≠ 0`, a nonzero weight-two cusp form `g` on `Γ₀(N)` with `T_ℓ g = a_ℓ • g` for every
prime `ℓ ∤ N` outside `S` gives rise to a normalized eigenform `h` with `a_ℓ(h) = a ℓ` for every
such prime `ℓ`. -/
theorem exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g ≠ 0) (a : ℕ → ℂ) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g = a ℓ • g) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ModularFormClass.qCoeff h ℓ = a ℓ := by
  classical
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N
  have qCoeff_smul : ∀ (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ),
      ModularFormClass.qCoeff ⇑(c • f) n = c * ModularFormClass.qCoeff ⇑f n := by
    intro c f n
    have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
    unfold ModularFormClass.qCoeff
    rw [FunLike.coe_smul, UpperHalfPlane.qExpansion_smul han, map_smul, smul_eq_mul]
  have qCoeff_zero' : ∀ n : ℕ,
      ModularFormClass.qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) n = 0 := by
    intro n
    have := qCoeff_smul 0 g n
    rwa [zero_smul, zero_mul] at this
  let T : Nat.Primes → Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := fun p =>
    if hpN : (p : ℕ) ∣ N then CuspForm.heckeULin 2 hpN else CuspForm.heckeTLin 2 p.2 hpN
  have hT_of_not_dvd : ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N),
      T p = CuspForm.heckeTLin 2 p.2 hpN := fun p hpN => by
    simp only [T, dite_eq_right hpN]
  have hT_of_dvd : ∀ (p : Nat.Primes) (hpN : (p : ℕ) ∣ N),
      T p = CuspForm.heckeULin 2 hpN := fun p hpN => by
    simp only [T, dite_eq_left hpN]
  have hcomm : ∀ p q : Nat.Primes, Commute (T p) (T q) := by
    intro p q
    by_cases hp : (p : ℕ) ∣ N <;> by_cases hq : (q : ℕ) ∣ N
    · rw [hT_of_dvd p hp, hT_of_dvd q hq]; exact CuspForm.heckeULin_comm 2 hp hq
    · rw [hT_of_dvd p hp, hT_of_not_dvd q hq]
      exact (CuspForm.heckeTLin_heckeULin_comm 2 q.2 hq hp).symm
    · rw [hT_of_not_dvd p hp, hT_of_dvd q hq]
      exact CuspForm.heckeTLin_heckeULin_comm 2 p.2 hp hq
    · rw [hT_of_not_dvd p hp, hT_of_not_dvd q hq]
      exact CuspForm.heckeTLin_comm 2 p.2 hp q.2 hq
  let W : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    ⨅ (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N) (_ : (ℓ : ℕ) ∉ S),
      Module.End.eigenspace (CuspForm.heckeTLin 2 ℓ.2 hℓN) (a ℓ)
  have mem_W : ∀ x, x ∈ W ↔ ∀ (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N), (ℓ : ℕ) ∉ S →
      CuspForm.heckeTLin 2 ℓ.2 hℓN x = a ℓ • x := by
    intro x
    simp only [W, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hgW : g ∈ W := (mem_W g).2 fun ℓ hℓN hℓS => hT ℓ ℓ.2 hℓN hℓS
  have hWT : ∀ (p : Nat.Primes), ∀ x ∈ W, T p x ∈ W := by
    intro p x hx
    rw [mem_W] at hx ⊢
    intro ℓ hℓN hℓS
    have hc := hcomm ℓ p
    rw [hT_of_not_dvd ℓ hℓN] at hc
    have := LinearMap.congr_fun hc.eq x
    simp only [mul_apply_eq_comp] at this
    rw [this, hx ℓ hℓN hℓS, map_smul]
  let T' : Nat.Primes → Module.End ℂ W := fun p => (T p).restrict (hWT p)
  have hcomm' : ∀ p q, Commute (T' p) (T' q) := by
    intro p q
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := LinearMap.congr_fun (hcomm p q).eq (x : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    simpa only [mul_apply_eq_comp, T', LinearMap.coe_restrict_apply] using this
  have : Nontrivial W := ⟨⟨⟨g, hgW⟩, 0, fun h => hg (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, v, hv0, hc⟩ := Module.End.exists_common_eigenvector_of_commute T' hcomm'
  set h₀ : CuspForm (CongruenceSubgroup.Gamma0 N) 2 :=
    (v : CuspForm (CongruenceSubgroup.Gamma0 N) 2) with hh₀
  have hh₀0 : h₀ ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hh₀W : h₀ ∈ W := v.2
  have hc' : ∀ p : Nat.Primes, T p h₀ = c p • h₀ := fun p => by
    have := congrArg Subtype.val (hc p)
    simpa only [T', LinearMap.coe_restrict_apply, Submodule.coe_smul] using this
  let cc : ℕ → ℂ := fun p => if hp : p.Prime then c ⟨p, hp⟩ else 0
  have hcc : ∀ (p : ℕ) (hp : p.Prime), cc p = c ⟨p, hp⟩ := fun p hp => by
    simp only [cc, dite_eq_left hp]
  have hcoeffT : ∀ (d : ℂ) (p : ℕ), p.Prime → ¬ p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff ⇑(d • h₀)) n
        = cc p * ModularFormClass.qCoeff ⇑(d • h₀) n := by
    intro d p hp hpN n
    have e := hc' ⟨p, hp⟩
    rw [hT_of_not_dvd ⟨p, hp⟩ hpN] at e
    have e2 : CuspForm.heckeTLin 2 hp hpN (d • h₀) = c ⟨p, hp⟩ • (d • h₀) := by
      rw [map_smul, e, smul_comm]
    have e3 := congrArg (fun F : CuspForm (CongruenceSubgroup.Gamma0 N) 2 =>
      ModularFormClass.qCoeff ⇑F n) e2
    simp only [CuspForm.coe_heckeTLin_apply] at e3
    rw [ModularFormClass.qCoeff_heckeT (d • h₀) hΓ hp.ne_zero n, qCoeff_smul] at e3
    rw [hcc p hp]
    exact e3
  have hcoeffU : ∀ (d : ℂ) (p : ℕ), p.Prime → p ∣ N → ∀ n : ℕ,
      ModularForm.coeffHeckeU p (ModularFormClass.qCoeff ⇑(d • h₀)) n
        = cc p * ModularFormClass.qCoeff ⇑(d • h₀) n := by
    intro d p hp hpN n
    have e := hc' ⟨p, hp⟩
    rw [hT_of_dvd ⟨p, hp⟩ hpN] at e
    have e2 : CuspForm.heckeULin 2 hpN (d • h₀) = c ⟨p, hp⟩ • (d • h₀) := by
      rw [map_smul, e, smul_comm]
    have e3 := congrArg (fun F : CuspForm (CongruenceSubgroup.Gamma0 N) 2 =>
      ModularFormClass.qCoeff ⇑F n) e2
    simp only [CuspForm.coe_heckeULin_apply] at e3
    rw [ModularFormClass.qCoeff_heckeU (d • h₀) hΓ hp.ne_zero n, qCoeff_smul] at e3
    rw [hcc p hp]
    exact e3
  have h1 : ModularFormClass.qCoeff ⇑h₀ 1 ≠ 0 := by
    intro h10
    apply hh₀0
    have hall := ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero 2 N
      (ModularFormClass.qCoeff ⇑((1 : ℂ) • h₀)) cc
      (fun p hp hpN n => hcoeffT 1 p hp hpN n) (fun p hp hpN n => hcoeffU 1 p hp hpN n)
      (by rw [one_smul]; exact h10)
    rw [one_smul] at hall
    have hq : ∀ n : ℕ, ModularFormClass.qCoeff ⇑h₀ n
        = ModularFormClass.qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) n := by
      intro n
      rw [qCoeff_zero']
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact CuspFormClass.qExpansion_coeff_zero h₀ one_pos
          (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)
      · exact hall n hn.ne'
    exact DFunLike.coe_injective <| congrArg (fun F : ModularForm _ 2 ↦ ⇑F) <|
      ModularForm.qExpansion_injective one_pos hΓ (a₁ := ModularFormClass.modularForm h₀)
        (a₂ := ModularFormClass.modularForm (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2))
        (PowerSeries.ext hq)
  set d : ℂ := (ModularFormClass.qCoeff ⇑h₀ 1)⁻¹ with hd
  set h : CuspForm (CongruenceSubgroup.Gamma0 N) 2 := d • h₀ with hhd
  have hb1 : ModularFormClass.qCoeff ⇑h 1 = 1 := by
    rw [hhd, qCoeff_smul, hd, inv_mul_cancel₀ h1]
  have hev := ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one 2 N
    (ModularFormClass.qCoeff ⇑h) cc (fun p hp hpN n => hcoeffT d p hp hpN n)
    (fun p hp hpN n => hcoeffU d p hp hpN n) hb1
  refine ⟨h, ?_, ?_⟩
  · rw [CuspForm.isNormalizedEigenform_iff_coeffHecke]
    refine ⟨hb1, fun p hp => ⟨fun hpN n => ?_, fun hpN n => ?_⟩⟩
    · rw [hcoeffT d p hp hpN n, hev p hp]
    · rw [hcoeffU d p hp hpN n, hev p hp]
  · intro ℓ hℓ hℓN hℓS
    have e1 : CuspForm.heckeTLin 2 hℓ hℓN h₀ = a ℓ • h₀ := (mem_W h₀).1 hh₀W ⟨ℓ, hℓ⟩ hℓN hℓS
    have e2 := hc' ⟨ℓ, hℓ⟩
    rw [hT_of_not_dvd ⟨ℓ, hℓ⟩ hℓN] at e2
    have e3 : (a ℓ - c ⟨ℓ, hℓ⟩) • h₀ = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    have hac : a ℓ = c ⟨ℓ, hℓ⟩ := by
      rcases smul_eq_zero.mp e3 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hh₀0
    rw [← hev ℓ hℓ, hcc ℓ hℓ, hac]

end CuspForm

end
