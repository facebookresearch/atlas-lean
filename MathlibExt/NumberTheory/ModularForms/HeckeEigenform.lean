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

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.NumberTheory.ModularForms.PeriodMapHecke

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
* `CuspForm.qCoeff_zero`: the constant `q`-coefficient of a cusp form on `Γ₀(N)` vanishes.
* `ModularFormClass.heckeT_eq_smul_iff`, `ModularFormClass.heckeU_eq_smul_iff`: being a Hecke
  eigenvector is a condition on `q`-coefficients.
* `CuspForm.isNormalizedEigenform_iff_coeffHecke`, `CuspForm.isNormalizedEigenform_iff_heckeT`,
  `CuspForm.isNormalizedEigenform_iff_heckeTLin`: normalized eigenforms are the cusp forms with
  first coefficient `1` that are eigenvectors of every `T_p` and `U_p`, with eigenvalue `a_p`.
* `ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one`,
  `ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero`: eigenvalues of a coefficient
  sequence, and vanishing when its first coefficient vanishes.
* `Module.End.exists_forall_apply_eq_smul_of_pairwise_commute`: a commuting family of
  endomorphisms of a nonzero finite-dimensional space over an algebraically closed field has a
  common eigenvector.
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

/-- The constant `q`-coefficient of a cusp form on `Γ₀(N)` vanishes. -/
theorem qCoeff_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularFormClass.qCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos
    (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N)

end CuspForm

/-! ### Hecke eigenvectors through `q`-coefficients -/

namespace ModularFormClass

open ModularForm

private theorem qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) :
    qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

private theorem periodic_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • f) ∘ ofComplex) 1 := fun z ↦ by
  simpa using congrArg (c * ·) (hper z)

private theorem eq_of_forall_qCoeff_eq_bare {f g : ℍ → ℂ} (hfper : Periodic (f ∘ ofComplex) 1)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (hgper : Periodic (g ∘ ofComplex) 1)
    (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g) (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) :
    f = g := by
  funext τ
  have hf := UpperHalfPlane.hasSum_qExpansion one_pos hfper hfhol hfbdd τ
  have hg := UpperHalfPlane.hasSum_qExpansion one_pos hgper hghol hgbdd τ
  simp only [qCoeff_eq] at h
  simp only [h] at hf
  exact hf.unique hg

private theorem bdd_of_mem_strictPeriods {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) : IsBoundedAtImInfty ⇑f :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  bdd_at_infty f

private theorem eq_of_forall_qCoeff_eq_class {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f g : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : ⇑f = ⇑g :=
  eq_of_forall_qCoeff_eq_bare (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (bdd_of_mem_strictPeriods f hΓ)
    (SlashInvariantFormClass.periodic_comp_ofComplex g hΓ) (ModularFormClass.holo g)
    (bdd_of_mem_strictPeriods g hΓ) h

/-! The regularity of `heckeU` and `heckeT` at `i∞`. -/

private theorem heckeUpperMatrix_one_zero (p j : ℕ) :
    ((heckeUpperMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeUpperMatrix hp]; rfl

private theorem heckeDiagMatrix_one_zero (p : ℕ) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeDiagMatrix hp]; rfl

private theorem isBoundedAtImInfty_heckeU {f : ℍ → ℂ} (k : ℤ) (p : ℕ)
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeUpperMatrix_one_zero p j))

private theorem isBoundedAtImInfty_heckeT {f : ℍ → ℂ} (k : ℤ) (p : ℕ)
    (hf : IsBoundedAtImInfty f) : IsBoundedAtImInfty (heckeT k p f) :=
  (isBoundedAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

private theorem apply_eq_of_coe_eq_add_nat {f : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) 1)
    {τ₁ τ₂ : ℍ} (m : ℕ) (h : (τ₁ : ℂ) = τ₂ + m) : f τ₁ = f τ₂ := by
  have h1 : (f ∘ ofComplex) ((τ₂ : ℂ) + m) = (f ∘ ofComplex) (τ₂ : ℂ) := by
    have := hf.nat_mul m
    rw [mul_one] at this
    exact this (τ₂ : ℂ)
  simp only [comp_apply] at h1
  rw [← h, ofComplex_apply, ofComplex_apply] at h1
  exact h1

private theorem heckeUpperMatrix_smul_vadd {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    heckeUpperMatrix p j • ((1 : ℝ) +ᵥ τ) = heckeUpperMatrix p (j + 1) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeUpperMatrix_smul hp, coe_heckeUpperMatrix_smul hp, coe_vadd]
  push_cast
  ring

private theorem coe_heckeUpperMatrix_smul_self {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    ((heckeUpperMatrix p p • τ : ℍ) : ℂ) = (heckeUpperMatrix p 0 • τ : ℍ) + (1 : ℕ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [coe_heckeUpperMatrix_smul hp, coe_heckeUpperMatrix_smul hp]
  field_simp
  push_cast
  ring

private theorem coe_heckeDiagMatrix_smul_vadd {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix p • ((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = (heckeDiagMatrix p • τ : ℍ) + (p : ℕ) := by
  rw [coe_heckeDiagMatrix_smul hp, coe_heckeDiagMatrix_smul hp, coe_vadd]
  push_cast
  ring

private theorem sum_heckeUpperMatrix_smul_vadd {f : ℍ → ℂ} {p : ℕ} (hp : p ≠ 0)
    (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ) := by
  simp only [heckeUpperMatrix_smul_vadd hp]
  have h0 := Finset.sum_range_succ' (fun j => f (heckeUpperMatrix p j • τ)) p
  have h1 := Finset.sum_range_succ (fun j => f (heckeUpperMatrix p j • τ)) p
  rw [apply_eq_of_coe_eq_add_nat hf 1 (coe_heckeUpperMatrix_smul_self hp τ)] at h1
  exact add_right_cancel (h0.symm.trans h1)

private theorem periodic_comp_ofComplex_of_vadd {g : ℍ → ℂ}
    (hg : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) : Periodic (g ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < Complex.im w
  · have hw' : 0 < Complex.im (w + 1) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert hg ⟨w, hw⟩ using 2
    apply UpperHalfPlane.ext
    simp [add_comm]
  · have hw1 : Complex.im (w + 1) ≤ 0 := by simpa using hw
    have hw0 : Complex.im w ≤ 0 := not_lt.mp hw
    simp only [comp_apply, ofComplex_apply_eq_of_im_nonpos hw1 hw0]

private theorem periodic_heckeU_comp_ofComplex {f : ℍ → ℂ} (k : ℤ) (p : ℕ)
    (hf : Periodic (f ∘ ofComplex) 1) : Periodic (heckeU k p f ∘ ofComplex) 1 := by
  refine periodic_comp_ofComplex_of_vadd fun τ ↦ ?_
  by_cases hp : p = 0
  · simp only [hp, heckeU_zero_left, Pi.zero_apply]
  · rw [heckeU_apply k hp, heckeU_apply k hp, sum_heckeUpperMatrix_smul_vadd hp hf]

private theorem periodic_heckeT_comp_ofComplex {f : ℍ → ℂ} (k : ℤ) (p : ℕ)
    (hf : Periodic (f ∘ ofComplex) 1) : Periodic (heckeT k p f ∘ ofComplex) 1 := by
  refine periodic_comp_ofComplex_of_vadd fun τ ↦ ?_
  by_cases hp : p = 0
  · simp only [hp, heckeT_zero_left]
    exact apply_eq_of_coe_eq_add_nat hf 1 (by rw [coe_vadd]; push_cast; ring)
  · rw [heckeT_apply k hp, heckeT_apply k hp, sum_heckeUpperMatrix_smul_vadd hp hf,
      apply_eq_of_coe_eq_add_nat hf p (coe_heckeDiagMatrix_smul_vadd hp τ)]

/-- A modular form `f` for a group with `1` as a strict period satisfies `T_p f = c • f` exactly
when its `q`-coefficients satisfy the corresponding eigenvalue equations. -/
theorem heckeT_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeT k p ⇑f = c • ⇑f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n
        = c * ModularFormClass.qCoeff f n := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hhol := ModularFormClass.holo f
  have hbdd := bdd_of_mem_strictPeriods f hΓ
  constructor
  · intro h n
    rw [← ModularFormClass.qCoeff_heckeT f hΓ hp n, h, qCoeff_const_smul hper hhol hbdd]
  · intro h
    refine eq_of_forall_qCoeff_eq_bare (periodic_heckeT_comp_ofComplex k p hper)
      (mdifferentiable_heckeT hhol k p) (isBoundedAtImInfty_heckeT k p hbdd)
      (periodic_const_smul hper c) (hhol.const_smul c) (hbdd.const_smul_left c) fun n ↦ ?_
    rw [ModularFormClass.qCoeff_heckeT f hΓ hp n, h n, qCoeff_const_smul hper hhol hbdd]

/-- A modular form `f` for a group with `1` as a strict period satisfies `U_p f = c • f` exactly
when its `q`-coefficients satisfy the corresponding eigenvalue equations. -/
theorem heckeU_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeU k p ⇑f = c • ⇑f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n
        = c * ModularFormClass.qCoeff f n := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hhol := ModularFormClass.holo f
  have hbdd := bdd_of_mem_strictPeriods f hΓ
  constructor
  · intro h n
    rw [← ModularFormClass.qCoeff_heckeU f hΓ hp n, h, qCoeff_const_smul hper hhol hbdd]
  · intro h
    refine eq_of_forall_qCoeff_eq_bare (periodic_heckeU_comp_ofComplex k p hper)
      (mdifferentiable_heckeU hhol k p) (isBoundedAtImInfty_heckeU k p hbdd)
      (periodic_const_smul hper c) (hhol.const_smul c) (hbdd.const_smul_left c) fun n ↦ ?_
    rw [ModularFormClass.qCoeff_heckeU f hΓ hp n, h n, qCoeff_const_smul hper hhol hbdd]

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
  have h0 : qCoeff f 0 = 0 := CuspForm.qCoeff_zero f
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

/-- A weight-two cusp form on `Γ₀(N)` is a normalized eigenform exactly when its first
`q`-coefficient is `1` and `T_p f = a_p • f` for `p ∤ N` and `U_p f = a_p • f` for `p ∣ N`, as
functions on the upper half-plane. -/
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

/-- A weight-two cusp form on `Γ₀(N)` is a normalized eigenform exactly when its first
`q`-coefficient is `1` and it is an eigenvector of the linear Hecke operators `T_p` (for
`p ∤ N`) and `U_p` (for `p ∣ N`) with eigenvalue `a_p`. -/
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

/-! ### Common eigenvectors of commuting endomorphisms -/

namespace Module.End

open Module Submodule

/-- A family of pairwise commuting endomorphisms of a nonzero finite-dimensional vector space
over an algebraically closed field has a common eigenvector. -/
theorem exists_forall_apply_eq_smul_of_pairwise_commute
    {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  classical
  have hcomm : ∀ i j, Commute (T i) (T j) := by
    intro i j
    rcases eq_or_ne i j with rfl | h
    · exact Commute.refl _
    · exact hT h
  suffices key : ∀ n : ℕ, ∀ W : Submodule K V, finrank K W = n → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, T i w ∈ W) → ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v by
    obtain ⟨v, -, hv0, hv⟩ := key _ ⊤ rfl (by simp) (fun i w _ => mem_top)
    exact ⟨v, hv0, hv⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn hW0 hWinv
    by_cases hscal : ∀ i, ∃ c : K, ∀ w ∈ W, T i w = c • w
    · obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
      refine ⟨v, hvW, hv0, fun i => ?_⟩
      obtain ⟨c, hc⟩ := hscal i
      exact ⟨c, hc v hvW⟩
    · push Not at hscal
      obtain ⟨i₀, hi₀⟩ := hscal
      have hmaps : ∀ w ∈ W, (T i₀) w ∈ W := hWinv i₀
      let S : Module.End K W := (T i₀).restrict hmaps
      have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue S
      let W' : Submodule K V := W ⊓ LinearMap.ker (T i₀ - μ • 1)
      have hW'le : W' ≤ W := inf_le_left
      have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ T i₀ v = μ • v := by
        intro v
        simp only [W', mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
          one_apply_eq_self, sub_eq_zero]
      have hW'0 : W' ≠ ⊥ := by
        obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
        have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
        have hwapp : T i₀ (w : V) = μ • (w : V) := by
          have := hw.apply_eq_smul
          have h2 := congrArg Subtype.val this
          simpa [S, LinearMap.restrict_apply] using h2
        intro hbot
        have : (w : V) ∈ W' := (hmemW' _).mpr ⟨w.2, hwapp⟩
        rw [hbot, mem_bot] at this
        exact hw0 this
      have hW'ne : W' ≠ W := by
        intro hEq
        obtain ⟨w, hw, hne⟩ := hi₀ μ
        have : w ∈ W' := hEq ▸ hw
        exact hne ((hmemW' w).mp this).2
      have hlt : W' < W := lt_of_le_of_ne hW'le hW'ne
      have hdim : finrank K W' < n := hWn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hW'inv : ∀ i, ∀ w ∈ W', T i w ∈ W' := by
        intro i w hw
        obtain ⟨hwW, hwT⟩ := (hmemW' w).mp hw
        refine (hmemW' _).mpr ⟨hWinv i w hwW, ?_⟩
        calc T i₀ (T i w) = T i (T i₀ w) := by
              have := hcomm i₀ i
              exact congrArg (fun f : Module.End K V => f w) this.eq
          _ = T i (μ • w) := by rw [hwT]
          _ = μ • T i w := by rw [LinearMap.map_smul]
      obtain ⟨v, hvW', hv0, hv⟩ := ih _ hdim W' rfl hW'0 hW'inv
      exact ⟨v, hW'le hvW', hv0, hv⟩

end Module.End

/-! ### Normalized eigenforms from simultaneous eigenvectors -/

namespace CuspForm

/-- A nonzero weight-two cusp form `g` on `Γ₀(N)` with `T_ℓ g = a_ℓ • g` for every prime
`ℓ ∤ N` outside `S` gives rise to a normalized eigenform `h` with `a_ℓ(h) = a ℓ` for every such
prime `ℓ`. -/
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
  have hcomm' : Pairwise fun p q => Commute (T' p) (T' q) := by
    intro p q _
    refine LinearMap.ext fun x => Subtype.ext ?_
    have := LinearMap.congr_fun (hcomm p q).eq (x : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    simpa only [mul_apply_eq_comp, T', LinearMap.coe_restrict_apply] using this
  have : Nontrivial W := ⟨⟨⟨g, hgW⟩, 0, fun h => hg (congrArg Subtype.val h)⟩⟩
  obtain ⟨v, hv0, hv⟩ := Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T' hcomm'
  set h₀ : CuspForm (CongruenceSubgroup.Gamma0 N) 2 :=
    (v : CuspForm (CongruenceSubgroup.Gamma0 N) 2) with hh₀
  have hh₀0 : h₀ ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hh₀W : h₀ ∈ W := v.2
  choose c hc using hv
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
    refine DFunLike.coe_injective <|
      ModularFormClass.eq_of_forall_qCoeff_eq_class h₀ 0 hΓ fun n => ?_
    rw [qCoeff_zero']
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspForm.qCoeff_zero h₀
    · exact hall n hn.ne'
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
