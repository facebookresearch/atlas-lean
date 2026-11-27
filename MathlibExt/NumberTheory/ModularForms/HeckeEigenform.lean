/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
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
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualModularity
public import MathlibExt.NumberTheory.ModularForms.PeriodMapHecke

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector
import MathlibExt.NumberTheory.ModularForms.HeckeAlgebra
import MathlibExt.NumberTheory.ModularForms.NormalizedEigenform
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

/-!
# Normalized Hecke eigenforms of weight two on `Γ₀(N)`

This file characterizes the Hecke eigenvalue equations `T_p f = c • f` and `U_p f = c • f`
through `q`-coefficients and normalized Hecke eigenforms of weight two through the Hecke
operators, and shows that a nonzero weight-two cusp form that is an eigenvector of the Hecke
operators `T_ℓ` for almost all primes `ℓ ∤ N` gives rise to a normalized eigenform with the same
eigenvalues. It builds on `MathlibExt.NumberTheory.ModularForms.NormalizedEigenform`, which gives
the finite-dimensionality of cusp forms on `Γ₀(N)`, the coefficient criterion
`CuspForm.isNormalizedEigenform_iff_coeffHecke` and the eigenvalue lemmas for coefficient
sequences.

## Main statements

* `ModularFormClass.heckeT_eq_smul_iff`, `ModularFormClass.heckeU_eq_smul_iff`: the Hecke
  eigenvalue equations are conditions on `q`-coefficients.
* `CuspForm.isNormalizedEigenform_iff_heckeT`, `CuspForm.isNormalizedEigenform_iff_heckeTLin`:
  normalized eigenforms are the cusp forms with first coefficient `1` that are eigenvectors of
  every `T_p` and `U_p`, with eigenvalue `a_p`.
* `CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul`: a nonzero simultaneous
  eigenvector of almost all `T_ℓ` yields a normalized eigenform with the same eigenvalues.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane Function
open scoped MatrixGroups ModularForm Manifold

/-! ### Hecke eigenvalue equations through `q`-coefficients -/

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
