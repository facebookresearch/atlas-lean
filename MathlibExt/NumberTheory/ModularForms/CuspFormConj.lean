/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_qCoeff_conj.lean`
and
`P2M/Sol/S_CuspForm_exists_qCoeff_conj.lean`
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

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.SlashActions
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

@[expose] public section

open UpperHalfPlane Complex Function Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate

/-- The `n`-th coefficient of the `q`-expansion of a function on the upper
half-plane, using the period `1` parameter `q = exp (2πiτ)`. -/
public noncomputable def ModularFormClass.qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

/-- The `q`-expansion coefficient is, by definition, the corresponding
coefficient of the `q`-expansion power series. -/
@[simp]
public theorem ModularFormClass.qCoeff_eq (f : ℍ → ℂ) (n : ℕ) :
    ModularFormClass.qCoeff f n = (UpperHalfPlane.qExpansion 1 f).coeff n :=
  rfl

namespace CuspForm

private theorem mapGL_apply' (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private theorem J_mul_mapGL (g : SL(2, ℤ)) :
    ∃ g' : SL(2, ℤ), g' 1 0 = -g 1 0 ∧ J * mapGL ℝ g = mapGL ℝ g' * J := by
  have hdet : (!![g 0 0, -g 0 1; -g 1 0, g 1 1] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination det_eq g
  let g' : SL(2, ℤ) := ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], hdet⟩
  have hg' : ∀ i j, g' i j = !![g 0 0, -g 0 1; -g 1 0, g 1 1] i j :=
    fun i j => rfl
  refine ⟨g', ?_, ?_⟩
  · rw [hg']
    simp
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, val_J,
        mapGL_apply', hg', Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      push_cast <;> ring

variable (N : ℕ)

abbrev Γ₀ : Subgroup (GL (Fin 2) ℝ) :=
  ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem exists_J_mul_eq {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ₀ N) :
    ∃ γ' ∈ Γ₀ N, J * γ = γ' * J := by
  obtain ⟨g, hg, rfl⟩ := hγ
  obtain ⟨g', hg', hmul⟩ := J_mul_mapGL g
  refine ⟨mapGL ℝ g', Subgroup.mem_map_of_mem (mapGL ℝ) ?_, hmul⟩
  rw [CongruenceSubgroup.Gamma0_mem, hg']
  push_cast
  rw [CongruenceSubgroup.Gamma0_mem.mp hg, neg_zero]

private def Jℚ : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp [Matrix.det_fin_two_of])

private theorem J_eq_map : J = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) Jℚ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [val_J, Jℚ, Matrix.GeneralLinearGroup.mkOfDetNeZero]

public theorem isCusp_J_smul [NeZero N] {c : OnePoint ℝ} (hc : IsCusp c (Γ₀ N)) :
    IsCusp (J • c) (Γ₀ N) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨Jℚ • c, by rw [← Rat.coe_castHom, OnePoint.map_smul, ← J_eq_map]⟩

private theorem slash_J_apply (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] J) τ = conj (f (J • τ)) := by
  rw [ModularForm.slash_apply, denom_J, one_zpow, mul_one, det_J, UpperHalfPlane.sigma_J]
  simp

private theorem conj_qParam_J_smul (τ : ℍ) :
    conj (Periodic.qParam 1 ((J • τ : ℍ) : ℂ)) = Periodic.qParam 1 (τ : ℂ) := by
  rw [coe_J_smul, Periodic.qParam, Periodic.qParam, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_div₀, map_neg, Complex.conj_conj, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  ring

private theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ₀ N).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

variable [NeZero N] (k : ℤ)

omit [NeZero N] in
private theorem hasSum_qCoeff (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ModularFormClass.qCoeff f m • Periodic.qParam 1 (τ : ℂ) ^ m)
      (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₀ N)) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods N)⟩
  exact hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N))
    (CuspFormClass.holo f) (CuspFormClass.zero_at_infty f).isBoundedAtImInfty τ


/-- The cusp form obtained by conjugating all `q`-expansion coefficients:
it is the slash action of the coefficient-conjugation matrix `J`. -/
public noncomputable def conjForm (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k where
  toFun := ⇑f ∣[k] J
  slash_action_eq' γ hγ := by
    obtain ⟨γ', hγ', hcomm⟩ := exists_J_mul_eq N hγ
    rw [← SlashAction.slash_mul, hcomm, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f γ' hγ']
  holo' := (CuspFormClass.holo f).slash k J
  zero_at_cusps' hc :=
    OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_J_smul N hc))

@[simp]
private theorem coe_conjForm (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ⇑(conjForm N k f) = ⇑f ∣[k] J :=
  rfl

private theorem conjForm_apply (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    conjForm N k f τ = conj (f (J • τ)) := by
  rw [coe_conjForm, slash_J_apply]

private theorem hasSum_conjForm (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ conj (ModularFormClass.qCoeff f m) •
        Periodic.qParam 1 (τ : ℂ) ^ m)
      (conjForm N k f τ) := by
  rw [conjForm_apply]
  have h := Complex.hasSum_conj'.mpr (hasSum_qCoeff N k f (J • τ))
  convert h using 2 with m
  rw [smul_eq_mul, smul_eq_mul, map_mul, map_pow, conj_qParam_J_smul]

/-- Coefficient conjugation: the `n`-th `q`-coefficient of the conjugate
form is the complex conjugate of the `n`-th `q`-coefficient of the original
form. -/
public theorem qCoeff_conjForm (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff (conjForm N k f) n =
      conj (ModularFormClass.qCoeff f n) := by
  have h := ModularFormClass.qExpansion_coeff_unique (f := conjForm N k f)
    one_pos (one_mem_strictPeriods N) (hasSum_conjForm N k f) n
  exact h.symm

end CuspForm

/-- Complex conjugation of `q`-coefficients is realized by another cusp form
of the same level `Γ₀(N)` and the same weight. -/
public theorem CuspForm.exists_qCoeff_conj (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k →
        CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ),
        ModularFormClass.qCoeff (ρ f) n =
          (starRingEnd ℂ) (ModularFormClass.qCoeff f n) :=
  ⟨CuspForm.conjForm N k, fun f n => CuspForm.qCoeff_conjForm N k f n⟩
