/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FLTPrelim_Modularity.lean`,
`Definitions/Def_Gamma0HeckeOperatorHom.lean`,
`Definitions/Def_ModularCurve_PeriodMap.lean`,
`Definitions/Def_ModularCurve_PeriodMapBundled.lean`,
`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Definitions/Def_ModularForm_HeckeOperatorForms.lean`,
`Theorems/Thm_CuspFormClass_isZeroAt_heckeT.lean`,
`Theorems/Thm_CuspFormClass_isZeroAt_heckeU.lean`,
`Theorems/Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0.lean`,
`Theorems/Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt.lean`,
`Theorems/Thm_ModularCurve_periodMap_eq_periodHom.lean`,
`Theorems/Thm_ModularCurve_periodMap_heckeTLin.lean`,
`Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean`,
`Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`,
`Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean`,
`Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean`,
`Theorems/Thm_ModularFormClass_isBoundedAt_heckeT.lean`,
`Theorems/Thm_ModularFormClass_isBoundedAt_heckeU.lean`,
`P2M/Sol/S_CuspFormClass_isZeroAt_heckeT.lean`,
`P2M/Sol/S_CuspFormClass_isZeroAt_heckeU.lean`,
`P2M/Sol/S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0.lean`,
`P2M/Sol/S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt.lean`,
`P2M/Sol/S_ModularCurve_periodMap_eq_periodHom.lean`,
`P2M/Sol/S_ModularCurve_periodMap_heckeTLin.lean`,
`P2M/Sol/S_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean`,
`P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`,
`P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean`,
`P2M/Sol/S_ModularForm_mdifferentiable_heckeU.lean`,
`P2M/Sol/S_ModularFormClass_isBoundedAt_heckeT.lean`, and
`P2M/Sol/S_ModularFormClass_isBoundedAt_heckeU.lean`
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

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import MathlibExt.NumberTheory.ModularForms.CoeffHecke
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Data.Nat.Prime.Int
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

@[expose] public section


-- ===== Definitions.Def_ModularCurve_PeriodMap =====

namespace ModularCurve.Period

open UpperHalfPlane

open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)

def IsEquivariantPrimitive : Prop :=
  ∀ γ : Γ, ∃ c : ℂ, ∀ z : ℍ, F ((γ : SL(2, ℤ)) • z) - F z = c

variable {Γ F}

namespace IsEquivariantPrimitive

noncomputable def period (_hF : IsEquivariantPrimitive Γ F) (γ : Γ) : ℂ :=
  F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I

theorem sub_eq_period (hF : IsEquivariantPrimitive Γ F) (γ : Γ) (z : ℍ) :
    F ((γ : SL(2, ℤ)) • z) - F z = hF.period γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [hc z, period, hc UpperHalfPlane.I]

@[simp]
theorem period_one (hF : IsEquivariantPrimitive Γ F) : hF.period 1 = 0 := by
  have h := hF.sub_eq_period 1 UpperHalfPlane.I
  simpa using h.symm

theorem period_mul (hF : IsEquivariantPrimitive Γ F) (γ δ : Γ) :
    hF.period (γ * δ) = hF.period γ + hF.period δ := by
  have h1 := hF.sub_eq_period (γ * δ) UpperHalfPlane.I
  have h2 := hF.sub_eq_period γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h3 := hF.sub_eq_period δ UpperHalfPlane.I
  have hsmul : ((γ * δ : Γ) : SL(2, ℤ)) • UpperHalfPlane.I
      = (γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [← mul_smul]; rfl
  rw [hsmul] at h1
  linear_combination h2 + h3 - h1

noncomputable def periodHom (hF : IsEquivariantPrimitive Γ F) : Additive Γ →+ ℂ where
  toFun γ := hF.period (Additive.toMul γ)
  map_zero' := hF.period_one
  map_add' γ δ := hF.period_mul (Additive.toMul γ) (Additive.toMul δ)

@[simp]
theorem periodHom_apply (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    hF.periodHom (Additive.ofMul γ) = hF.period γ :=
  rfl

theorem period_congr {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (c : ℂ) (h : ∀ z, F z - F' z = c) (γ : Γ) :
    hF.period γ = hF'.period γ := by
  rw [← hF.sub_eq_period γ UpperHalfPlane.I, ← hF'.sub_eq_period γ UpperHalfPlane.I]
  have h1 := h ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h2 := h UpperHalfPlane.I
  linear_combination h1 - h2

end IsEquivariantPrimitive

end ModularCurve.Period

-- ===== Definitions.Def_ModularCurve_PeriodMapBundled =====

namespace ModularCurve

open UpperHalfPlane CongruenceSubgroup Filter Topology Period

open scoped MatrixGroups

def HasEquivariantPrimitive (N : ℕ) (f : CuspForm (Gamma0 N) 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    IsEquivariantPrimitive (Gamma0 N) F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

noncomputable def periodMap (N : ℕ) (f : CuspForm (Gamma0 N) 2) : Additive (Gamma0 N) →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F then h.choose_spec.2.2.1.periodHom else 0

theorem periodMap_def (N : ℕ) (f : CuspForm (Gamma0 N) 2) {F : ℍ → ℂ}
    (hF : HasEquivariantPrimitive N f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitive N f F₀), periodMap N f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dif_pos h⟩

end ModularCurve

-- ===== Definitions.Def_ModularForm_HeckeOperator =====

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularForm

def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] := rfl

def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

theorem det_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) : ((heckeMatrix p j).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_heckeMatrix hp, Matrix.det_fin_two_of]
  ring

theorem det_heckeMatrix_pos (p j : ℕ) : 0 < ((heckeMatrix p j).det : ℝ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [det_heckeMatrix hp]; exact_mod_cast Nat.pos_of_ne_zero hp

theorem denom_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeMatrix hp]

theorem coe_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeMatrix hp]

theorem σ_heckeMatrix (p j : ℕ) : UpperHalfPlane.σ (heckeMatrix p j) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos (det_heckeMatrix_pos p j)]

theorem slash_heckeMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeMatrix, det_heckeMatrix hp, denom_heckeMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

theorem heckeU_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeU k p f = ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j := rfl

theorem heckeT_eq_heckeU_add (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p := rfl

theorem heckeT_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = (∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j) + f ∣[k] heckeDiagMatrix p := rfl

@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeMatrix_apply k hp, Finset.mul_sum]

theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

theorem heckeU_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f + g) = heckeU k p f + heckeU k p g := by
  simp [heckeU, Finset.sum_add_distrib]

theorem heckeT_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f + g) = heckeT k p f + heckeT k p g := by
  simp only [heckeT, heckeU_add, SlashAction.add_slash]
  abel

theorem heckeU_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeU k p (c • f) = c • heckeU k p f := by
  simp only [heckeU, ModularForm.smul_slash, σ_heckeMatrix, ContinuousAlgEquiv.refl_apply,
    Finset.smul_sum]

theorem heckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) :
    heckeT k p (c • f) = c • heckeT k p f := by
  rw [heckeT, heckeT, heckeU_smul, ModularForm.smul_slash, σ_heckeDiagMatrix,
    ContinuousAlgEquiv.refl_apply, smul_add]

theorem heckeU_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeU k p (-f) = -heckeU k p f := by
  simp [heckeU, Finset.sum_neg_distrib]

theorem heckeT_neg (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : heckeT k p (-f) = -heckeT k p f := by
  simp only [heckeT, heckeU_neg, SlashAction.neg_slash, neg_add]

theorem heckeU_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeU k p (f - g) = heckeU k p f - heckeU k p g := by
  rw [sub_eq_add_neg, heckeU_add, heckeU_neg, ← sub_eq_add_neg]

theorem heckeT_sub (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f - g) = heckeT k p f - heckeT k p g := by
  rw [sub_eq_add_neg, heckeT_add, heckeT_neg, ← sub_eq_add_neg]

def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

theorem coeffHeckeT_apply (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeU_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : coeffHeckeU p a n = a (n * p) := rfl

theorem coeffHeckeT_of_dvd (k : ℤ) {p n : ℕ} (h : p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) + (p : ℂ) ^ (k - 1) * a (n / p) := by
  rw [coeffHeckeT, if_pos h]

theorem coeffHeckeT_of_not_dvd (k : ℤ) {p n : ℕ} (h : ¬ p ∣ n) (a : ℕ → ℂ) :
    coeffHeckeT k p a n = a (n * p) := by
  rw [coeffHeckeT, if_neg h, add_zero]

theorem coeffHeckeT_eq_coeffHeckeU_add (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    coeffHeckeT k p a n = coeffHeckeU p a n + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0 := rfl

theorem coeffHeckeT_add (k : ℤ) (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeT k p (a + b) = coeffHeckeT k p a + coeffHeckeT k p b := by
  funext n
  simp only [coeffHeckeT, Pi.add_apply]
  split_ifs <;> ring

theorem coeffHeckeT_smul (k : ℤ) (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeT k p (c • a) = c • coeffHeckeT k p a := by
  funext n
  simp only [coeffHeckeT, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem coeffHeckeU_add (p : ℕ) (a b : ℕ → ℂ) :
    coeffHeckeU p (a + b) = coeffHeckeU p a + coeffHeckeU p b := rfl

theorem coeffHeckeU_smul (p : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    coeffHeckeU p (c • a) = c • coeffHeckeU p a := rfl

end ModularForm

end

-- ===== P2M.Sol.S_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0 =====
-- (shared with P2M.Sol.S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0)
namespace PeriodMapPort.Internal.SlashInvariance

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped _root_.MatrixGroups _root_.ModularForm _root_.OnePoint

namespace ModularForm
export _root_.ModularForm (rec ext heckeMatrix heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add)
open _root_.ModularForm

namespace HeckeSlashInvariance

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply]
    all_goals (repeat erw [mapGL_apply])
    all_goals simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
    all_goals first
      | (push_cast; ring1)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply]
    all_goals (repeat erw [mapGL_apply])
    all_goals simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
    all_goals first
      | (push_cast; ring1)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply]
    all_goals (repeat erw [mapGL_apply])
    all_goals simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
    all_goals first
      | (push_cast; ring1)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply]
    all_goals (repeat erw [mapGL_apply])
    all_goals simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val']
    all_goals first
      | (push_cast; ring1)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section reindex

variable {p : ℕ} [NeZero p]

theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.range p, F j = ∑ x : ZMod p, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex

section heckeU

variable {p : ℕ}

theorem unit_of_apply_one_zero_eq_zero (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) :
    ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
  push_cast at this
  linear_combination this + ((g 0 1 : ℤ) : ZMod p) * hc

def affinePerm (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) : Equiv.Perm (ZMod p) where
  toFun j := ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j)
  invFun j := ((g 0 0 : ℤ) : ZMod p) * (((g 0 0 : ℤ) : ZMod p) * j - ((g 0 1 : ℤ) : ZMod p))
  left_inv j := by
    linear_combination (((g 0 0 : ℤ) : ZMod p) * ((g 0 1 : ℤ) : ZMod p)
      + j * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) + 1)) *
        unit_of_apply_one_zero_eq_zero g hc
  right_inv j := by
    linear_combination (-(((g 1 1 : ℤ) : ZMod p) * ((g 0 1 : ℤ) : ZMod p))
      + j * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) + 1)) *
        unit_of_apply_one_zero_eq_zero g hc

theorem affinePerm_apply (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) (j : ZMod p) :
    affinePerm g hc j =
      ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j) := rfl

variable [NeZero p]

theorem heckeMatrix_mul_of_dvd (g : SL(2, ℤ)) (hc : (p : ℤ) ∣ g 1 0) (x : ZMod p) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeMatrix p x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeMatrix p (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
  have hc0 : ((g 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  set x' := affinePerm g hc0 x with hx'
  obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + x.val * g 1 1 - x'.val * (g 0 0 + x.val * g 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hx', affinePerm_apply]
    linear_combination (-(((g 0 1 : ℤ) : ZMod p) + x * ((g 1 1 : ℤ) : ZMod p))) *
      unit_of_apply_one_zero_eq_zero g hc0
      - (((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * x) * x) * hc0
  exact heckeMatrix_mul_of_eq (NeZero.ne p) g x.val x'.val e (by linear_combination he)

variable {N : ℕ} (k : ℤ)

theorem heckeU_slash_mapGL (hpN : p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeU k p f ∣[k] (mapGL ℝ g) = heckeU k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpN).trans hcN
  rw [heckeU_eq_sum_zmod k f, SlashAction.sum_slash]
  calc ∑ x : ZMod p, (f ∣[k] heckeMatrix p x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod p, f ∣[k] heckeMatrix p
          (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_dvd g hc x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N := by
          rw [CongruenceSubgroup.Gamma0_mem, hg']
          push_cast
          rw [CongruenceSubgroup.Gamma0_mem.mp hg, mul_zero]
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val :=
        Equiv.sum_comp (affinePerm g _) (fun x ↦ f ∣[k] heckeMatrix p x.val)

end heckeU

section heckeT

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[scoped simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[scoped simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

theorem heckeT_eq_sum_onePoint [NeZero p] (k : ℤ) (f : ℍ → ℂ) :
    heckeT k p f = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x := by
  rw [heckeT_eq_heckeU_add, heckeU_eq_sum_zmod, add_comm]
  exact (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] heckeRep p x)).symm

variable [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

@[scoped simp] theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [if_pos (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, hmul⟩
      rw [hg']
      have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
      exact hcop.dvd_of_dvd_mul_left (he ▸ hg)
    ·
      rw [if_neg (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0
        with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ hg, hmul⟩
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    ·
      rw [if_pos h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_eq' hp g j.val e he
      exact ⟨g', hg' ▸ hg, hmul⟩
    ·
      rw [if_neg h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ dvd_mul_of_dvd_right hg _, hmul⟩

variable {N : ℕ} (k : ℤ)

theorem heckeT_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeT k p f ∣[k] (mapGL ℝ g) = heckeT k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  rw [heckeT_eq_sum_onePoint k f, SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] heckeRep p x) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p (redMatrix p g • x) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeRep_mul hpN g hcN x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g)) (fun x ↦ f ∣[k] heckeRep p x)

end heckeT

end HeckeSlashInvariance
open scoped PeriodMapPort.Internal.SlashInvariance.ModularForm.HeckeSlashInvariance

open HeckeSlashInvariance in
theorem heckeT_slash_eq_self_of_mem_Gamma0' {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeT k p f) = ModularForm.heckeT k p f := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeT_slash_mapGL k hpN f hf g hg

open HeckeSlashInvariance in
theorem heckeU_slash_eq_self_of_mem_Gamma0' {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeU_slash_mapGL k hpN f hf g hg

end ModularForm
open scoped PeriodMapPort.Internal.SlashInvariance.ModularForm.HeckeSlashInvariance
  PeriodMapPort.Internal.SlashInvariance.ModularForm

end
open scoped PeriodMapPort.Internal.SlashInvariance.ModularForm.HeckeSlashInvariance
  PeriodMapPort.Internal.SlashInvariance.ModularForm

end SlashInvariance
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0 =====

theorem ModularForm.heckeT_slash_eq_self_of_mem_Gamma0 : ∀ {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))), SlashAction.map k γ (ModularForm.heckeT k p f) = ModularForm.heckeT k p f :=
  @PeriodMapPort.Internal.SlashInvariance.ModularForm.heckeT_slash_eq_self_of_mem_Gamma0'

-- ===== Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0 =====

theorem ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 : ∀ {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))), SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f :=
  @PeriodMapPort.Internal.SlashInvariance.ModularForm.heckeU_slash_eq_self_of_mem_Gamma0'

-- ===== P2M.Sol.S_ModularForm_mdifferentiable_heckeT =====
-- (shared with P2M.Sol.S_ModularForm_mdifferentiable_heckeU)
namespace PeriodMapPort.Internal.Regularity

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace M4cP1W2

open ModularForm ModularFormClass

section Matrices

variable (p j : ℕ)

theorem heckeMatrix_one_zero :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeMatrix hp]; rfl

theorem heckeDiagMatrix_one_zero :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeDiagMatrix hp]; rfl

end Matrices

section Regularity

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

theorem mdifferentiable_heckeU (hf : MDiff f) : MDiff (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => MDiff g) (fun _ _ ha hb => ha.add hb)
    mdifferentiable_const (fun _ _ => hf.slash k _)

theorem mdifferentiable_heckeT (hf : MDiff f) : MDiff (heckeT k p f) :=
  (mdifferentiable_heckeU k p hf).add (hf.slash k _)

theorem isBoundedAtImInfty_heckeU (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

theorem isBoundedAtImInfty_heckeT (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeT k p f) :=
  (isBoundedAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

theorem isZeroAtImInfty_heckeU (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsZeroAtImInfty g)
    (fun _ _ ha hb => ha.add hb) (zero_zeroAtFilter atImInfty)
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

theorem isZeroAtImInfty_heckeT (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeT k p f) :=
  (isZeroAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

theorem apply_eq_of_coe_eq_add_nat (hf : Periodic (f ∘ ofComplex) 1) {τ₁ τ₂ : ℍ} (m : ℕ)
    (h : (τ₁ : ℂ) = τ₂ + m) : f τ₁ = f τ₂ := by
  have h1 : (f ∘ ofComplex) ((τ₂ : ℂ) + m) = (f ∘ ofComplex) (τ₂ : ℂ) := by
    have := hf.nat_mul m
    rw [mul_one] at this
    exact this (τ₂ : ℂ)
  simp only [comp_apply] at h1
  rw [← h, ofComplex_apply, ofComplex_apply] at h1
  exact h1

variable {p} in

theorem heckeMatrix_smul_vadd (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    heckeMatrix p j • ((1 : ℝ) +ᵥ τ) = heckeMatrix p (j + 1) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hp, coe_heckeMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in

theorem coe_heckeMatrix_smul_self (hp : p ≠ 0) (τ : ℍ) :
    ((heckeMatrix p p • τ : ℍ) : ℂ) = (heckeMatrix p 0 • τ : ℍ) + (1 : ℕ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [coe_heckeMatrix_smul hp, coe_heckeMatrix_smul hp]
  field_simp
  push_cast
  ring

variable {p} in

theorem coe_heckeDiagMatrix_smul_vadd (hp : p ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix p • ((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = (heckeDiagMatrix p • τ : ℍ) + (p : ℕ) := by
  rw [coe_heckeDiagMatrix_smul hp, coe_heckeDiagMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in
theorem sum_heckeMatrix_smul_vadd (hp : p ≠ 0) (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    ∑ j ∈ Finset.range p, f (heckeMatrix p j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ) := by
  simp only [heckeMatrix_smul_vadd hp]
  have h0 := Finset.sum_range_succ' (fun j => f (heckeMatrix p j • τ)) p
  have h1 := Finset.sum_range_succ (fun j => f (heckeMatrix p j • τ)) p
  rw [apply_eq_of_coe_eq_add_nat hf 1 (coe_heckeMatrix_smul_self hp τ)] at h1
  exact add_right_cancel (h0.symm.trans h1)

theorem heckeU_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeU k p f ((1 : ℝ) +ᵥ τ) = heckeU k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeU_zero_left, Pi.zero_apply]
  · rw [heckeU_apply k hp, heckeU_apply k hp, sum_heckeMatrix_smul_vadd hp hf]

theorem heckeT_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeT k p f ((1 : ℝ) +ᵥ τ) = heckeT k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeT_zero_left]
    exact apply_eq_of_coe_eq_add_nat hf 1 (by rw [coe_vadd]; push_cast; ring)
  · rw [heckeT_apply k hp, heckeT_apply k hp, sum_heckeMatrix_smul_vadd hp hf,
      apply_eq_of_coe_eq_add_nat hf p (coe_heckeDiagMatrix_smul_vadd hp τ)]

theorem periodic_comp_ofComplex_of_vadd {g : ℍ → ℂ} (hg : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    Periodic (g ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < im w
  · have hw' : 0 < im (w + 1) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    convert hg ⟨w, hw⟩ using 2
    apply UpperHalfPlane.ext
    simp [add_comm]
  · have hw1 : im (w + 1) ≤ 0 := by simpa using hw
    have hw0 : im w ≤ 0 := not_lt.mp hw
    simp only [comp_apply, ofComplex_apply_eq_of_im_nonpos hw1 hw0]

theorem periodic_heckeU_comp_ofComplex (hf : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeU k p f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeU_vadd k p hf)

theorem periodic_heckeT_comp_ofComplex (hf : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeT k p f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeT_vadd k p hf)

end Regularity

section Uniqueness

theorem qExpansion_coeff_unique' {g : ℍ → ℂ} (hcont : Continuous g) {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion 1 g).coeff m :=
  UpperHalfPlane.qExpansion_coeff_unique (ContinuousMap.mk g hcont) one_pos hg hs m

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem hasSum_qCoeff [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) τ

theorem eq_of_forall_qCoeff_eq [ModularFormClass F Γ k] {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g := by
  refine DFunLike.ext f g fun τ => ?_
  have hf := hasSum_qCoeff f hΓ τ
  have hg := hasSum_qCoeff g hΓ τ
  simp only [h] at hf
  exact hf.unique hg

end Uniqueness

section QExpAction

theorem qParam_one (z : ℂ) : Periodic.qParam 1 z = exp (2 * π * I * z) := by
  simp [Periodic.qParam]

variable {p : ℕ} (hp : p ≠ 0)

include hp in
theorem natCast_ne_zero' : (p : ℂ) ≠ 0 := by exact_mod_cast hp

include hp in

theorem qParam_heckeMatrix_smul (j : ℕ) (τ : ℍ) :
    Periodic.qParam 1 ((heckeMatrix p j • τ : ℍ) : ℂ)
      = exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j := by
  rw [qParam_one, coe_heckeMatrix_smul hp, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have := natCast_ne_zero' hp
  field_simp

include hp in

theorem qParam_heckeDiagMatrix_smul (τ : ℍ) :
    Periodic.qParam 1 ((heckeDiagMatrix p • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ p := by
  rw [qParam_one, qParam_one, coe_heckeDiagMatrix_smul hp, ← Complex.exp_nat_mul]
  congr 1
  ring

include hp in

theorem exp_div_pow (τ : ℍ) : exp (2 * π * I * τ / p) ^ p = Periodic.qParam 1 τ := by
  rw [qParam_one, ← Complex.exp_nat_mul]
  congr 1
  have := natCast_ne_zero' hp
  field_simp

include hp in

theorem sum_rootOfUnity_pow (m : ℕ) :
    ∑ j ∈ Finset.range p, (exp (2 * π * I / p) ^ j) ^ m = if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp
  have hswap : ∀ j : ℕ, (exp (2 * π * I / p) ^ j) ^ m = (exp (2 * π * I / p) ^ m) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j m]
  simp only [hswap]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr h]
    simp
  · have hne : exp (2 * π * I / p) ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div]

theorem not_dvd_of_not_mem_range {m : ℕ} (hm : m ∉ Set.range (fun l : ℕ ↦ l * p)) : ¬ p ∣ m := by
  rintro ⟨l, rfl⟩
  exact hm ⟨l, by simp [mul_comm]⟩

variable {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
  (hbdd : IsBoundedAtImInfty f)

include hp hper hhol hbdd in

theorem hasSum_average (τ : ℍ) :
    HasSum (fun l : ℕ ↦ qCoeff f (l * p) * Periodic.qParam 1 τ ^ l)
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)) := by
  have hF : ∀ τ' : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ' ^ m) (f τ') :=
    hasSum_qExpansion one_pos hper hhol hbdd

  have h1 : HasSum (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      (∑ j ∈ Finset.range p, f (heckeMatrix p j • τ)) := by
    refine hasSum_sum fun j _ => ?_
    have := hF (heckeMatrix p j • τ)
    rwa [qParam_heckeMatrix_smul hp j τ] at this

  have h2 : (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      = fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0 := by
    funext m
    simp only [mul_pow, smul_eq_mul, ← Finset.mul_sum, sum_rootOfUnity_pow hp m]
    split_ifs <;> ring
  rw [h2] at h1

  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  have h3 := (hinj.hasSum_iff (f := fun m ↦
      if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0)
    (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mpr h1
  have h4 : ((fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m else 0) ∘
      fun l : ℕ ↦ l * p) = fun l ↦ (p : ℂ) * (qCoeff f (l * p) * Periodic.qParam 1 τ ^ l) := by
    funext l
    simp only [comp_apply, if_pos (dvd_mul_left p l)]
    rw [mul_comm l p, pow_mul, exp_div_pow hp τ]
    ring
  rw [h4] at h3
  have h5 := h3.mul_left ((p : ℂ)⁻¹)
  simp only [← mul_assoc, inv_mul_cancel₀ (natCast_ne_zero' hp), one_mul] at h5
  exact h5

include hp hper hhol hbdd in

theorem hasSum_diag (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ if p ∣ n then (p : ℂ) ^ (k - 1) * qCoeff f (n / p) * Periodic.qParam 1 τ ^ n
        else 0)
      ((p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ)) := by
  have hD := (hasSum_qExpansion one_pos hper hhol hbdd (heckeDiagMatrix p • τ)).mul_left
    ((p : ℂ) ^ (k - 1))
  rw [qParam_heckeDiagMatrix_smul hp τ] at hD
  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  refine (hinj.hasSum_iff (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mp ?_
  convert hD using 1
  funext l
  simp only [comp_apply, if_pos (dvd_mul_left p l), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hp),
    smul_eq_mul]
  rw [← pow_mul, mul_comm l p, mul_assoc]
  rfl

include hp hper hhol hbdd in

theorem hasSum_heckeU (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeU p (qCoeff f) n • Periodic.qParam 1 τ ^ n) (heckeU k p f τ) := by
  rw [heckeU_apply k hp]
  simpa only [coeffHeckeU_apply, smul_eq_mul] using hasSum_average hp hper hhol hbdd τ

include hp hper hhol hbdd in

theorem hasSum_heckeT (k : ℤ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeT k p (qCoeff f) n • Periodic.qParam 1 τ ^ n) (heckeT k p f τ) := by
  rw [heckeT_apply k hp]
  convert (hasSum_average hp hper hhol hbdd τ).add (hasSum_diag hp hper hhol hbdd k τ) using 1
  funext n
  rw [coeffHeckeT_apply, smul_eq_mul]
  split_ifs <;> ring

include hp hper hhol hbdd in
theorem qCoeff_heckeU_bare (k : ℤ) (n : ℕ) :
    qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  (qExpansion_coeff_unique' (mdifferentiable_heckeU k p hhol).continuous
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeU_comp_ofComplex k p hper)
      (mdifferentiable_heckeU k p hhol) (isBoundedAtImInfty_heckeU k p hbdd))
    (hasSum_heckeU hp hper hhol hbdd k) n).symm

include hp hper hhol hbdd in
theorem qCoeff_heckeT_bare (k : ℤ) (n : ℕ) :
    qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n :=
  (qExpansion_coeff_unique' (mdifferentiable_heckeT k p hhol).continuous
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeT_comp_ofComplex k p hper)
      (mdifferentiable_heckeT k p hhol) (isBoundedAtImInfty_heckeT k p hbdd))
    (hasSum_heckeT hp hper hhol hbdd k) n).symm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

include hp in
theorem qCoeff_heckeU_class [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (n : ℕ) : qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeU_bare hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) k n

include hp in
theorem qCoeff_heckeT_class [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (n : ℕ) : qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeT_bare hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (holo f)
    (bdd_at_infty f) k n

end QExpAction

end M4cP1W2

end

end Regularity
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularForm_mdifferentiable_heckeT =====

theorem ModularForm.mdifferentiable_heckeT : ∀ {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ), MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f) :=
  fun hf k p => PeriodMapPort.Internal.Regularity.M4cP1W2.mdifferentiable_heckeT k p hf

-- ===== Theorems.Thm_ModularForm_mdifferentiable_heckeU =====

theorem ModularForm.mdifferentiable_heckeU : ∀ {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ), MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f) :=
  fun hf k p => PeriodMapPort.Internal.Regularity.M4cP1W2.mdifferentiable_heckeU k p hf

-- ===== P2M.Sol.S_ModularFormClass_isBoundedAt_heckeT =====
-- (shared with P2M.Sol.S_ModularFormClass_isBoundedAt_heckeU,
-- P2M.Sol.S_CuspFormClass_isZeroAt_heckeT and P2M.Sol.S_CuspFormClass_isZeroAt_heckeU)
namespace PeriodMapPort.Internal.Cusps

namespace ModularForm
export _root_.ModularForm (add ext upperTriangularGL heckeMatrix heckeDiagMatrix heckeMatrix_zero heckeDiagMatrix_zero heckeU heckeT heckeU_def heckeT_eq_heckeU_add)
namespace S06W2
open _root_.ModularForm

open UpperHalfPlane OnePoint
open scoped _root_.MatrixGroups _root_.ModularForm

section RatCusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

theorem isCusp_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c Γ) (g : GL (Fin 2) ℚ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g • c, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem isBoundedAt_slash_ratCast [ModularFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsBoundedAt.smul_iff.mp (ModularFormClass.bdd_at_cusps f (isCusp_ratCast_smul hc g))

theorem isZeroAt_slash_ratCast [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k :=
  OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_ratCast_smul hc g))

end RatCusps

section HeckeMatrices

def ratUpperTriangularGL (a b d : ℚ) (had : a * d ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

theorem upperTriangularGL_eq_map (a b d : ℚ) (had : a * d ≠ 0) :
    upperTriangularGL a b d (by exact_mod_cast had) =
      Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (ratUpperTriangularGL a b d had) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ratUpperTriangularGL, upperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_heckeMatrix_eq_map (p j : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeMatrix p j = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeMatrix, hp, ratUpperTriangularGL, upperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_heckeDiagMatrix_eq_map (p : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeDiagMatrix p = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeDiagMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeDiagMatrix, hp, ratUpperTriangularGL, upperTriangularGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

end HeckeMatrices

section Cusps

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}

theorem isBoundedAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsBoundedAt (f i) k) : c.IsBoundedAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.const_boundedAtFilter _ (0 : ℂ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isZeroAt_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, c.IsZeroAt (f i) k) : c.IsZeroAt (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isBoundedAt_heckeU [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isBoundedAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

theorem isBoundedAt_heckeT [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsBoundedAt (heckeT k p ⇑f) k := by
  rw [heckeT_eq_heckeU_add]
  refine (isBoundedAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isBoundedAt_slash_ratCast f g hc

theorem isZeroAt_heckeU [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (heckeU k p ⇑f) k := by
  rw [heckeU_def]
  refine isZeroAt_sum _ fun j _ => ?_
  obtain ⟨g, hg⟩ := exists_heckeMatrix_eq_map p j
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

theorem isZeroAt_heckeT [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    c.IsZeroAt (heckeT k p ⇑f) k := by
  rw [heckeT_eq_heckeU_add]
  refine (isZeroAt_heckeU f p hc).add ?_
  obtain ⟨g, hg⟩ := exists_heckeDiagMatrix_eq_map p
  rw [hg]
  exact isZeroAt_slash_ratCast f g hc

end Cusps

end ModularForm.S06W2

end Cusps
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularFormClass_isBoundedAt_heckeT =====

theorem ModularFormClass.isBoundedAt_heckeT : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsBoundedAt c (ModularForm.heckeT k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isBoundedAt_heckeT f p hc

-- ===== Theorems.Thm_ModularFormClass_isBoundedAt_heckeU =====

theorem ModularFormClass.isBoundedAt_heckeU : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsBoundedAt c (ModularForm.heckeU k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isBoundedAt_heckeU f p hc

-- ===== Theorems.Thm_CuspFormClass_isZeroAt_heckeT =====

theorem CuspFormClass.isZeroAt_heckeT : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isZeroAt_heckeT f p hc

-- ===== Theorems.Thm_CuspFormClass_isZeroAt_heckeU =====

theorem CuspFormClass.isZeroAt_heckeU : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsZeroAt c (ModularForm.heckeU k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isZeroAt_heckeU f p hc

-- ===== Definitions.Def_ModularForm_HeckeOperatorForms =====

set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {N : ℕ} {p : ℕ}

def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k :=
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  { toFun := fun f =>
      { toFun := heckeT k p ⇑f
        slash_action_eq' := fun γ hγ => heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
          (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
        holo' := mdifferentiable_heckeT (ModularFormClass.holo f) k p
        bdd_at_cusps' := fun hc => ModularFormClass.isBoundedAt_heckeT f p hc }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeT k p ⇑(f + g) = heckeT k p ⇑f + heckeT k p ⇑g by rw [ModularForm.coe_add, heckeT_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeT k p ⇑(c • f) = c • heckeT k p ⇑f by rw [ModularForm.IsGLPos.coe_smul, heckeT_smul] }

def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toFun f :=
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0 k hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (ModularFormClass.holo f) k p
      bdd_at_cusps' := fun hc => ModularFormClass.isBoundedAt_heckeU f p hc }
  map_add' f g := DFunLike.coe_injective <|
    show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [ModularForm.coe_add, heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [ModularForm.IsGLPos.coe_smul, heckeU_smul]

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

@[simp] theorem coe_heckeULin_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeULin k hpN f) = heckeU k p ⇑f := rfl

theorem heckeTLin_apply_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeTLin k hp hpN f τ = heckeT k p ⇑f τ := rfl

theorem heckeULin_apply_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULin k hpN f τ = heckeU k p ⇑f τ := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {N : ℕ} {p : ℕ}

def heckeTLin (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) k :=
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  { toFun := fun f =>
      { toFun := heckeT k p ⇑f
        slash_action_eq' := fun γ hγ => heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
          (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
        holo' := mdifferentiable_heckeT (CuspFormClass.holo f) k p
        zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeT f p hc }
    map_add' := fun f g => DFunLike.coe_injective <|
      show heckeT k p ⇑(f + g) = heckeT k p ⇑f + heckeT k p ⇑g by rw [CuspForm.coe_add, heckeT_add]
    map_smul' := fun c f => DFunLike.coe_injective <|
      show heckeT k p ⇑(c • f) = c • heckeT k p ⇑f by rw [CuspForm.IsGLPos.coe_smul, heckeT_smul] }

def heckeULin (k : ℤ) [NeZero N] (hpN : p ∣ N) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 N) k where
  toFun f :=
    { toFun := heckeU k p ⇑f
      slash_action_eq' := fun γ hγ => heckeU_slash_eq_self_of_mem_Gamma0 k hpN
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
      holo' := mdifferentiable_heckeU (CuspFormClass.holo f) k p
      zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }
  map_add' f g := DFunLike.coe_injective <|
    show heckeU k p ⇑(f + g) = heckeU k p ⇑f + heckeU k p ⇑g by rw [CuspForm.coe_add, heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show heckeU k p ⇑(c • f) = c • heckeU k p ⇑f by rw [CuspForm.IsGLPos.coe_smul, heckeU_smul]

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

@[simp] theorem coe_heckeULin_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeULin k hpN f) = heckeU k p ⇑f := rfl

theorem heckeTLin_apply_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeTLin k hp hpN f τ = heckeT k p ⇑f τ := rfl

theorem heckeULin_apply_apply (k : ℤ) [NeZero N] (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    heckeULin k hpN f τ = heckeU k p ⇑f τ := rfl

end CuspForm

end

-- ===== Shared support: functions with equal derivatives on the upper half-plane =====
namespace PeriodMapPort.Internal.Constancy

set_option autoImplicit false

open UpperHalfPlane

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem sub_eq_const_of_forall_hasDerivAt {F G : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt F (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt G (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, F ↑τ - G ↑τ = c := by
  refine ⟨F ↑UpperHalfPlane.I - G ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => F z - G z)
    (fun σ => by have h := (hF σ).sub (hG σ); rw [sub_self] at h; exact h) τ UpperHalfPlane.I

end PeriodMapPort.Internal.Constancy

-- ===== P2M.Sol.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0 =====
namespace PeriodMapPort.Internal.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (Period.IsEquivariantPrimitive)
namespace Period
export _root_.ModularCurve.Period (IsEquivariantPrimitive)
namespace SolExistsPrimitive
open _root_.ModularCurve.Period _root_.ModularCurve

open UpperHalfPlane Filter Topology Complex Function ModularForm Metric
open scoped MatrixGroups Real CongruenceSubgroup ModularForm Manifold
open _root_.PeriodMapPort.Internal.Constancy

local notation "𝕢" => Function.Periodic.qParam

theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (𝕢 h) (2 * π * Complex.I / h * 𝕢 h z) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * ↑π * Complex.I * w / ↑h)
      (2 * ↑π * Complex.I / ↑h) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * ↑π * Complex.I)).div_const (↑h : ℂ)
  have h2 := h1.cexp
  have hval : 2 * (π:ℂ) * Complex.I / ↑h * 𝕢 h z
      = cexp (2 * ↑π * Complex.I * z / ↑h) * (2 * ↑π * Complex.I / ↑h) := by
    simp only [Function.Periodic.qParam]
    ring
  rw [hval]
  exact h2

section Primitive

variable {h : ℝ} {g : ℍ → ℂ}

theorem exists_primitive (hh : 0 < h) (hper : Periodic (g ∘ ofComplex) h)
    (hhol : MDiff g) (hzero : IsZeroAtImInfty g) :
    ∃ G : ℍ → ℂ, (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := by
  have hbdd : IsBoundedAtImInfty g := hzero.boundedAtFilter

  set Φ : ℂ → ℂ := cuspFunction h g with hΦ
  have hΦdiff : DifferentiableOn ℂ Φ (ball 0 1) :=
    differentiableOn_cuspFunction_ball hh hper hhol hbdd
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ, cuspFunction_apply_zero hh (analyticAt_cuspFunction_zero hh hper hhol hbdd) hper]
    exact hzero.valueAtInfty_eq_zero

  set Φ₁ : ℂ → ℂ := dslope Φ 0 with hΦ₁
  have hΦ₁diff : DifferentiableOn ℂ Φ₁ (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds 0 one_pos)).mpr hΦdiff
  have hΦ₁mul : ∀ q : ℂ, q * Φ₁ q = Φ q := fun q => by
    have := sub_smul_dslope Φ 0 q
    simpa [hΦ0, smul_eq_mul] using this

  obtain ⟨Ψ, hΨ0, hΨ⟩ := (hΦ₁diff.isExactOn_ball).with_val_at 0 0

  have hqball : ∀ τ : ℍ, 𝕢 h ↑τ ∈ ball (0:ℂ) 1 := by
    intro τ
    rw [mem_ball_zero_iff, Function.Periodic.norm_qParam]
    have him : (0:ℝ) < Complex.im ↑τ := τ.2
    calc Real.exp (-2 * π * Complex.im ↑τ / h) < Real.exp 0 :=
          Real.exp_lt_exp.mpr (by
            apply div_neg_of_neg_of_pos _ hh
            nlinarith [Real.pi_pos])
      _ = 1 := Real.exp_zero

  refine ⟨fun τ : ℍ => ↑h / (2 * π * Complex.I) * Ψ (𝕢 h ↑τ), fun τ => ?_, ?_⟩
  ·
    have hchain : HasDerivAt (fun z : ℂ => ↑h / (2 * π * Complex.I) * Ψ (𝕢 h z)) (g τ) ↑τ := by
      have h1 : HasDerivAt (fun z : ℂ => Ψ (𝕢 h z))
          (Φ₁ (𝕢 h ↑τ) * (2 * π * Complex.I / h * 𝕢 h ↑τ)) ↑τ :=
        (hΨ _ (hqball τ)).comp (↑τ : ℂ) (hasDerivAt_qParam h ↑τ)
      have h2 := h1.const_mul (↑h / (2 * π * Complex.I))
      convert h2 using 1 <;> try rfl
      have hne : (↑h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
      have h3 : ↑h / (2 * ↑π * Complex.I) * (Φ₁ (𝕢 h ↑τ) * (2 * ↑π * Complex.I / ↑h * 𝕢 h ↑τ))
          = 𝕢 h ↑τ * Φ₁ (𝕢 h ↑τ) := by
        field_simp
      rw [h3, hΦ₁mul]
      exact (eq_cuspFunction τ hh.ne' hper).symm

    refine hchain.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  ·
    have hΨcont : ContinuousAt Ψ 0 :=
      (hΨ 0 (mem_ball_self one_pos)).differentiableAt.continuousAt
    have hq0 : Tendsto (fun τ : ℍ => 𝕢 h ↑τ) atImInfty (𝓝 0) :=
      qParam_tendsto_atImInfty hh
    have : Tendsto (fun τ : ℍ => Ψ (𝕢 h ↑τ)) atImInfty (𝓝 (Ψ 0)) :=
      (hΨcont.tendsto).comp hq0
    rw [hΨ0] at this
    simpa using this.const_mul (↑h / (2 * π * Complex.I))

end Primitive

section ChainRule

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z)) ((g ∣[(2:ℤ)] γ) τ) ↑τ := by

  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]

  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rw [← hfun] at hcomp
  convert hcomp using 1 <;> try rfl
  exact SL_slash_apply (g : ℍ → ℂ) γ τ

end ChainRule

section Assembly

open CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped Pointwise in

theorem natCast_mem_strictPeriods_conj {Γ : Subgroup SL(2, ℤ)} {N : ℕ}
    (hΓ : Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    (N : ℝ) ∈ Subgroup.strictPeriods
      (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ •
        (Γ : Subgroup (GL (Fin 2) ℝ))) := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul]

  have hT1 : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T
      = Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.GeneralLinearGroup.upperRightHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> erw [Matrix.SpecialLinearGroup.map_apply_coe]
    all_goals simp [RingHom.mapMatrix_apply]
  have hTN : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))
      = Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
    rw [zpow_natCast, map_pow, hT1, ← AddChar.map_nsmul_eq_pow]
    norm_num
  rw [← hTN, ← map_mul, ← map_inv, ← map_mul]
  refine Subgroup.mem_map_of_mem _ (hΓ ?_)
  have hTmem : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  exact (Gamma_normal N).conj_mem _ hTmem δ

variable {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)

theorem periodic_slash_comp_ofComplex {N : ℕ}
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (hΓ : Gamma N ≤ Γ) (δ : SL(2, ℤ)) :
    Periodic (((f : ℍ → ℂ) ∣[k] δ) ∘ ofComplex) (N : ℝ) :=
  SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ δ))
    (natCast_mem_strictPeriods_conj hΓ δ)

theorem SL_slash_eq_self_of_mem [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) : (f : ℍ → ℂ) ∣[k] γ = f :=
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

variable {N : ℕ} [NeZero N] [CuspFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) 2]

theorem exists_equivariantPrimitive (hΓ : Gamma N ≤ Γ) :
    ∃ Fprim : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) ∧
      Tendsto Fprim atImInfty (𝓝 0) ∧
      IsEquivariantPrimitive Γ Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => Fprim (δ • w)) atImInfty (𝓝 L) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hN : (0:ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

  have hmaster : ∀ δ : SL(2, ℤ), ∃ G : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ) ∧
      Tendsto G atImInfty (𝓝 0) := fun δ =>
    exists_primitive hN (periodic_slash_comp_ofComplex f hΓ δ)
      ((CuspFormClass.holo f).slash 2 _) (CuspFormClass.zero_at_infty_slash f δ)

  obtain ⟨Fprim, hFprim, hFprim0⟩ := hmaster 1
  have hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ := by
    intro τ
    simpa using hFprim τ
  refine ⟨Fprim, hFf, hFprim0, ?_, ?_⟩
  ·
    intro γ

    have hslash : ((f : ℍ → ℂ) ∣[(2:ℤ)] (γ : SL(2, ℤ))) = f := SL_slash_eq_self_of_mem f γ.2
    have hchain : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => Fprim ((γ : SL(2, ℤ)) • ofComplex z))
        (f τ) ↑τ := by
      intro τ
      have := hasDerivAt_comp_smul hFf (γ : SL(2, ℤ)) τ
      rwa [hslash] at this
    obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hchain hFf
    exact ⟨c, fun z => by simpa using hc z⟩
  ·

    intro δ
    obtain ⟨Gδ, hGδ, hGδ0⟩ := hmaster δ
    have hchain : ∀ τ : ℍ, HasDerivAt (fun z : ℂ => Fprim (δ • ofComplex z))
        (((f : ℍ → ℂ) ∣[(2:ℤ)] δ) τ) ↑τ := fun τ => hasDerivAt_comp_smul hFf δ τ
    obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hchain hGδ
    refine ⟨c, ?_⟩
    have h1 : (fun w : ℍ => Fprim (δ • w)) = fun w : ℍ => (Gδ ∘ ofComplex) ↑w + c := by
      funext w
      have := hc w
      simp only [ofComplex_apply] at this ⊢
      linear_combination this
    rw [h1]
    have : Tendsto (fun w : ℍ => (Gδ ∘ ofComplex) ↑w) atImInfty (𝓝 0) := by
      simpa [Function.comp_def, ofComplex_apply] using hGδ0
    simpa using this.add_const c

end Assembly

section Gamma0

open CongruenceSubgroup

theorem Gamma_le_Gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := fun _ hA =>
  Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1

variable {N : ℕ} [NeZero N] (f : CuspForm (Gamma0 N) 2)

end Gamma0

end ModularCurve.Period.SolExistsPrimitive

open scoped MatrixGroups in

theorem solution {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ Fprim : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) ∧
      Filter.Tendsto Fprim UpperHalfPlane.atImInfty (nhds 0) ∧
      ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ,
        Filter.Tendsto (fun w : UpperHalfPlane => Fprim (δ • w)) UpperHalfPlane.atImInfty (nhds L) :=
  ModularCurve.Period.SolExistsPrimitive.exists_equivariantPrimitive f
    (ModularCurve.Period.SolExistsPrimitive.Gamma_le_Gamma0 N)

end S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0 =====

open scoped MatrixGroups

theorem ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 : ∀ {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), ∃ Fprim : UpperHalfPlane → ℂ,
      (∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) ∧
      Filter.Tendsto Fprim UpperHalfPlane.atImInfty (nhds 0) ∧
      ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim ∧
      ∀ δ : SL(2, ℤ), ∃ L : ℂ,
        Filter.Tendsto (fun w : UpperHalfPlane => Fprim (δ • w)) UpperHalfPlane.atImInfty (nhds L) :=
  @PeriodMapPort.Internal.S_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0.solution

-- ===== P2M.Sol.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt =====
namespace PeriodMapPort.Internal.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt

set_option autoImplicit false

open UpperHalfPlane ModularCurve.Period

open scoped MatrixGroups

open _root_.PeriodMapPort.Internal.Constancy in
theorem solution {Γ : Subgroup SL(2, ℤ)}
    {F G : UpperHalfPlane → ℂ} {f : UpperHalfPlane → ℂ}
    (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F)
    (hG : ModularCurve.Period.IsEquivariantPrimitive Γ G)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ)
    (hGf : ∀ τ : UpperHalfPlane, HasDerivAt (G ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hF.periodHom = hG.periodHom := by
  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hFf hGf
  refine DFunLike.ext _ _ fun γ => ?_
  show hF.period (Additive.toMul γ) = hG.period (Additive.toMul γ)
  exact hF.period_congr hG c (fun z => by simpa [ofComplex_apply] using hc z) _

end S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt =====

open scoped MatrixGroups

theorem ModularCurve.Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt : ∀ {Γ : Subgroup SL(2, ℤ)} {F G : UpperHalfPlane → ℂ} {f : UpperHalfPlane → ℂ} (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F) (hG : ModularCurve.Period.IsEquivariantPrimitive Γ G) (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) (hGf : ∀ τ : UpperHalfPlane, HasDerivAt (G ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ), hF.periodHom = hG.periodHom :=
  @PeriodMapPort.Internal.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt.solution

-- ===== P2M.Sol.S_ModularCurve_periodMap_eq_periodHom =====
namespace PeriodMapPort.Internal.S_ModularCurve_periodMap_eq_periodHom

set_option autoImplicit false

open scoped MatrixGroups

theorem solution {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    {Fprim : UpperHalfPlane → ℂ} (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    ModularCurve.periodMap N f = hFprim.periodHom := by
  obtain ⟨F₁, hF₁⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨F₀, h₀, h⟩ := ModularCurve.periodMap_def N f (F := F₁) hF₁
  rw [h]
  exact h₀.2.2.1.periodHom_eq_of_hasDerivAt hFprim h₀.1 hFf

end S_ModularCurve_periodMap_eq_periodHom
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularCurve_periodMap_eq_periodHom =====

open scoped MatrixGroups

theorem ModularCurve.periodMap_eq_periodHom : ∀ {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} {Fprim : UpperHalfPlane → ℂ} (hFprim : ModularCurve.Period.IsEquivariantPrimitive (CongruenceSubgroup.Gamma0 N) Fprim) (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (Fprim ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ), ModularCurve.periodMap N f = hFprim.periodHom :=
  @PeriodMapPort.Internal.S_ModularCurve_periodMap_eq_periodHom.solution

-- ===== P2M.Sol.S_ModularCurve_periodMap_heckeTLin =====
namespace PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin

set_option Elab.async false
set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve
export _root_.ModularCurve (periodMap Period.IsEquivariantPrimitive Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom)
namespace Period
export _root_.ModularCurve.Period (IsEquivariantPrimitive CuspForm.exists_equivariantPrimitive_gamma0)
namespace SolHeckeT
open _root_.ModularCurve.Period _root_.ModularCurve

open UpperHalfPlane Filter Topology Complex
open _root_.PeriodMapPort.Internal.Constancy

namespace HeckeAnalytic

open Matrix CongruenceSubgroup

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

@[scoped simp] lemma repMat_none (ℓ : ℕ) : repMat ℓ none = !![(ℓ : ℤ), 0; 0, 1] := rfl

@[scoped simp] lemma repMat_some (ℓ : ℕ) (j : Fin ℓ) : repMat ℓ (some j) = !![1, (j : ℤ); 0, (ℓ : ℤ)] :=
  rfl

lemma det_repMat (ℓ : ℕ) (i : Option (Fin ℓ)) : (repMat ℓ i).det = (ℓ : ℤ) := by
  cases i <;> simp [repMat, Matrix.det_fin_two_of]

lemma exists_cocycle {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _

  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos

    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  cases i with
  | none =>

    by_cases hcdvd : (ℓ : ℤ) ∣ c
    ·
      obtain ⟨c', hc'⟩ := hcdvd
      have hdetδ : Matrix.det !![a, (ℓ : ℤ) * b; c', d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + b * hc'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      ·
        erw [Gamma0_mem]
        show ((c' : ℤ) : ZMod N) = 0
        have hcopN : Nat.Coprime N ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
        have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
          simpa [Int.gcd_natCast_natCast] using hcopN)
        have hNc' : (N : ℤ) ∣ c' := by
          refine hcop.dvd_of_dvd_mul_left ?_
          rw [← hc']
          exact hNc
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a, (ℓ : ℤ) * b; c', d] * repMat ℓ none
        rw [hgmat, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = a * (ℓ : ℤ) + (ℓ : ℤ) * b * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = a * 0 + (ℓ : ℤ) * b * 1
          ring
        · show (0 * a + 1 * c : ℤ) = c' * (ℓ : ℤ) + d * 0
          linear_combination hc'
        · show (0 * b + 1 * d : ℤ) = c' * 0 + d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key c d hcdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - a * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · erw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] * repMat ℓ (some j')
        rw [hgmat, repMat_none, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = (ℓ : ℤ) * a * 1 + (b - a * (j' : ℤ)) * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = (ℓ : ℤ) * a * (j' : ℤ) + (b - a * (j' : ℤ)) * (ℓ : ℤ)
          ring
        · show (0 * a + 1 * c : ℤ) = c * 1 + e * 0
          ring
        · show (0 * b + 1 * d : ℤ) = c * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
  | some j =>

    by_cases hpdvd : (ℓ : ℤ) ∣ (a + (j : ℤ) * c)
    ·
      obtain ⟨p', hp'⟩ := hpdvd
      have hdetδ : Matrix.det !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - d * hp'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · erw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] * repMat ℓ none
        rw [hgmat, repMat_some, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = p' * (ℓ : ℤ) + (b + (j : ℤ) * d) * 0
          linear_combination hp'
        · show (1 * b + (j : ℤ) * d : ℤ) = p' * 0 + (b + (j : ℤ) * d) * 1
          ring
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = c * (ℓ : ℤ) + (ℓ : ℤ) * d * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = c * 0 + (ℓ : ℤ) * d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + c * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · erw [Gamma0_mem]
        show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast
        rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
          mul_zero]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
        rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
          ring
        · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
          ring

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

@[scoped simp] lemma repGL_coe (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat ℓ i).map (algebraMap ℤ ℝ) := rfl

lemma mapGL_coe' (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

lemma map_int_mul (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

def heckeSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i

section BoardBridge

variable (ℓ : ℕ) [NeZero ℓ]

theorem repGL_some_eq_heckeMatrix (j : Fin ℓ) :
    repGL ℓ (some j) = ModularForm.heckeMatrix ℓ j := by
  refine Units.ext ?_
  rw [repGL_coe, ModularForm.val_heckeMatrix (NeZero.ne ℓ), repMat_some]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

theorem repGL_none_eq_heckeDiagMatrix :
    repGL ℓ none = ModularForm.heckeDiagMatrix ℓ := by
  refine Units.ext ?_
  rw [repGL_coe, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ), repMat_none]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

theorem heckeSlashSum_eq_heckeT (k : ℤ) (f : UpperHalfPlane → ℂ) :
    heckeSlashSum k ℓ f = ModularForm.heckeT k ℓ f := by
  rw [heckeSlashSum, ModularForm.heckeT_def, Fintype.sum_option, repGL_none_eq_heckeDiagMatrix,
    add_comm, ← Fin.sum_univ_eq_sum_range (fun j => f ∣[k] ModularForm.heckeMatrix ℓ j) ℓ]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [repGL_some_eq_heckeMatrix]

end BoardBridge

end HeckeAnalytic
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

open UpperHalfPlane Filter Topology Complex Function ModularForm Matrix CongruenceSubgroup Subgroup HeckeEis

section ChainRule

theorem slash_two_apply_of_det_pos (f : ℍ → ℂ) {β : GL (Fin 2) ℝ} (hβ : 0 < β.val.det)
    (τ : ℍ) :
    (f ∣[(2 : ℤ)] β) τ = f (β • τ) * (↑β.val.det / denom β ↑τ ^ 2) := by
  have hβ' : 0 < β.det.val := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [ModularForm.slash_apply, σ, if_pos hβ', ContinuousAlgEquiv.refl_apply]
  have habs : |β.det.val| = β.val.det := by
    rw [abs_of_pos hβ', Matrix.GeneralLinearGroup.val_det_apply]
  rw [habs, show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, _root_.zpow_neg, zpow_ofNat, mul_assoc,
    ← div_eq_mul_inv]

theorem hasDerivAt_comp_smul_of_det_pos {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) {β : GL (Fin 2) ℝ}
    (hβ : 0 < β.val.det) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (β • ofComplex z)) ((g ∣[(2 : ℤ)] β) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (β • ofComplex z))
      = (G ∘ ofComplex) ∘ fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (β • τ))
      ((fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (β • τ)
  have hinner : HasDerivAt (fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ))
      (↑β.val.det / denom β ↑τ ^ 2) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul hβ τ).hasDerivAt
  have hcomp := houter.comp (↑τ : ℂ) hinner
  rw [← hfun] at hcomp
  rw [slash_two_apply_of_det_pos g hβ τ]
  exact hcomp

end ChainRule
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

noncomputable local instance (N ℓ : ℕ) [NeZero ℓ] :
    Fintype (Gamma0 N ⧸ heckeUpper N ℓ) :=
  (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex

section CosetRep

variable (N ℓ : ℕ) [NeZero ℓ]

noncomputable def alphaGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((alphaMat ℓ).map (algebraMap ℤ ℝ)) (by
    have h : ((alphaMat ℓ).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (alphaMat ℓ).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_alphaMat]
    simp [NeZero.ne ℓ])

@[scoped simp]
theorem alphaGL_coe :
    (alphaGL ℓ : Matrix (Fin 2) (Fin 2) ℝ) = (alphaMat ℓ).map (algebraMap ℤ ℝ) :=
  rfl

theorem alphaGL_val_det : (alphaGL ℓ).val.det = (ℓ : ℝ) := by
  show ((alphaMat ℓ).map (algebraMap ℤ ℝ)).det = (ℓ : ℝ)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_alphaMat]
  simp

noncomputable def gammaToGL : Gamma0 N →* GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ).comp (Gamma0 N).subtype

@[scoped simp]
theorem gammaToGL_apply (x : Gamma0 N) :
    gammaToGL N x = Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) :=
  rfl

theorem gammaToGL_val_det (x : Gamma0 N) : (gammaToGL N x).val.det = 1 := by
  rw [gammaToGL_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]

theorem gammaToGL_smul (x : Gamma0 N) (z : ℍ) : gammaToGL N x • z = (x : SL(2, ℤ)) • z :=
  rfl

noncomputable def heckeCosetRep (q : Gamma0 N ⧸ heckeUpper N ℓ) : GL (Fin 2) ℝ :=
  alphaGL ℓ * gammaToGL N (Quotient.out q)⁻¹

theorem heckeCosetRep_def (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    heckeCosetRep N ℓ q = alphaGL ℓ * gammaToGL N (Quotient.out q)⁻¹ :=
  rfl

theorem heckeCosetRep_val_det (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    (heckeCosetRep N ℓ q).val.det = (ℓ : ℝ) := by
  rw [heckeCosetRep_def, Units.val_mul, Matrix.det_mul, alphaGL_val_det, gammaToGL_val_det,
    mul_one]

theorem heckeCosetRep_val_det_pos (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    0 < (heckeCosetRep N ℓ q).val.det := by
  rw [heckeCosetRep_val_det]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

theorem gammaToGL_heckeConj_mul_alphaGL (h : heckeUpper N ℓ) :
    gammaToGL N (heckeConj N ℓ h) * alphaGL ℓ = alphaGL ℓ * gammaToGL N (h : Gamma0 N) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (heckeConjMat ℓ ((((h : Gamma0 N) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ)).map
        (algebraMap ℤ ℝ) * ((alphaMat ℓ).map (algebraMap ℤ ℝ))
      = ((alphaMat ℓ).map (algebraMap ℤ ℝ))
        * ((((h : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))
  rw [← HeckeAnalytic.map_int_mul, ← HeckeAnalytic.map_int_mul,
    heckeConjMat_mul_alphaMat ((mem_heckeUpper N ℓ).mp h.2)]

omit [NeZero ℓ] in

theorem coe_transferAux_inv_smul (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    ((transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q) : heckeUpper N ℓ) : Gamma0 N)
      = (Quotient.out q)⁻¹ * (γ * Quotient.out (γ⁻¹ • q)) := by
  rw [coe_transferAux, smul_inv_smul]

theorem heckeCosetRep_mul_gammaToGL (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    heckeCosetRep N ℓ q * gammaToGL N γ
      = gammaToGL N (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
        * heckeCosetRep N ℓ (γ⁻¹ • q) := by
  rw [heckeCosetRep_def, heckeCosetRep_def, ← mul_assoc, gammaToGL_heckeConj_mul_alphaGL,
    mul_assoc, mul_assoc, ← map_mul (gammaToGL N), ← map_mul (gammaToGL N)]
  refine congrArg (fun x : Gamma0 N => alphaGL ℓ * gammaToGL N x) ?_
  rw [coe_transferAux_inv_smul]
  group

end CosetRep
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

section Telescoping

variable {N ℓ : ℕ} [NeZero ℓ] {Fprim : ℍ → ℂ}

theorem sum_heckeCosetRep_smul_sub (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (γ : Gamma0 N) (z : ℍ) :
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        (Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
          - Fprim (heckeCosetRep N ℓ q • z))
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by

  have hterm : ∀ q : Gamma0 N ⧸ heckeUpper N ℓ,
      Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
        = Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
          + hF.period
              (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q))) := by
    intro q
    have h1 : heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z)
        = ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)) : Gamma0 N)
            : SL(2, ℤ)) • (heckeCosetRep N ℓ (γ⁻¹ • q) • z) := by
      rw [show ((γ : SL(2, ℤ)) • z) = gammaToGL N γ • z from rfl, ← mul_smul,
        heckeCosetRep_mul_gammaToGL, mul_smul]
      rfl
    rw [h1]
    have h2 := hF.sub_eq_period
      (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
      (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
    linear_combination h2

  calc
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        (Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
          - Fprim (heckeCosetRep N ℓ q • z))
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          (Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
            + hF.period
                (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
            - Fprim (heckeCosetRep N ℓ q • z)) :=
        Finset.sum_congr rfl fun q _ => by rw [hterm q]
    _ = (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z))
          + (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
              hF.period
                (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q))))
          - ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z))
          + (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
              hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)))
          - ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z) := by
        rw [(MulAction.bijective (γ⁻¹ : Gamma0 N)).sum_comp
            (fun q : Gamma0 N ⧸ heckeUpper N ℓ => Fprim (heckeCosetRep N ℓ q • z)),
          (MulAction.bijective (γ⁻¹ : Gamma0 N)).sum_comp
            (fun q : Gamma0 N ⧸ heckeUpper N ℓ => hF.period
              (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)))]
    _ = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by
        ring

end Telescoping
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

section Main

variable {N ℓ : ℕ} [NeZero ℓ]

variable (N ℓ) in

noncomputable def heckeQuotSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, f ∣[(2 : ℤ)] heckeCosetRep N ℓ q

theorem hasDerivAt_sum_heckeCosetRep {Fprim : ℍ → ℂ} {f : ℍ → ℂ}
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt
      ((fun w : ℍ => ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • w))
        ∘ ofComplex)
      (heckeQuotSlashSum N ℓ f τ) ↑τ := by
  have key := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Gamma0 N ⧸ heckeUpper N ℓ)))
    (x := (↑τ : ℂ))
    (A := fun (q : Gamma0 N ⧸ heckeUpper N ℓ) (z : ℂ) =>
      Fprim (heckeCosetRep N ℓ q • ofComplex z))
    (A' := fun q : Gamma0 N ⧸ heckeUpper N ℓ => (f ∣[(2 : ℤ)] heckeCosetRep N ℓ q) τ)
    (fun q _ => hasDerivAt_comp_smul_of_det_pos hFf (heckeCosetRep_val_det_pos N ℓ q) τ)
  rw [show heckeQuotSlashSum N ℓ f τ
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, (f ∣[(2 : ℤ)] heckeCosetRep N ℓ q) τ from
    Finset.sum_apply τ Finset.univ fun q => f ∣[(2 : ℤ)] heckeCosetRep N ℓ q]
  exact key

theorem periodHom_heckeQuotSlashSum {Fprim Fprim' : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (heckeQuotSlashSum N ℓ f τ) ↑τ) :
    hF'.periodHom = heckeOperatorHom N ℓ ℂ hF.periodHom := by

  have hGsub : ∀ (γ : Gamma0 N) (z : ℍ),
      (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z)))
        - (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z))
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
            hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by
    intro γ z
    rw [← Finset.sum_sub_distrib]
    exact sum_heckeCosetRep_smul_sub hF γ z

  have hGequiv : IsEquivariantPrimitive (Gamma0 N)
      (fun w : ℍ => ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • w)) :=
    fun γ =>
      ⟨∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)),
        fun z => hGsub γ z⟩

  have hGperiod : ∀ γ : Gamma0 N,
      hGequiv.period γ
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
            hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by
    intro γ
    rw [← hGequiv.sub_eq_period γ UpperHalfPlane.I]
    exact hGsub γ UpperHalfPlane.I

  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hF'f (hasDerivAt_sum_heckeCosetRep hFf)
  refine AddMonoidHom.ext fun x => ?_
  show hF'.period (Additive.toMul x)
    = heckeOperatorHom N ℓ ℂ hF.periodHom (Additive.ofMul (Additive.toMul x))
  rw [hF'.period_congr hGequiv c (fun w => by
      simpa only [Function.comp_apply, ofComplex_apply] using hc w) (Additive.toMul x),
    hGperiod (Additive.toMul x), heckeOperatorHom_apply]
  rfl

end Main
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

section Bridge

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ]

variable (N ℓ) in

def HeckeCosetMatch : Prop :=
  ∃ e : Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ),
    ∀ i : Option (Fin ℓ), ∃ δ : Gamma0 N,
      HeckeAnalytic.repGL ℓ i = gammaToGL N δ * heckeCosetRep N ℓ (e i)

omit [NeZero N] in

theorem heckeSlashSum_eq_heckeQuotSlashSum (hmatch : HeckeCosetMatch N ℓ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    HeckeAnalytic.heckeSlashSum 2 ℓ f = heckeQuotSlashSum N ℓ f := by
  obtain ⟨e, he⟩ := hmatch
  rw [HeckeAnalytic.heckeSlashSum, heckeQuotSlashSum,
    ← Equiv.sum_comp e fun q => f ∣[(2 : ℤ)] heckeCosetRep N ℓ q]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨δ, hδ⟩ := he i
  rw [hδ, SlashAction.slash_mul,
    hf (gammaToGL N δ) (Subgroup.mem_map.mpr ⟨(δ : SL(2, ℤ)), δ.2, rfl⟩)]

omit [NeZero N] in

theorem periodHom_heckeSlashSum_of_match (hmatch : HeckeCosetMatch N ℓ)
    (f : CuspForm (Gamma0 N) 2) {Fprim Fprim' : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (HeckeAnalytic.heckeSlashSum 2 ℓ (⇑f) τ) ↑τ) :
    hF'.periodHom = heckeOperatorHom N ℓ ℂ hF.periodHom := by
  refine periodHom_heckeQuotSlashSum hF hFf hF' fun τ => ?_
  rw [← heckeSlashSum_eq_heckeQuotSlashSum hmatch (SlashInvariantFormClass.slash_action_eq f)]
  exact hF'f τ

end Bridge
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

open HeckeAnalytic

section Representatives

def unipotentUpper (N : ℕ) (t : ℤ) : Gamma0 N :=
  ⟨⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, by
    erw [Gamma0_mem]
    show ((0 : ℤ) : ZMod N) = 0
    exact Int.cast_zero⟩

theorem unipotentUpper_mul (N : ℕ) (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t = unipotentUpper N (s + t) := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, t; 0, 1] = !![1, s + t; 0, 1]
  rw [Matrix.mul_fin_two]
  refine Matrix.ext fun x y => ?_
  fin_cases x <;> fin_cases y
  · show (1 * 1 + s * 0 : ℤ) = 1
    ring
  · show (1 * t + s * 1 : ℤ) = s + t
    ring
  · show (0 * 1 + 1 * 0 : ℤ) = 0
    ring
  · show (0 * t + 1 * 1 : ℤ) = 1
    ring

theorem unipotentUpper_zero (N : ℕ) : unipotentUpper N 0 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 1
  rw [Matrix.one_fin_two]

theorem inv_unipotentUpper (N : ℕ) (t : ℤ) :
    (unipotentUpper N t)⁻¹ = unipotentUpper N (-t) :=
  inv_eq_of_mul_eq_one_right (by
    rw [unipotentUpper_mul, show t + -t = 0 by ring, unipotentUpper_zero])

variable {N ℓ : ℕ}

theorem hecke_bezout (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (ℓ : ℤ) * Nat.gcdA ℓ N + (N : ℤ) * Nat.gcdB ℓ N = 1 := by
  have h := Nat.gcd_eq_gcd_ab ℓ N
  rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)] at h
  exact_mod_cast h.symm

theorem not_dvd_gcdB (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : ¬ (ℓ : ℤ) ∣ Nat.gcdB ℓ N := by
  intro hdvd
  have h1 : (ℓ : ℤ) ∣ 1 := by
    rw [← hecke_bezout hℓ hℓN]
    exact dvd_add (dvd_mul_right _ _) (hdvd.mul_left _)
  have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  have h3 : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.one_lt
  omega

def bezoutRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Gamma0 N :=
  ⟨⟨!![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hecke_bezout hℓ hℓN⟩, by
    erw [Gamma0_mem]
    show ((N : ℤ) : ZMod N) = 0
    rw [Int.cast_natCast]
    exact ZMod.natCast_self N⟩

def cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none => bezoutRep hℓ hℓN
  | some j => unipotentUpper N (-(j : ℤ))

@[scoped simp]
theorem cosetRep_none (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    cosetRep hℓ hℓN (none : Option (Fin ℓ)) = bezoutRep hℓ hℓN :=
  rfl

@[scoped simp]
theorem cosetRep_some (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (j : Fin ℓ) :
    cosetRep hℓ hℓN (some j) = unipotentUpper N (-(j : ℤ)) :=
  rfl

def rawDelta (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none =>
    ⟨⟨!![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1], by
      rw [Matrix.det_fin_two_of]
      linear_combination hecke_bezout hℓ hℓN⟩, by
      erw [Gamma0_mem]
      show ((N : ℤ) : ZMod N) = 0
      rw [Int.cast_natCast]
      exact ZMod.natCast_self N⟩
  | some _ => 1

theorem repMat_mul_cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repMat ℓ i * (((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          * alphaMat ℓ := by
  match i with
  | none =>
    show !![(ℓ : ℤ), 0; 0, 1] * !![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)]
        = !![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1] * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show ((ℓ : ℤ) * Nat.gcdA ℓ N + 0 * (N : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 1 + -Nat.gcdB ℓ N * 0
      ring
    · show ((ℓ : ℤ) * -Nat.gcdB ℓ N + 0 * (ℓ : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 0 + -Nat.gcdB ℓ N * (ℓ : ℤ)
      ring
    · show (0 * Nat.gcdA ℓ N + 1 * (N : ℤ) : ℤ) = (N : ℤ) * 1 + 1 * 0
      ring
    · show (0 * -Nat.gcdB ℓ N + 1 * (ℓ : ℤ) : ℤ) = (N : ℤ) * 0 + 1 * (ℓ : ℤ)
      ring
  | some j =>
    show !![1, (j : ℤ); 0, (ℓ : ℤ)] * !![1, -(j : ℤ); 0, 1]
        = (1 : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.one_mul]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show (1 * 1 + (j : ℤ) * 0 : ℤ) = 1
      ring
    · show (1 * -(j : ℤ) + (j : ℤ) * 1 : ℤ) = 0
      ring
    · show (0 * 1 + (ℓ : ℤ) * 0 : ℤ) = 0
      ring
    · show (0 * -(j : ℤ) + (ℓ : ℤ) * 1 : ℤ) = (ℓ : ℤ)
      ring

end Representatives
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

section Bijection

variable {N ℓ : ℕ}

def cosetOfRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    Gamma0 N ⧸ heckeUpper N ℓ :=
  (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ)

theorem cosetOfRep_def (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    cosetOfRep hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

theorem unipotentUpper_mul_mem_iff (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (s + t) := by
  rw [unipotentUpper_mul, mem_heckeUpper]
  exact Iff.rfl

theorem unipotentUpper_mul_bezoutRep_not_mem (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (s : ℤ) :
    unipotentUpper N s * bezoutRep hℓ hℓN ∉ heckeUpper N ℓ := by
  intro hmem
  rw [mem_heckeUpper] at hmem

  have hentry : (((unipotentUpper N s * bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ))) 0 1
      = 1 * -Nat.gcdB ℓ N + s * (ℓ : ℤ) :=
    (Matrix.two_mul_expl
      (((unipotentUpper N s : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (((bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).2.1
  rw [hentry,
    show (1 : ℤ) * -Nat.gcdB ℓ N + s * (ℓ : ℤ) = s * (ℓ : ℤ) - Nat.gcdB ℓ N by ring] at hmem

  exact not_dvd_gcdB hℓ hℓN ((dvd_sub_right (dvd_mul_left _ _)).mp hmem)

theorem cosetOfRep_injective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Injective (cosetOfRep (N := N) hℓ hℓN) := by
  intro i i' h
  rw [cosetOfRep_def, cosetOfRep_def, QuotientGroup.eq] at h
  match i, i' with
  | none, none => rfl
  | some j, none =>

    exact absurd h (by
      rw [cosetRep_some, cosetRep_none, inv_unipotentUpper, neg_neg]
      exact unipotentUpper_mul_bezoutRep_not_mem hℓ hℓN (j : ℤ))
  | none, some j' =>

    refine absurd ((heckeUpper N ℓ).inv_mem h) ?_
    rw [cosetRep_some, cosetRep_none, _root_.mul_inv_rev, inv_inv, inv_unipotentUpper, neg_neg]
    exact unipotentUpper_mul_bezoutRep_not_mem hℓ hℓN (j' : ℤ)
  | some j, some j' =>

    rw [cosetRep_some, cosetRep_some, inv_unipotentUpper, neg_neg,
      unipotentUpper_mul_mem_iff] at h

    have hj := j.isLt
    have hj' := j'.isLt
    have hzero : (j : ℤ) + -(j' : ℤ) = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
      rw [Int.natAbs_natCast]
      omega
    have hval : (j : ℕ) = (j' : ℕ) := by omega
    exact congrArg some (Fin.ext hval)

theorem dvd_of_alphaMat_mul_eq_mul_alphaMat {X Y : Matrix (Fin 2) (Fin 2) ℤ}
    (h : alphaMat ℓ * X = Y * alphaMat ℓ) : (ℓ : ℤ) ∣ X 0 1 := by
  have h01 : (alphaMat ℓ * X) 0 1 = (Y * alphaMat ℓ) 0 1 := by rw [h]
  rw [(Matrix.two_mul_expl (alphaMat ℓ) X).2.1, (Matrix.two_mul_expl Y (alphaMat ℓ)).2.1,
    alphaMat_apply_zero_zero, alphaMat_apply_zero_one, alphaMat_apply_one_one] at h01
  exact ⟨Y 0 1, by linear_combination h01⟩

theorem repMat_some_zero (hpos : 0 < ℓ) : repMat ℓ (some ⟨0, hpos⟩) = alphaMat ℓ := by
  rw [repMat_some]
  rfl

theorem cosetOfRep_surjective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Surjective (cosetOfRep (N := N) hℓ hℓN) := by
  intro q
  obtain ⟨γ, rfl⟩ : ∃ γ : Gamma0 N, (γ : Gamma0 N ⧸ heckeUpper N ℓ) = q :=
    ⟨Quotient.out q, QuotientGroup.out_eq' q⟩

  obtain ⟨δ, -, m, hm⟩ := exists_cocycle hℓ hℓN (γ⁻¹ : Gamma0 N).2 (some ⟨0, hℓ.pos⟩)
  refine ⟨m, ?_⟩
  rw [cosetOfRep_def, QuotientGroup.eq, ← (heckeUpper N ℓ).inv_mem_iff, _root_.mul_inv_rev,
    inv_inv, mem_heckeUpper]

  refine dvd_of_alphaMat_mul_eq_mul_alphaMat
    (Y := (δ : Matrix (Fin 2) (Fin 2) ℤ)
      * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ?_
  have hcoe : (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    rfl
  calc alphaMat ℓ
      * (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (alphaMat ℓ * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hcoe, mul_assoc]
    _ = (repMat ℓ (some ⟨0, hℓ.pos⟩)
          * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [repMat_some_zero hℓ.pos]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m)
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hm]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ) * (repMat ℓ m
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [mul_assoc]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ)
          * ((((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
            * alphaMat ℓ) := by
        rw [repMat_mul_cosetRep]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ)
          * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * alphaMat ℓ := by
        rw [mul_assoc]

noncomputable def heckeCosetEquiv (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ) :=
  Equiv.ofBijective (cosetOfRep hℓ hℓN)
    ⟨cosetOfRep_injective hℓ hℓN, cosetOfRep_surjective hℓ hℓN⟩

@[scoped simp]
theorem heckeCosetEquiv_apply (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    heckeCosetEquiv hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

end Bijection
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

section CosetMatch

variable {N ℓ : ℕ} [NeZero ℓ]

theorem repGL_eq_rawDelta_mul (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repGL ℓ i = gammaToGL N (rawDelta hℓ hℓN i)
      * (alphaGL ℓ * gammaToGL N (cosetRep hℓ hℓN i)⁻¹) := by
  have key : repGL ℓ i * gammaToGL N (cosetRep hℓ hℓN i)
      = gammaToGL N (rawDelta hℓ hℓN i) * alphaGL ℓ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repMat ℓ i).map (algebraMap ℤ ℝ)
        * ((((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (algebraMap ℤ ℝ))
      = ((((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (algebraMap ℤ ℝ))
        * ((alphaMat ℓ).map (algebraMap ℤ ℝ))
    rw [← HeckeAnalytic.map_int_mul, ← HeckeAnalytic.map_int_mul, repMat_mul_cosetRep]
  calc repGL ℓ i
      = (repGL ℓ i * gammaToGL N (cosetRep hℓ hℓN i))
          * (gammaToGL N (cosetRep hℓ hℓN i))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = (gammaToGL N (rawDelta hℓ hℓN i) * alphaGL ℓ)
          * (gammaToGL N (cosetRep hℓ hℓN i))⁻¹ := by
        rw [key]
    _ = gammaToGL N (rawDelta hℓ hℓN i)
          * (alphaGL ℓ * gammaToGL N (cosetRep hℓ hℓN i)⁻¹) := by
        rw [mul_assoc, map_inv]

theorem exists_heckeCosetRep_coe_eq (γ : Gamma0 N) :
    ∃ ε : Gamma0 N, heckeCosetRep N ℓ (γ : Gamma0 N ⧸ heckeUpper N ℓ)
      = gammaToGL N ε * (alphaGL ℓ * gammaToGL N γ⁻¹) := by
  obtain ⟨h, hout⟩ := QuotientGroup.mk_out_eq_mul (heckeUpper N ℓ) γ
  refine ⟨heckeConj N ℓ h⁻¹, ?_⟩
  rw [heckeCosetRep_def,
    show Quotient.out ((γ : Gamma0 N ⧸ heckeUpper N ℓ)) = γ * (h : Gamma0 N) from hout,
    _root_.mul_inv_rev, map_mul, ← mul_assoc, ← mul_assoc]
  congr 1

  exact (gammaToGL_heckeConj_mul_alphaGL N ℓ h⁻¹).symm

theorem heckeCosetMatch (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : HeckeCosetMatch N ℓ := by
  refine ⟨heckeCosetEquiv hℓ hℓN, fun i => ?_⟩
  obtain ⟨ε, hε⟩ := exists_heckeCosetRep_coe_eq (ℓ := ℓ) (cosetRep hℓ hℓN i)
  refine ⟨rawDelta hℓ hℓN i * ε⁻¹, ?_⟩
  rw [show heckeCosetEquiv hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) from rfl,
    hε, map_mul, map_inv, mul_assoc, ← mul_assoc ((gammaToGL N ε)⁻¹), inv_mul_cancel, one_mul]
  exact repGL_eq_rawDelta_mul hℓ hℓN i

end CosetMatch
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic

end ModularCurve.Period.SolHeckeT
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve

end
open scoped PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT

theorem solution {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero N := ⟨fun h => hℓN (h ▸ dvd_zero ℓ)⟩
  obtain ⟨F, hFf, -, hFe, -⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨F', hF'f, -, hF'e, -⟩ :=
    ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 (CuspForm.heckeTLin 2 hℓ hℓN f)
  rw [ModularCurve.periodMap_eq_periodHom hF'e hF'f, ModularCurve.periodMap_eq_periodHom hFe hFf]
  refine ModularCurve.Period.SolHeckeT.periodHom_heckeSlashSum_of_match
    (ModularCurve.Period.SolHeckeT.heckeCosetMatch hℓ hℓN) f hFe hFf hF'e fun τ => ?_
  rw [ModularCurve.Period.SolHeckeT.HeckeAnalytic.heckeSlashSum_eq_heckeT ℓ 2 ⇑f,
    ← CuspForm.coe_heckeTLin_apply 2 hℓ hℓN f]
  exact hF'f τ

end S_ModularCurve_periodMap_heckeTLin
end Internal
end PeriodMapPort

-- ===== Theorems.Thm_ModularCurve_periodMap_heckeTLin =====

theorem ModularCurve.periodMap_heckeTLin : ∀ {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) :=
  @PeriodMapPort.Internal.S_ModularCurve_periodMap_heckeTLin.solution
