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

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms
public import MathlibExt.NumberTheory.ModularForms.TwoCuspReductionSpan

import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# The Hecke sums `heckeT` and `heckeU` on functions on the upper half-plane

For `f : ℍ → ℂ`, `ModularForm.heckeU k p f` (from `TwoCuspReductionSpan`) is
`τ ↦ p⁻¹ ∑_{j < p} f ((τ + j) / p)` and `ModularForm.heckeT k p f` adds `p ^ (k - 1) f (p τ)`.
This file gives their values, their `q`-expansion coefficients for `p ≠ 0`
(`ModularFormClass.qCoeff_heckeU`, `ModularFormClass.qCoeff_heckeT`), their regularity (holomorphy, period `1`, boundedness and
vanishing at the cusps), their invariance under `Γ₀(N)` (`heckeT` for a prime `p ∤ N`, `heckeU`
for `p ∣ N`), and the linear maps `heckeTLin` and `heckeULin` they induce on modular and cusp
forms for `Γ₀(N)`: the classical Hecke operators `T_p` and `U_p`.
-/

@[expose] public section

-- ===== Definitions.Def_ModularForm_HeckeOperator =====

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularForm

theorem denom_heckeUpperMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (heckeUpperMatrix p j) τ = p := by
  simp [UpperHalfPlane.denom, val_heckeUpperMatrix hp]

theorem coe_heckeUpperMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeUpperMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_heckeUpperMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_heckeUpperMatrix hp]

theorem slash_heckeUpperMatrix_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (j : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    (f ∣[k] heckeUpperMatrix p j) τ = (p : ℂ)⁻¹ * f (heckeUpperMatrix p j • τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [ModularForm.slash_apply, σ_heckeUpperMatrix, det_heckeUpperMatrix hp,
    denom_heckeUpperMatrix hp]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [mul_assoc, ← zpow_add₀ hp', show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

/-- The Hecke sum `heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p` in weight `k`, for a
function `f` on the upper half-plane. With Mathlib's slash action this is
`heckeT k p f τ = p⁻¹ ∑_{j < p} f ((τ + j) / p) + p ^ (k - 1) f (p τ)` for `p ≠ 0`
(`heckeT_apply`), and `heckeT k 0 f = f`. For `p ≠ 0` it acts on the `q`-expansion coefficients
of a modular form for a group with `1` as a strict period by `coeffHeckeT`
(`ModularFormClass.qCoeff_heckeT`).

On modular forms for `Γ₀(N)` it is the classical Hecke operator `T_p` only for a prime `p` not
dividing `N` (`ModularForm.heckeTLin`); for composite `p` it is not `T_p`, and for a prime
`p ∣ N` the classical operator is `U_p`, given by `heckeU k p` (`ModularForm.heckeULin`). On
forms for a group `GammaH N H` between `Γ₁(N)` and `Γ₀(N)`, the classical `T_p` for a prime
`p ∤ N` is `heckeU k p f + (⟨p⟩ f) ∣[k] heckeDiagMatrix p`, where the diamond operator `⟨p⟩`
slashes by a matrix of `Γ₀(N)` whose lower-right entry is `p` modulo `N`. So the classical
`T_p f` equals `heckeT k p f` exactly when `⟨p⟩ f = f`, for instance when `p` modulo `N` lies in
`H`. In Lean, `CuspForm.coe_heckeTLinH_apply` gives this formula for `CuspForm.heckeTLinH` on
cusp forms for `GammaH N H`, under the explicit hypothesis `CuspForm.StableT N H k p`; when that
hypothesis does not hold, `CuspForm.heckeTLinH` is defined to be zero. -/
def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

theorem heckeT_eq_heckeU_add (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f = heckeU k p f + f ∣[k] heckeDiagMatrix p := rfl

theorem heckeT_def (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) :
    heckeT k p f =
      (∑ j ∈ Finset.range p, f ∣[k] heckeUpperMatrix p j) + f ∣[k] heckeDiagMatrix p := rfl

@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

theorem heckeU_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeU k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ) := by
  simp only [heckeU, Finset.sum_apply, slash_heckeUpperMatrix_apply k hp, Finset.mul_sum]

theorem heckeT_apply (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    heckeT k p f τ = (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ)
      + (p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ) := by
  rw [heckeT, Pi.add_apply, heckeU_apply k hp, slash_heckeDiagMatrix_apply k hp]

@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

theorem heckeT_add (k : ℤ) (p : ℕ) (f g : UpperHalfPlane → ℂ) :
    heckeT k p (f + g) = heckeT k p f + heckeT k p g := by
  simp only [heckeT, heckeU_add, SlashAction.add_slash]
  abel

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

/-- The coefficient formula of `heckeT k p`: the `n`-th coefficient is
`a (n * p) + p ^ (k - 1) * a (n / p)` when `p ∣ n`, and `a (n * p)` otherwise. For `p ≠ 0`, this
is how `heckeT k p` acts on the `q`-expansion coefficients `a` of a modular form for a group with
`1` as a strict period (`ModularFormClass.qCoeff_heckeT`); at `p = 0` it is not, as
`heckeT k 0 f = f`. -/
def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

/-- The coefficient formula of `heckeU k p`: `n ↦ a (n * p)`. For `p ≠ 0`, this is how
`heckeU k p` acts on the `q`-expansion coefficients `a` of a modular form for a group with `1` as
a strict period (`ModularFormClass.qCoeff_heckeU`); at `p = 0` it is not, as
`heckeU k 0 f = 0`. -/
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

-- ===== Regularity of heckeU and heckeT at i∞ =====

namespace UpperHalfPlane

open Function

/-- A function `f` on `ℍ` such that `f ∘ ofComplex` has period `1` takes the same value at two
points whose images in `ℂ` differ by a natural number. -/
theorem apply_eq_of_coe_eq_add_nat {f : ℍ → ℂ} (hf : Periodic (f ∘ ofComplex) 1) {τ₁ τ₂ : ℍ}
    (m : ℕ) (h : (τ₁ : ℂ) = τ₂ + m) : f τ₁ = f τ₂ := by
  have h1 : (f ∘ ofComplex) ((τ₂ : ℂ) + m) = (f ∘ ofComplex) (τ₂ : ℂ) := by
    have := hf.nat_mul m
    rw [mul_one] at this
    exact this (τ₂ : ℂ)
  simp only [comp_apply] at h1
  rw [← h, ofComplex_apply, ofComplex_apply] at h1
  exact h1

end UpperHalfPlane

namespace ModularForm

open UpperHalfPlane Function
open scoped MatrixGroups

/-- The lower-left entry of `heckeUpperMatrix p j` is `0`, also for `p = 0`, where the matrix is
the identity. -/
theorem heckeUpperMatrix_one_zero (p j : ℕ) :
    ((heckeUpperMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeUpperMatrix hp]; rfl

/-- The lower-left entry of `heckeDiagMatrix p` is `0`, also for `p = 0`, where the matrix is the
identity. -/
theorem heckeDiagMatrix_one_zero (p : ℕ) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeDiagMatrix hp]; rfl

/-- `heckeU k p` sends a function bounded at `i∞` to one bounded at `i∞`. -/
theorem isBoundedAtImInfty_heckeU {f : ℍ → ℂ} (k : ℤ) (p : ℕ) (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeUpperMatrix_one_zero p j))

/-- `heckeT k p` sends a function bounded at `i∞` to one bounded at `i∞`. -/
theorem isBoundedAtImInfty_heckeT {f : ℍ → ℂ} (k : ℤ) (p : ℕ) (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeT k p f) :=
  (isBoundedAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

/-- For `p ≠ 0`, `heckeUpperMatrix p j` sends `1 +ᵥ τ` to the image of `τ` under
`heckeUpperMatrix p (j + 1)`. -/
theorem heckeUpperMatrix_smul_vadd {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    heckeUpperMatrix p j • ((1 : ℝ) +ᵥ τ) = heckeUpperMatrix p (j + 1) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeUpperMatrix_smul hp, coe_heckeUpperMatrix_smul hp, coe_vadd]
  push_cast
  ring

/-- For `p ≠ 0`, the images of `τ` under `heckeUpperMatrix p p` and `heckeUpperMatrix p 0`
differ by `1`. -/
theorem coe_heckeUpperMatrix_smul_self {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    ((heckeUpperMatrix p p • τ : ℍ) : ℂ) = (heckeUpperMatrix p 0 • τ : ℍ) + (1 : ℕ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [coe_heckeUpperMatrix_smul hp, coe_heckeUpperMatrix_smul hp]
  field_simp
  push_cast
  ring

/-- For `p ≠ 0`, the image of `1 +ᵥ τ` under `heckeDiagMatrix p` is the image of `τ` plus `p`. -/
theorem coe_heckeDiagMatrix_smul_vadd {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix p • ((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = (heckeDiagMatrix p • τ : ℍ) + (p : ℕ) := by
  rw [coe_heckeDiagMatrix_smul hp, coe_heckeDiagMatrix_smul hp, coe_vadd]
  push_cast
  ring

/-- For `p ≠ 0` and `f` with `f ∘ ofComplex` of period `1`, summing `f` over the images of
`1 +ᵥ τ` under `heckeUpperMatrix p j`, `j < p`, gives the sum over the images of `τ`. -/
theorem sum_heckeUpperMatrix_smul_vadd {f : ℍ → ℂ} {p : ℕ} (hp : p ≠ 0)
    (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ) := by
  simp only [heckeUpperMatrix_smul_vadd hp]
  have h0 := Finset.sum_range_succ' (fun j => f (heckeUpperMatrix p j • τ)) p
  have h1 := Finset.sum_range_succ (fun j => f (heckeUpperMatrix p j • τ)) p
  rw [apply_eq_of_coe_eq_add_nat hf 1 (coe_heckeUpperMatrix_smul_self hp τ)] at h1
  exact add_right_cancel (h0.symm.trans h1)

/-- If `f ∘ ofComplex` has period `1`, so does `heckeU k p f ∘ ofComplex`. -/
theorem periodic_heckeU_comp_ofComplex {f : ℍ → ℂ} (k : ℤ) (p : ℕ)
    (hf : Periodic (f ∘ ofComplex) 1) : Periodic (heckeU k p f ∘ ofComplex) 1 := by
  refine periodic_comp_ofComplex (h := 1) fun τ ↦ ?_
  by_cases hp : p = 0
  · simp only [hp, heckeU_zero_left, Pi.zero_apply]
  · rw [heckeU_apply k hp, heckeU_apply k hp, sum_heckeUpperMatrix_smul_vadd hp hf]

/-- If `f ∘ ofComplex` has period `1`, so does `heckeT k p f ∘ ofComplex`. -/
theorem periodic_heckeT_comp_ofComplex {f : ℍ → ℂ} (k : ℤ) (p : ℕ)
    (hf : Periodic (f ∘ ofComplex) 1) : Periodic (heckeT k p f ∘ ofComplex) 1 := by
  refine periodic_comp_ofComplex (h := 1) fun τ ↦ ?_
  by_cases hp : p = 0
  · simp only [hp, heckeT_zero_left]
    exact apply_eq_of_coe_eq_add_nat hf 1 (by rw [coe_vadd]; push_cast; ring)
  · rw [heckeT_apply k hp, heckeT_apply k hp, sum_heckeUpperMatrix_smul_vadd hp hf,
      apply_eq_of_coe_eq_add_nat hf p (coe_heckeDiagMatrix_smul_vadd hp τ)]

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

theorem heckeUpperMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeUpperMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeUpperMatrix p j' := by
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

theorem heckeUpperMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeUpperMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
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
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeUpperMatrix p j' := by
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
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeUpperMatrix p x.val := by
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

theorem heckeUpperMatrix_mul_of_dvd (g : SL(2, ℤ)) (hc : (p : ℤ) ∣ g 1 0) (x : ZMod p) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeUpperMatrix p x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeUpperMatrix p
          (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
  have hc0 : ((g 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  set x' := affinePerm g hc0 x with hx'
  obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + x.val * g 1 1 - x'.val * (g 0 0 + x.val * g 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hx', affinePerm_apply]
    linear_combination (-(((g 0 1 : ℤ) : ZMod p) + x * ((g 1 1 : ℤ) : ZMod p))) *
      unit_of_apply_one_zero_eq_zero g hc0
      - (((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * x) * x) * hc0
  exact heckeUpperMatrix_mul_of_eq (NeZero.ne p) g x.val x'.val e (by linear_combination he)

variable {N : ℕ} (k : ℤ)

theorem heckeU_slash_mapGL (hpN : p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeU k p f ∣[k] (mapGL ℝ g) = heckeU k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpN).trans hcN
  rw [heckeU_eq_sum_zmod k f, SlashAction.sum_slash]
  calc ∑ x : ZMod p, (f ∣[k] heckeUpperMatrix p x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod p, f ∣[k] heckeUpperMatrix p
          (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeUpperMatrix_mul_of_dvd g hc x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N := by
          rw [CongruenceSubgroup.Gamma0_mem, hg']
          push_cast
          rw [CongruenceSubgroup.Gamma0_mem.mp hg, mul_zero]
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : ZMod p, f ∣[k] heckeUpperMatrix p x.val :=
        Equiv.sum_comp (affinePerm g _) (fun x ↦ f ∣[k] heckeUpperMatrix p x.val)

end heckeU

section heckeT

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeUpperMatrix p j.val)

@[scoped simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[scoped simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeUpperMatrix p j.val := rfl

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
      obtain ⟨g', hg', hmul⟩ := heckeUpperMatrix_mul_of_eq' hp g j.val e he
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
      obtain ⟨g', hg', hmul⟩ :=
        heckeUpperMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
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

@[expose] public section

-- ===== Theorems.Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0 =====

namespace ModularForm

/-- For a prime `p` not dividing `N`, `heckeT k p` sends a function invariant under the
weight-`k` slash action of `Γ₀(N)` to another such function. -/
theorem heckeT_slash_eq_self_of_mem_Gamma0 : ∀ {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))), SlashAction.map k γ (ModularForm.heckeT k p f) = ModularForm.heckeT k p f :=
  @PeriodMapPort.Internal.SlashInvariance.ModularForm.heckeT_slash_eq_self_of_mem_Gamma0'

end ModularForm

-- ===== Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0 =====

namespace ModularForm

/-- For `p` dividing `N`, `heckeU k p` sends a function invariant under the weight-`k` slash
action of `Γ₀(N)` to another such function. -/
theorem heckeU_slash_eq_self_of_mem_Gamma0 : ∀ {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))), SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f :=
  @PeriodMapPort.Internal.SlashInvariance.ModularForm.heckeU_slash_eq_self_of_mem_Gamma0'

end ModularForm

end

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

section Regularity

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

theorem mdifferentiable_heckeU (hf : MDiff f) : MDiff (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => MDiff g) (fun _ _ ha hb => ha.add hb)
    mdifferentiable_const (fun _ _ => hf.slash k _)

theorem mdifferentiable_heckeT (hf : MDiff f) : MDiff (heckeT k p f) :=
  (mdifferentiable_heckeU k p hf).add (hf.slash k _)

theorem isZeroAtImInfty_heckeU (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsZeroAtImInfty g)
    (fun _ _ ha hb => ha.add hb) (zero_zeroAtFilter atImInfty)
    (fun j _ => hf.slash k (heckeUpperMatrix_one_zero p j))

theorem isZeroAtImInfty_heckeT (hf : IsZeroAtImInfty f) :
    IsZeroAtImInfty (heckeT k p f) :=
  (isZeroAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

end Regularity

section Uniqueness

theorem qExpansion_coeff_unique' {g : ℍ → ℂ} (hcont : Continuous g) {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction 1 g) 0)
    (hs : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam 1 τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion 1 g).coeff m :=
  UpperHalfPlane.qExpansion_coeff_unique (ContinuousMap.mk g hcont) one_pos hg hs m

end Uniqueness

section QExpAction

theorem qParam_one (z : ℂ) : Periodic.qParam 1 z = exp (2 * π * I * z) := by
  simp [Periodic.qParam]

variable {p : ℕ} (hp : p ≠ 0)

include hp in
theorem natCast_ne_zero' : (p : ℂ) ≠ 0 := by exact_mod_cast hp

include hp in

theorem qParam_heckeUpperMatrix_smul (j : ℕ) (τ : ℍ) :
    Periodic.qParam 1 ((heckeUpperMatrix p j • τ : ℍ) : ℂ)
      = exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j := by
  rw [qParam_one, coe_heckeUpperMatrix_smul hp, ← Complex.exp_nat_mul, ← Complex.exp_add]
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
      ((p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ)) := by
  have hF : ∀ τ' : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ' ^ m) (f τ') :=
    hasSum_qExpansion one_pos hper hhol hbdd

  have h1 : HasSum (fun m ↦ ∑ j ∈ Finset.range p,
      qCoeff f m • (exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j) ^ m)
      (∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ)) := by
    refine hasSum_sum fun j _ => ?_
    have := hF (heckeUpperMatrix p j • τ)
    rwa [qParam_heckeUpperMatrix_smul hp j τ] at this

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

@[expose] public section

-- ===== Theorems.Thm_ModularForm_mdifferentiable_heckeT =====

namespace ModularForm

/-- `heckeT k p` sends a holomorphic function on `ℍ` to a holomorphic function. -/
theorem mdifferentiable_heckeT : ∀ {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ), MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f) :=
  fun hf k p => PeriodMapPort.Internal.Regularity.M4cP1W2.mdifferentiable_heckeT k p hf

end ModularForm

-- ===== Theorems.Thm_ModularForm_mdifferentiable_heckeU =====

namespace ModularForm

/-- `heckeU k p` sends a holomorphic function on `ℍ` to a holomorphic function. -/
theorem mdifferentiable_heckeU : ∀ {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ), MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f) :=
  fun hf k p => PeriodMapPort.Internal.Regularity.M4cP1W2.mdifferentiable_heckeU k p hf

end ModularForm

-- ===== The q-expansion coefficients of heckeU and heckeT =====

namespace ModularFormClass

/-- The `q`-expansion coefficients of `heckeU k p f`, for `p ≠ 0` and a modular form `f` for a
group with `1` as a strict period: the `n`-th one is the `n * p`-th one of `f`. -/
theorem qCoeff_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeU k p ⇑f) n
      = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff ⇑f) n :=
  PeriodMapPort.Internal.Regularity.M4cP1W2.qCoeff_heckeU_class hp f hΓ n

/-- The `q`-expansion coefficients of `heckeT k p f`, for `p ≠ 0` and a modular form `f` for a
group with `1` as a strict period, are given by `coeffHeckeT`. -/
theorem qCoeff_heckeT {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeT k p ⇑f) n
      = ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff ⇑f) n :=
  PeriodMapPort.Internal.Regularity.M4cP1W2.qCoeff_heckeT_class hp f hΓ n

end ModularFormClass

end

-- ===== P2M.Sol.S_ModularFormClass_isBoundedAt_heckeT =====
-- (shared with P2M.Sol.S_ModularFormClass_isBoundedAt_heckeU,
-- P2M.Sol.S_CuspFormClass_isZeroAt_heckeT and P2M.Sol.S_CuspFormClass_isZeroAt_heckeU)
namespace PeriodMapPort.Internal.Cusps

namespace ModularForm
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

theorem exists_heckeUpperMatrix_eq_map (p j : ℕ) :
    ∃ g : GL (Fin 2) ℚ, heckeUpperMatrix p j = Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by rw [heckeUpperMatrix_zero, map_one]⟩
  · refine ⟨ratUpperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeUpperMatrix, hp, ratUpperTriangularGL, upperTriangularGL,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

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
  obtain ⟨g, hg⟩ := exists_heckeUpperMatrix_eq_map p j
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
  obtain ⟨g, hg⟩ := exists_heckeUpperMatrix_eq_map p j
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

@[expose] public section

-- ===== Theorems.Thm_ModularFormClass_isBoundedAt_heckeT =====

namespace ModularFormClass

/-- For a modular form `f` of weight `k` on an arithmetic subgroup `Γ`, `heckeT k p f` is
bounded at every cusp of `Γ`. -/
theorem isBoundedAt_heckeT : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsBoundedAt c (ModularForm.heckeT k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isBoundedAt_heckeT f p hc

end ModularFormClass

-- ===== Theorems.Thm_ModularFormClass_isBoundedAt_heckeU =====

namespace ModularFormClass

/-- For a modular form `f` of weight `k` on an arithmetic subgroup `Γ`, `heckeU k p f` is
bounded at every cusp of `Γ`. -/
theorem isBoundedAt_heckeU : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsBoundedAt c (ModularForm.heckeU k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isBoundedAt_heckeU f p hc

end ModularFormClass

-- ===== Theorems.Thm_CuspFormClass_isZeroAt_heckeT =====

namespace CuspFormClass

/-- For a cusp form `f` of weight `k` on an arithmetic subgroup `Γ`, `heckeT k p f` vanishes at
every cusp of `Γ`. -/
theorem isZeroAt_heckeT : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsZeroAt c (ModularForm.heckeT k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isZeroAt_heckeT f p hc

end CuspFormClass

-- ===== Theorems.Thm_CuspFormClass_isZeroAt_heckeU =====

namespace CuspFormClass

/-- For a cusp form `f` of weight `k` on an arithmetic subgroup `Γ`, `heckeU k p f` vanishes at
every cusp of `Γ`. -/
theorem isZeroAt_heckeU : ∀ {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ), OnePoint.IsZeroAt c (ModularForm.heckeU k p ⇑f) k :=
  fun f p _ hc => PeriodMapPort.Internal.Cusps.ModularForm.S06W2.isZeroAt_heckeU f p hc

end CuspFormClass

-- ===== Definitions.Def_ModularForm_HeckeOperatorForms =====

set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {N : ℕ} {p : ℕ}

/-- The Hecke operator `T_p` on modular forms of weight `k` for `Γ₀(N)`, for a prime `p` not
dividing `N`, as a `ℂ`-linear map; it acts on the underlying functions by `heckeT k p`. -/
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

/-- The Hecke operator `U_p` on modular forms of weight `k` for `Γ₀(N)`, for a divisor `p` of
the level `N ≠ 0`, as a `ℂ`-linear map; it acts on the underlying functions by `heckeU k p`. -/
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

/-- The Hecke operator `T_p` on cusp forms of weight `k` for `Γ₀(N)`, for a prime `p` not
dividing `N`, as a `ℂ`-linear map; it acts on the underlying functions by `heckeT k p`. -/
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

/-- The Hecke operator `U_p` on cusp forms of weight `k` for `Γ₀(N)`, for a divisor `p` of the
level `N ≠ 0`, as a `ℂ`-linear map; it acts on the underlying functions by `heckeU k p`. -/
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

end
