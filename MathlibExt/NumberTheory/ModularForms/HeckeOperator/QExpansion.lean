/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_mdifferentiable_heckeT.lean`,
`P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean`,
`Theorems/Thm_ModularForm_mdifferentiable_heckeU.lean`,
`P2M/Sol/S_ModularForm_mdifferentiable_heckeU.lean`,
`Theorems/Thm_ModularFormClass_qCoeff_heckeT.lean`,
`P2M/Sol/S_ModularFormClass_qCoeff_heckeT.lean`,
`Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean`,
`P2M/Sol/S_ModularFormClass_qCoeff_heckeU.lean`,
`Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean`
and
`P2M/Sol/S_ModularFormClass_eq_of_forall_qCoeff_eq.lean`
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

public import MathlibExt.NumberTheory.ModularForms.HeckeOperator.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# `q`-expansions of Hecke operators

The Hecke operators `heckeU k p` and `heckeT k p` preserve holomorphy and
boundedness at `i∞`, and act on `q`-expansion coefficients (period `1`) by
`coeffHeckeU p` and `coeffHeckeT k p`. A modular form for a group containing
the translation by `1` is determined by its `q`-expansion coefficients.

## Main results

* `ModularForm.mdifferentiable_heckeU`, `ModularForm.mdifferentiable_heckeT`
* `ModularFormClass.qCoeff_heckeU`, `ModularFormClass.qCoeff_heckeT`
* `ModularFormClass.eq_of_forall_qCoeff_eq`
-/

@[expose] public section

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace ModularForm

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

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

/-- The `U`-type Hecke sum preserves holomorphy. -/
public theorem mdifferentiable_heckeU (hf : MDiff f) : MDiff (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => MDiff g) (fun _ _ ha hb => ha.add hb)
    mdifferentiable_const (fun _ _ => hf.slash k _)

/-- The `T`-type Hecke operator preserves holomorphy. -/
public theorem mdifferentiable_heckeT (hf : MDiff f) : MDiff (heckeT k p f) :=
  (mdifferentiable_heckeU k p hf).add (hf.slash k _)

/-- The `U`-type Hecke sum preserves boundedness at `i∞`. -/
public theorem isBoundedAtImInfty_heckeU (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeUpperMatrix_one_zero p j))

/-- The `T`-type Hecke operator preserves boundedness at `i∞`. -/
public theorem isBoundedAtImInfty_heckeT (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeT k p f) :=
  (isBoundedAtImInfty_heckeU k p hf).add (hf.slash k (heckeDiagMatrix_one_zero p))

private theorem apply_eq_of_coe_eq_add_nat (hf : Periodic (f ∘ ofComplex) 1) {τ₁ τ₂ : ℍ}
    (m : ℕ) (h : (τ₁ : ℂ) = τ₂ + m) : f τ₁ = f τ₂ := by
  have h1 : (f ∘ ofComplex) ((τ₂ : ℂ) + m) = (f ∘ ofComplex) (τ₂ : ℂ) := by
    have := hf.nat_mul m
    rw [mul_one] at this
    exact this (τ₂ : ℂ)
  simp only [comp_apply] at h1
  rw [← h, ofComplex_apply, ofComplex_apply] at h1
  exact h1

variable {p} in
private theorem heckeUpperMatrix_smul_vadd (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    heckeUpperMatrix p j • ((1 : ℝ) +ᵥ τ) = heckeUpperMatrix p (j + 1) • τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeUpperMatrix_smul hp, coe_heckeUpperMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in
private theorem coe_heckeUpperMatrix_smul_self (hp : p ≠ 0) (τ : ℍ) :
    ((heckeUpperMatrix p p • τ : ℍ) : ℂ) = (heckeUpperMatrix p 0 • τ : ℍ) + (1 : ℕ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [coe_heckeUpperMatrix_smul hp, coe_heckeUpperMatrix_smul hp]
  field_simp
  push_cast
  ring

variable {p} in
private theorem coe_heckeDiagMatrix_smul_vadd (hp : p ≠ 0) (τ : ℍ) :
    ((heckeDiagMatrix p • ((1 : ℝ) +ᵥ τ) : ℍ) : ℂ) = (heckeDiagMatrix p • τ : ℍ) + (p : ℕ) := by
  rw [coe_heckeDiagMatrix_smul hp, coe_heckeDiagMatrix_smul hp, coe_vadd]
  push_cast
  ring

variable {p} in
private theorem sum_heckeUpperMatrix_smul_vadd (hp : p ≠ 0) (hf : Periodic (f ∘ ofComplex) 1)
    (τ : ℍ) :
    ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • ((1 : ℝ) +ᵥ τ))
      = ∑ j ∈ Finset.range p, f (heckeUpperMatrix p j • τ) := by
  simp only [heckeUpperMatrix_smul_vadd hp]
  have h0 := Finset.sum_range_succ' (fun j => f (heckeUpperMatrix p j • τ)) p
  have h1 := Finset.sum_range_succ (fun j => f (heckeUpperMatrix p j • τ)) p
  rw [apply_eq_of_coe_eq_add_nat hf 1 (coe_heckeUpperMatrix_smul_self hp τ)] at h1
  exact add_right_cancel (h0.symm.trans h1)

private theorem heckeU_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeU k p f ((1 : ℝ) +ᵥ τ) = heckeU k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeU_zero_left, Pi.zero_apply]
  · rw [heckeU_apply k hp, heckeU_apply k hp, sum_heckeUpperMatrix_smul_vadd hp hf]

private theorem heckeT_vadd (hf : Periodic (f ∘ ofComplex) 1) (τ : ℍ) :
    heckeT k p f ((1 : ℝ) +ᵥ τ) = heckeT k p f τ := by
  by_cases hp : p = 0
  · simp only [hp, heckeT_zero_left]
    exact apply_eq_of_coe_eq_add_nat hf 1 (by rw [coe_vadd]; push_cast; ring)
  · rw [heckeT_apply k hp, heckeT_apply k hp, sum_heckeUpperMatrix_smul_vadd hp hf,
      apply_eq_of_coe_eq_add_nat hf p (coe_heckeDiagMatrix_smul_vadd hp τ)]

private theorem periodic_comp_ofComplex_of_vadd {g : ℍ → ℂ}
    (hg : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) : Periodic (g ∘ ofComplex) 1 := by
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

/-- The `U`-type Hecke sum preserves periodicity with period `1`. -/
public theorem periodic_heckeU_comp_ofComplex (hf : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeU k p f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeU_vadd k p hf)

/-- The `T`-type Hecke operator preserves periodicity with period `1`. -/
public theorem periodic_heckeT_comp_ofComplex (hf : Periodic (f ∘ ofComplex) 1) :
    Periodic (heckeT k p f ∘ ofComplex) 1 :=
  periodic_comp_ofComplex_of_vadd (heckeT_vadd k p hf)

end ModularForm

namespace ModularFormClass

open ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

private theorem hasSum_qCoeff [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) τ

/-- A modular form for a group containing the translation by `1` is determined by
its `q`-expansion coefficients. -/
public theorem eq_of_forall_qCoeff_eq [ModularFormClass F Γ k] {f g : F}
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g := by
  refine DFunLike.ext f g fun τ => ?_
  have hf := hasSum_qCoeff f hΓ τ
  have hg := hasSum_qCoeff g hΓ τ
  simp only [h] at hf
  exact hf.unique hg

private theorem qParam_one (z : ℂ) : Periodic.qParam 1 z = exp (2 * π * I * z) := by
  simp [Periodic.qParam]

section QExpAction

variable {p : ℕ} (hp : p ≠ 0)

include hp in
private theorem qParam_heckeUpperMatrix_smul (j : ℕ) (τ : ℍ) :
    Periodic.qParam 1 ((heckeUpperMatrix p j • τ : ℍ) : ℂ)
      = exp (2 * π * I * τ / p) * exp (2 * π * I / p) ^ j := by
  rw [qParam_one, coe_heckeUpperMatrix_smul hp, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  field_simp

include hp in
private theorem qParam_heckeDiagMatrix_smul (τ : ℍ) :
    Periodic.qParam 1 ((heckeDiagMatrix p • τ : ℍ) : ℂ) = Periodic.qParam 1 τ ^ p := by
  rw [qParam_one, qParam_one, coe_heckeDiagMatrix_smul hp, ← Complex.exp_nat_mul]
  congr 1
  ring

include hp in
private theorem exp_div_pow (τ : ℍ) : exp (2 * π * I * τ / p) ^ p = Periodic.qParam 1 τ := by
  rw [qParam_one, ← Complex.exp_nat_mul]
  congr 1
  have : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  field_simp

include hp in
private theorem sum_rootOfUnity_pow (m : ℕ) :
    ∑ j ∈ Finset.range p, (exp (2 * π * I / p) ^ j) ^ m = if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp
  have hswap : ∀ j : ℕ, (exp (2 * π * I / p) ^ j) ^ m = (exp (2 * π * I / p) ^ m) ^ j :=
    fun j => by rw [← pow_mul, ← pow_mul, Nat.mul_comm j m]
  simp only [hswap]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr h]
    simp
  · have hne : exp (2 * π * I / p) ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
    rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm m p, pow_mul, hζ.pow_eq_one, one_pow,
      sub_self, zero_div]

private theorem not_dvd_of_not_mem_range {m : ℕ} (hm : m ∉ Set.range (fun l : ℕ ↦ l * p)) :
    ¬ p ∣ m := by
  rintro ⟨l, rfl⟩
  exact hm ⟨l, by simp [mul_comm]⟩

variable {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
  (hbdd : IsBoundedAtImInfty f)

include hp hper hhol hbdd in
private theorem hasSum_average (τ : ℍ) :
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
  have h4 : ((fun m ↦ if p ∣ m then (p : ℂ) * qCoeff f m * exp (2 * π * I * τ / p) ^ m
      else 0) ∘ fun l : ℕ ↦ l * p) =
      fun l ↦ (p : ℂ) * (qCoeff f (l * p) * Periodic.qParam 1 τ ^ l) := by
    funext l
    simp only [comp_apply, ite_eq_left (dvd_mul_left p l)]
    rw [mul_comm l p, pow_mul, exp_div_pow hp τ]
    ring
  rw [h4] at h3
  have h5 := h3.mul_left ((p : ℂ)⁻¹)
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  simp only [← mul_assoc, inv_mul_cancel₀ hp', one_mul] at h5
  exact h5

include hp hper hhol hbdd in
private theorem hasSum_diag (τ : ℍ) :
    HasSum (fun n : ℕ ↦ if p ∣ n then
        (p : ℂ) ^ (k - 1) * qCoeff f (n / p) * Periodic.qParam 1 τ ^ n else 0)
      ((p : ℂ) ^ (k - 1) * f (heckeDiagMatrix p • τ)) := by
  have hD := (hasSum_qExpansion one_pos hper hhol hbdd (heckeDiagMatrix p • τ)).mul_left
    ((p : ℂ) ^ (k - 1))
  rw [qParam_heckeDiagMatrix_smul hp τ] at hD
  have hinj : Function.Injective (fun l : ℕ ↦ l * p) := mul_left_injective₀ hp
  refine (hinj.hasSum_iff (fun m hm => by simp [not_dvd_of_not_mem_range hm])).mp ?_
  convert hD using 1
  funext l
  simp only [comp_apply, ite_eq_left (dvd_mul_left p l),
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hp), smul_eq_mul]
  rw [← pow_mul, mul_comm l p, mul_assoc]
  rfl

include hp hper hhol hbdd in
private theorem hasSum_heckeU (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeU p (qCoeff f) n • Periodic.qParam 1 τ ^ n)
      (heckeU k p f τ) := by
  rw [heckeU_apply k hp]
  simpa only [coeffHeckeU_apply, smul_eq_mul] using hasSum_average hp hper hhol hbdd τ

include hp hper hhol hbdd in
private theorem hasSum_heckeT (τ : ℍ) :
    HasSum (fun n : ℕ ↦ coeffHeckeT k p (qCoeff f) n • Periodic.qParam 1 τ ^ n)
      (heckeT k p f τ) := by
  rw [heckeT_apply k hp]
  convert (hasSum_average hp hper hhol hbdd τ).add (hasSum_diag (k := k) hp hper hhol hbdd τ)
    using 1
  funext n
  rw [coeffHeckeT_apply, smul_eq_mul]
  split_ifs <;> ring

include hp hper hhol hbdd in
private theorem qCoeff_heckeU_of_periodic (n : ℕ) :
    qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  (qExpansion_coeff_unique (f := ContinuousMap.mk _ (mdifferentiable_heckeU k p hhol).continuous)
    one_pos
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeU_comp_ofComplex k p hper)
      (mdifferentiable_heckeU k p hhol) (isBoundedAtImInfty_heckeU k p hbdd))
    (hasSum_heckeU (k := k) hp hper hhol hbdd) n).symm

include hp hper hhol hbdd in
private theorem qCoeff_heckeT_of_periodic (n : ℕ) :
    qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n :=
  (qExpansion_coeff_unique (f := ContinuousMap.mk _ (mdifferentiable_heckeT k p hhol).continuous)
    one_pos
    (analyticAt_cuspFunction_zero one_pos (periodic_heckeT_comp_ofComplex k p hper)
      (mdifferentiable_heckeT k p hhol) (isBoundedAtImInfty_heckeT k p hbdd))
    (hasSum_heckeT (k := k) hp hper hhol hbdd) n).symm

end QExpAction

/-- The `U`-type Hecke sum acts on `q`-expansion coefficients by `coeffHeckeU`. -/
public theorem qCoeff_heckeU [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    qCoeff (heckeU k p f) n = coeffHeckeU p (qCoeff f) n :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeU_of_periodic hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) n

/-- The `T`-type Hecke operator acts on `q`-expansion coefficients by `coeffHeckeT`. -/
public theorem qCoeff_heckeT [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    qCoeff (heckeT k p f) n = coeffHeckeT k p (qCoeff f) n :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  qCoeff_heckeT_of_periodic hp (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) n

end ModularFormClass
