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

`Theorems/Thm_ModularCurve_cosetPoly_smul.lean`,
`P2M/Sol/S_ModularCurve_cosetPoly_smul.lean`,
`Theorems/Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean`,
`P2M/Sol/S_ModularCurve_hasSum_qParam_heckeMatrix_smul.lean`,
`Theorems/Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean`,
and
`P2M/Sol/S_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean`
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

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomialData
public import MathlibExt.NumberTheory.ModularForms.OldForms
public import MathlibExt.NumberTheory.ModularForms.TwoCuspReductionSpan
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Polynomial
open scoped MatrixGroups ModularForm OnePoint

namespace ModularCurve

namespace CosetPoly

open ModularForm

private theorem mapGL_mk_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (h : A.det = 1) (i j : Fin 2) :
    ((mapGL ℝ (⟨A, h⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((A i j : ℤ) : ℝ) :=
  rfl

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

private theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), heckeUpperMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeUpperMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Units.val_mul, ne_eq, hp, not_false_eq_true,
        val_heckeUpperMatrix, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
        Int.coe_castRingHom, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.map_apply, Fin.sum_univ_two, one_mul,
        Matrix.cons_val_one, mapGL_mk_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_one,
        mul_zero, add_zero, Fin.mk_one, zero_mul, zero_add, Int.cast_sub]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

private theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), heckeUpperMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Units.val_mul, ne_eq, hp, not_false_eq_true,
        val_heckeUpperMatrix, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
        Int.coe_castRingHom, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.map_apply, Fin.sum_univ_two, one_mul,
        Matrix.cons_val_one, val_heckeDiagMatrix, mapGL_mk_apply, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, mul_zero, add_zero, Fin.mk_one, mul_one, zero_add, zero_mul]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

private theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeUpperMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Units.val_mul, ne_eq, hp, not_false_eq_true,
        val_heckeDiagMatrix, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
        Int.coe_castRingHom, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.map_apply, Fin.sum_univ_two,
        Matrix.cons_val_one, zero_mul, add_zero, val_heckeUpperMatrix, mapGL_mk_apply, Int.cast_mul,
        Int.cast_natCast, mul_one, Int.cast_sub, mul_zero, Fin.mk_one, one_mul, zero_add]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

private theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Units.val_mul, ne_eq, hp, not_false_eq_true,
        val_heckeDiagMatrix, mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
        Int.coe_castRingHom, Matrix.mul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.map_apply, Fin.sum_univ_two,
        Matrix.cons_val_one, zero_mul, add_zero, mapGL_mk_apply, Int.cast_mul, Int.cast_natCast,
        mul_zero, Fin.mk_one, mul_one, zero_add, one_mul]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section projectiveLine

variable {p : ℕ}

private def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeUpperMatrix p j.val)

@[scoped simp] private theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[scoped simp] private theorem heckeRep_coe (j : ZMod p) :
    heckeRep p j = heckeUpperMatrix p j.val := rfl

variable [Fact p.Prime]

variable (p) in
private def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p);
      ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) -
            ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p) = 1 by
          linear_combination this]
      exact one_ne_zero)

@[scoped simp] private theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] private theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] private theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] private theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

private theorem heckeRep_mul (g : SL(2, ℤ)) (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    · rw [ite_eq_left (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      exact heckeDiagMatrix_mul_of_eq' hp g e he
    · rw [ite_eq_right (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0 with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      exact heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    · rw [ite_eq_left h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      exact heckeMatrix_mul_of_eq' hp g j.val e he
    · rw [ite_eq_right h, heckeRep_coe, heckeRep_coe]
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
      exact heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)

private theorem apply_heckeRep_smul_smul (F : ℍ → ℂ) (hF : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
    F (γ • τ) = F τ)
    (g : SL(2, ℤ)) (x : OnePoint (ZMod p)) (τ : ℍ) :
    F (heckeRep p x • g • τ) = F (heckeRep p (redMatrix p g • x) • τ) := by
  obtain ⟨g', hmul⟩ := heckeRep_mul g x
  have h1 : heckeRep p x • g • τ = (heckeRep p x * mapGL ℝ g) • τ := by
    rw [mul_smul]; rfl
  have h2 : (mapGL ℝ g' * heckeRep p (redMatrix p g • x)) • τ
      = g' • heckeRep p (redMatrix p g • x) • τ := by
    rw [mul_smul]; rfl
  rw [h1, hmul, h2, hF]

end projectiveLine

section reindex

variable {p : ℕ} [NeZero p]

private theorem prod_range_eq_prod_zmod {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ j ∈ Finset.range p, G j = ∏ x : ZMod p, G x.val := by
  refine Finset.prod_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val)
      (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

private theorem prod_fin_eq_prod_zmod {M : Type} [CommMonoid M] (G : ℕ → M) :
    ∏ b : Fin p, G (b : ℕ) = ∏ x : ZMod p, G x.val := by
  rw [Fin.prod_univ_eq_prod_range, prod_range_eq_prod_zmod]

private theorem cosetPoly_eq_prod_onePoint (F : ℍ → ℂ) (τ : ℍ) :
    (X - C (F (heckeDiagMatrix p • τ))) * ∏ b : Fin p, (X - C (F (heckeUpperMatrix p (b : ℕ) • τ)))
      = ∏ x : OnePoint (ZMod p), (X - C (F (heckeRep p x • τ))) := by
  rw [prod_fin_eq_prod_zmod (fun j ↦ X - C (F (heckeUpperMatrix p j • τ)))]
  exact (Fintype.prod_option (fun x : OnePoint (ZMod p) ↦ X - C (F (heckeRep p x • τ)))).symm

end reindex

theorem _root_.ModularCurve.cosetPoly_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (F : ℍ → ℂ)
    (hF : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (X - C (F (heckeDiagMatrix ℓ • γ • τ))) * ∏ b : Fin ℓ,
        (X - C (F (heckeUpperMatrix ℓ (b : ℕ) • γ • τ)))
      = (X - C (F (heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ,
          (X - C (F (heckeUpperMatrix ℓ (b : ℕ) • τ))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [cosetPoly_eq_prod_onePoint F (γ • τ), cosetPoly_eq_prod_onePoint F τ]
  calc ∏ x : OnePoint (ZMod ℓ), (X - C (F (heckeRep ℓ x • γ • τ)))
      = ∏ x : OnePoint (ZMod ℓ), (X - C (F (heckeRep ℓ (redMatrix ℓ γ • x) • τ))) :=
        Finset.prod_congr rfl fun x _ ↦ by rw [apply_heckeRep_smul_smul F hF γ x τ]
    _ = ∏ x : OnePoint (ZMod ℓ), (X - C (F (heckeRep ℓ x • τ))) :=
        Equiv.prod_comp (MulAction.toPerm (redMatrix ℓ γ)) (fun x ↦ X - C (F (heckeRep ℓ x • τ)))

end CosetPoly

end ModularCurve

end

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

private theorem coe_heckeUpperMatrix_smul {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) :
    ((ModularForm.heckeUpperMatrix p j • τ : ℍ) : ℂ) = ((τ : ℂ) + j) / p := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (ModularForm.det_heckeUpperMatrix_pos p j)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, ModularForm.val_heckeUpperMatrix hp]

theorem _root_.ModularCurve.hasSum_qParam_heckeMatrix_smul (ℓ : ℕ) [NeZero ℓ] (b : ℕ)
    (A : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 1 (τ : ℂ) ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m /
        ℓ) * A.coeff m) * 𝕢 ℓ (τ : ℂ) ^ m)
      (F (ModularForm.heckeUpperMatrix ℓ b • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓ' : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  have e : 𝕢 1 ((ModularForm.heckeUpperMatrix ℓ b • τ : ℍ) : ℂ)
      = Complex.exp (2 * Real.pi * Complex.I * b / ℓ) * 𝕢 ℓ (τ : ℂ) := by
    rw [coe_heckeUpperMatrix_smul hℓ, Periodic.qParam, Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have e2 : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * b / ℓ) ^ m
      = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
    intro m
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  have hfg : (fun m : ℤ => (Complex.exp (2 * Real.pi * Complex.I * b * m /
      ℓ) * A.coeff m) * 𝕢 ℓ (τ : ℂ) ^ m)
      = fun m : ℤ => A.coeff m * 𝕢 1 ((ModularForm.heckeUpperMatrix ℓ b • τ : ℍ) : ℂ) ^ m := by
    funext m
    rw [e, mul_zpow, e2]
    ring
  rw [hfg]
  exact hA _

end Realized

end ModularCurve

end

noncomputable section

open UpperHalfPlane Complex Filter Topology Function
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

namespace Realized

theorem _root_.ModularCurve.hasSum_qParam_heckeDiagMatrix_smul (ℓ : ℕ) [NeZero ℓ]
    (A : LaurentSeries ℂ) (F : ℍ → ℂ)
    (hA : ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 1 (τ : ℂ) ^ m) (F τ)) (τ : ℍ) :
    HasSum (fun m : ℤ => (ModularCurve.qExpand ℂ (ℓ * ℓ) A).coeff m * 𝕢 ℓ (τ : ℂ) ^ m)
      (F (ModularForm.heckeDiagMatrix ℓ • τ)) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  have hℓ' : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  have hN : ((ℓ * ℓ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne (ℓ * ℓ))
  have e : 𝕢 1 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = 𝕢 ℓ (τ : ℂ) ^ ((ℓ * ℓ : ℕ) : ℤ) := by
    rw [ModularForm.coe_heckeDiagMatrix_smul hℓ, Periodic.qParam, Periodic.qParam, zpow_natCast,
      ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hinj : Function.Injective (fun m : ℤ => ((ℓ * ℓ : ℕ) : ℤ) * m) := mul_right_injective₀ hN
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ => (ModularCurve.qExpand ℂ (ℓ * ℓ) A).coeff m * 𝕢 ℓ (τ : ℂ) ^ m) ∘
        (fun m : ℤ => ((ℓ * ℓ : ℕ) : ℤ) * m)
        = fun m : ℤ => A.coeff m * 𝕢 1 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) ^ m := by
      funext m
      simp only [Function.comp_apply]
      rw [ModularCurve.qExpand_coeff_mul, e, ← zpow_mul]
    rw [hfg]
    exact hA _
  · intro m hm
    rw [ModularCurve.qExpand_coeff_of_not_dvd (ℓ * ℓ) A (fun ⟨c, hc⟩ => hm ⟨c, hc.symm⟩), zero_mul]

end Realized

end ModularCurve

end
