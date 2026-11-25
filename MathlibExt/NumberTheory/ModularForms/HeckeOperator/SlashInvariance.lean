/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean`,
`P2M/Sol/S_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean`,
`Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`
and
`P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`
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
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Invariance of Hecke operators under `Γ₀(N)`

If `f` is invariant under the weight-`k` slash action of `Γ₀(N)`, then so are
`heckeT k p f` for a prime `p ∤ N` and `heckeU k p f` for `p ∣ N`. Right
multiplication by an element `γ` of `Γ₀(N)` permutes the double-coset
representatives `!![1, j; 0, p]` (and `!![p, 0; 0, 1]` for `T`) up to left
factors in `Γ₀(N)`: for `U` the permutation is affine on `ZMod p`, for `T` it
is the action of the reduction of `γ` on the projective line over `ZMod p`.

## Main results

* `ModularForm.heckeT_slash_eq_self_of_mem_Gamma0`
* `ModularForm.heckeU_slash_eq_self_of_mem_Gamma0`
-/

@[expose] public section

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm OnePoint

namespace ModularForm

private theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

attribute [local simp] mapGL_apply

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

private theorem heckeUpperMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeUpperMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeUpperMatrix p j' := by
  have hdet := det_eq g
  refine ⟨Matrix.SpecialLinearGroup.mk
    !![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.sum_univ_two, Fin.zero_eta, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.coe_castRingHom,
        Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.map_apply, Matrix.mul_apply,
        Matrix.of_apply, Units.val_mul, add_zero, algebraMap_int_eq, hp, mapGL_coe_matrix,
        map_apply_coe, mul_one, mul_zero, ne_eq, not_false_eq_true, one_mul, val_heckeUpperMatrix,
        zero_add, zero_mul]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

private theorem heckeUpperMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeUpperMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨Matrix.SpecialLinearGroup.mk !![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.sum_univ_two, Fin.zero_eta, Int.cast_add,
        Int.cast_mul, Int.cast_natCast, Int.coe_castRingHom, Matrix.SpecialLinearGroup.coe_mk,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Units.val_mul, add_zero,
        algebraMap_int_eq, hp, mapGL_coe_matrix, map_apply_coe, mul_one, mul_zero, ne_eq,
        not_false_eq_true, one_mul, val_heckeDiagMatrix, val_heckeUpperMatrix, zero_add, zero_mul]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

private theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeUpperMatrix p j' := by
  have hdet := det_eq g
  refine ⟨Matrix.SpecialLinearGroup.mk !![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.sum_univ_two, Fin.zero_eta, Int.cast_mul,
        Int.cast_natCast, Int.cast_sub, Int.coe_castRingHom, Matrix.SpecialLinearGroup.coe_mk,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, Units.val_mul, add_zero,
        algebraMap_int_eq, hp, mapGL_coe_matrix, map_apply_coe, mul_one, mul_zero, ne_eq,
        not_false_eq_true, one_mul, val_heckeDiagMatrix, val_heckeUpperMatrix, zero_add, zero_mul]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

private theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨Matrix.SpecialLinearGroup.mk !![g 0 0, p * g 0 1; e, g 1 1] ?_, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.mk_one, Fin.sum_univ_two, Fin.zero_eta, Int.cast_mul,
        Int.cast_natCast, Int.coe_castRingHom, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.map_apply,
        Matrix.mul_apply, Matrix.of_apply, Units.val_mul, add_zero, algebraMap_int_eq, hp,
        mapGL_coe_matrix, map_apply_coe, mul_one, mul_zero, ne_eq, not_false_eq_true, one_mul,
        val_heckeDiagMatrix, zero_add, zero_mul]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section reindex

variable {p : ℕ} [NeZero p]

private theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.range p, F j = ∑ x : ZMod p, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val)
    (fun _ _ ↦ Finset.mem_univ _) (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_)
    (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

private theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeUpperMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex

section heckeU

variable {p : ℕ}

private theorem unit_of_apply_one_zero_eq_zero (g : SL(2, ℤ))
    (hc : ((g 1 0 : ℤ) : ZMod p) = 0) :
    ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
  push_cast at this
  linear_combination this + ((g 0 1 : ℤ) : ZMod p) * hc

/-- The affine permutation `j ↦ d (b + d j)` of `ZMod p` induced by an element
`!![a, b; c, d]` of `SL(2, ℤ)` with `p ∣ c`. -/
private def affinePerm (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) :
    Equiv.Perm (ZMod p) where
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

private theorem affinePerm_apply (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0)
    (j : ZMod p) :
    affinePerm g hc j =
      ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j) :=
  rfl

variable [NeZero p]

private theorem heckeUpperMatrix_mul_of_dvd (g : SL(2, ℤ)) (hc : (p : ℤ) ∣ g 1 0)
    (x : ZMod p) :
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
      - (((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * x) * x) *
        hc0
  exact heckeUpperMatrix_mul_of_eq (NeZero.ne p) g x.val x'.val e (by linear_combination he)

private theorem heckeU_slash_mapGL {N : ℕ} (k : ℤ) (hpN : p ∣ N) (f : ℍ → ℂ)
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

/-- The representatives of the `T`-type double coset, indexed by the
projective line over `ZMod p`. -/
private def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeUpperMatrix p j.val)

private theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

private theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeUpperMatrix p j.val := rfl

private theorem heckeT_eq_sum_onePoint [NeZero p] (k : ℤ) (f : ℍ → ℂ) :
    heckeT k p f = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x := by
  rw [heckeT_eq_heckeU_add, heckeU_eq_sum_zmod, add_comm]
  exact (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] heckeRep p x)).symm

variable [Fact p.Prime]

variable (p) in
/-- The reduction modulo `p` of `!![a, b; c, d]`, written as `!![d, b; c, a]`,
acting on the projective line over `ZMod p`. -/
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

private theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

private theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

private theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

private theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

private theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero p := ⟨hp⟩
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    · rw [ite_eq_left (by simpa [redMatrix_apply_one_zero] using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, hmul⟩
      rw [hg']
      have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
      exact hcop.dvd_of_dvd_mul_left (he ▸ hg)
    · rw [ite_eq_right (by simpa [redMatrix_apply_one_zero] using hc), heckeRep_infty,
        heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0 with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hmul⟩ :=
        heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ hg, hmul⟩
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
      obtain ⟨g', hg', hmul⟩ := heckeUpperMatrix_mul_of_eq' hp g j.val e he
      exact ⟨g', hg' ▸ hg, hmul⟩
    · rw [ite_eq_right h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ :
          (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
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

private theorem heckeT_slash_mapGL {N : ℕ} (k : ℤ) (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeT k p f ∣[k] (mapGL ℝ g) = heckeT k p f := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
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

/-- For a prime `p ∤ N`, the Hecke operator `T p` preserves invariance under
the weight-`k` slash action of `Γ₀(N)`. -/
public theorem heckeT_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    heckeT k p f ∣[k] γ = heckeT k p f := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeT_slash_mapGL k hpN f hf g hg

/-- For `p ∣ N`, the Hecke operator `U p` preserves invariance under the
weight-`k` slash action of `Γ₀(N)`. -/
public theorem heckeU_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    heckeU k p f ∣[k] γ = heckeU k p f := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeU_slash_mapGL k hpN f hf g hg

end ModularForm
