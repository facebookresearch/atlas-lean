/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd.lean`
and
`P2M/Sol/S_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd.lean`
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
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Reduction of congruence subgroups modulo a prime

If `p` does not divide `N`, then reduction modulo `p` maps `Γ(N)` onto
`SL(2, ZMod p)`: the elementary transvections of `SL(2, ZMod p)` lift to
`Γ(N)` by the Chinese remainder theorem, and `SL(2, ZMod p)` is generated
by transvections and diagonal matrices. Also, `-1` lies in `Γ₁(N)` if
and only if `N ≤ 2`.

The source statement also contains a third claim, that the kernel of
reduction modulo `p` is `Γ(p)`; that is Mathlib's `CongruenceSubgroup.Gamma_mem'`,
so it is not repeated here.
-/

@[expose] public section

open scoped MatrixGroups

namespace GammaReductionAux

private def U01 (k : ℤ) : SL(2, ℤ) := ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def U10 (k : ℤ) : SL(2, ℤ) := ⟨!![1, 0; k, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem U01_mem_Gamma {N : ℕ} {k : ℤ} (hk : (N : ℤ) ∣ k) :
    U01 k ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem]
  obtain ⟨t, rfl⟩ := hk
  simp [U01]

private theorem U10_mem_Gamma {N : ℕ} {k : ℤ} (hk : (N : ℤ) ∣ k) :
    U10 k ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem]
  obtain ⟨t, rfl⟩ := hk
  simp [U10]

variable (p : ℕ) [Fact p.Prime]

private abbrev red : SL(2, ℤ) →* SL(2, ZMod p) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p))

private def u01 (c : ZMod p) : SL(2, ZMod p) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def u10 (c : ZMod p) : SL(2, ZMod p) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem red_U01 (k : ℤ) : red p (U01 k) = u01 p (k : ZMod p) := by
  apply Subtype.ext
  change (Int.castRingHom (ZMod p)).mapMatrix !![1, k; 0, 1] =
    ((u01 p (k : ZMod p) : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
  ext i j; fin_cases i <;> fin_cases j <;> simp [u01, RingHom.mapMatrix_apply]

private theorem red_U10 (k : ℤ) : red p (U10 k) = u10 p (k : ZMod p) := by
  apply Subtype.ext
  change (Int.castRingHom (ZMod p)).mapMatrix !![1, 0; k, 1] =
    ((u10 p (k : ZMod p) : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
  ext i j; fin_cases i <;> fin_cases j <;> simp [u10, RingHom.mapMatrix_apply]

private theorem exists_lift {N : ℕ} (hpN : ¬ p ∣ N) (c : ZMod p) :
    ∃ k : ℤ, (N : ℤ) ∣ k ∧ (k : ZMod p) = c := by
  have hcop : N.Coprime p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN))
  obtain ⟨k, hkN, hkp⟩ := Nat.chineseRemainder hcop 0 c.val
  refine ⟨(k : ℤ), ?_, ?_⟩
  · have : N ∣ k := (Nat.modEq_zero_iff_dvd.mp hkN)
    exact_mod_cast this
  · have h1 : ((k : ℕ) : ZMod p) = ((c.val : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hkp
    rw [ZMod.natCast_val, ZMod.cast_id', id] at h1
    exact_mod_cast h1

private abbrev S (N : ℕ) : Subgroup SL(2, ZMod p) := (CongruenceSubgroup.Gamma N).map (red p)

private theorem u01_mem {N : ℕ} (hpN : ¬ p ∣ N) (c : ZMod p) : u01 p c ∈ S p N := by
  obtain ⟨k, hk, hkc⟩ := exists_lift p hpN c
  exact ⟨U01 k, U01_mem_Gamma hk, by rw [red_U01, hkc]⟩

private theorem u10_mem {N : ℕ} (hpN : ¬ p ∣ N) (c : ZMod p) : u10 p c ∈ S p N := by
  obtain ⟨k, hk, hkc⟩ := exists_lift p hpN c
  exact ⟨U10 k, U10_mem_Gamma hk, by rw [red_U10, hkc]⟩

private def Real' (N : ℕ) (A : Matrix (Fin 2) (Fin 2) (ZMod p)) : Prop :=
  ∃ s ∈ S p N, ((s : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = A

private theorem real_one (N : ℕ) : Real' p N 1 := ⟨1, Subgroup.one_mem _, rfl⟩

private theorem real_mul {N : ℕ} {A B : Matrix (Fin 2) (Fin 2) (ZMod p)}
    (hA : Real' p N A) (hB : Real' p N B) : Real' p N (A * B) := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  exact ⟨s * t, Subgroup.mul_mem _ hs ht, rfl⟩

private theorem real_list_prod {N : ℕ} (L : List (Matrix (Fin 2) (Fin 2) (ZMod p)))
    (hL : ∀ A ∈ L, Real' p N A) : Real' p N L.prod := by
  induction L with
  | nil => exact real_one p N
  | cons A L ih =>
    rw [List.prod_cons]
    exact real_mul p (hL A (List.mem_cons_self ..))
      (ih fun B hB => hL B (List.mem_cons_of_mem _ hB))

private theorem real_transvection {N : ℕ} (hpN : ¬ p ∣ N)
    (t : Matrix.TransvectionStruct (Fin 2) (ZMod p)) : Real' p N t.toMatrix := by
  obtain ⟨i, j, hij, c⟩ := t
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine ⟨u01 p c, u01_mem p hpN c, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [u01, Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single]
  · refine ⟨u10 p c, u10_mem p hpN c, ?_⟩
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [u10, Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single]
  · exact absurd rfl hij

private theorem real_diag {N : ℕ} (hpN : ¬ p ∣ N) (a : ZMod p) (ha : a ≠ 0) :
    Real' p N (Matrix.diagonal ![a, a⁻¹]) := by
  have h : Matrix.diagonal ![a, a⁻¹] =
      ((u01 p a : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (u10 p (-a⁻¹) : SL(2, ZMod p)) * (u01 p a : SL(2, ZMod p)) *
        ((u01 p (-1) : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (u10 p 1 : SL(2, ZMod p)) * (u01 p (-1) : SL(2, ZMod p)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [u01, u10, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] <;>
        field_simp <;> ring
  rw [h]
  refine real_mul p (real_mul p (real_mul p (real_mul p (real_mul p ?_ ?_) ?_) ?_) ?_) ?_
  · exact ⟨u01 p a, u01_mem p hpN a, rfl⟩
  · exact ⟨u10 p (-a⁻¹), u10_mem p hpN _, rfl⟩
  · exact ⟨u01 p a, u01_mem p hpN a, rfl⟩
  · exact ⟨u01 p (-1), u01_mem p hpN _, rfl⟩
  · exact ⟨u10 p 1, u10_mem p hpN _, rfl⟩
  · exact ⟨u01 p (-1), u01_mem p hpN _, rfl⟩

private theorem S_eq_top {N : ℕ} (hpN : ¬ p ∣ N) : S p N = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨L, L', D, hg⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
    ((g : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p))
  have hdet : (Matrix.diagonal D).det = 1 := by
    have h := g.prop
    rw [hg, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.TransvectionStruct.det_toMatrix_prod, one_mul, mul_one] at h
    exact h
  rw [Matrix.det_diagonal, Fin.prod_univ_two] at hdet
  have ha : D 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hD : D = ![D 0, (D 0)⁻¹] := by
    funext i; fin_cases i
    · rfl
    · change D 1 = (D 0)⁻¹
      exact eq_inv_of_mul_eq_one_right hdet
  have hreal : Real' p N ((g : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [hg]
    refine real_mul p ?_ ?_
    · refine real_mul p ?_ ?_
      · exact real_list_prod p _ fun A hA => by
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hA
          exact real_transvection p hpN t
      · rw [hD]; exact real_diag p hpN (D 0) ha
    · exact real_list_prod p _ fun A hA => by
        obtain ⟨t, _, rfl⟩ := List.mem_map.mp hA
        exact real_transvection p hpN t
  obtain ⟨s, hs, hsg⟩ := hreal
  have : s = g := Subtype.ext hsg
  rw [← this]; exact hs

end GammaReductionAux

namespace CongruenceSubgroup

/-- If `p` does not divide `N`, then reduction modulo `p` maps `Γ(N)` onto
`SL(2, ZMod p)`. -/
theorem exists_mem_Gamma_map_eq_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ∀ g : SL(2, ZMod p), ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma N ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) γ = g := by
  intro g
  have h : g ∈ GammaReductionAux.S p N := by
    rw [GammaReductionAux.S_eq_top p hpN]; trivial
  obtain ⟨γ, hγ, hγg⟩ := h
  exact ⟨γ, hγ, hγg⟩

/-- `-1` lies in `Γ₁(N)` if and only if `N ≤ 2`. -/
theorem neg_one_mem_Gamma1_iff (N : ℕ) [NeZero N] :
    (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma1 N ↔ N ≤ 2 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  have hN : (N : ℕ) ≠ 0 := NeZero.ne N
  constructor
  · rintro ⟨h, -, -⟩
    have h1 : ((-1 : ℤ) : ZMod N) = 1 := by simpa using h
    have h2 : ((2 : ℤ) : ZMod N) = 0 := by
      have : ((2 : ℤ) : ZMod N) = 1 - ((-1 : ℤ) : ZMod N) := by push_cast; ring
      rw [this, h1, sub_self]
    have h3 : (N : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 N).mp h2
    have h4 : N ∣ 2 := by exact_mod_cast h3
    exact Nat.le_of_dvd two_pos h4
  · intro hN2
    have hcases : N = 1 ∨ N = 2 := by have := Nat.pos_of_ne_zero hN; omega
    rcases hcases with rfl | rfl
    · simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq,
        Int.reduceNeg, Int.cast_neg, Int.cast_one, ne_eq, one_ne_zero, not_false_eq_true,
        Matrix.one_apply_ne, neg_zero, Int.cast_zero, and_true, and_self]
      decide
    · simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq,
        Int.reduceNeg, Int.cast_neg, Int.cast_one, ne_eq, one_ne_zero, not_false_eq_true,
        Matrix.one_apply_ne, neg_zero, Int.cast_zero, and_true, and_self]
      decide

end CongruenceSubgroup
