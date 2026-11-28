/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_
traceZero_of_charP_three.lean`
and
`P2M/Sol/S_groupCohomology_subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three.lean`
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

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants

@[expose] public section

set_option autoImplicit false

/-!
# Vanishing of `H^1` for `SL(2, F)` on trace-zero matrices in characteristic 3

For a finite field `F` of characteristic `3`, any representation of
`SL(2, F)` identified, by an injective equivariant map, with the trace-zero
`2 x 2` matrices under conjugation has vanishing first group cohomology.
-/

set_option autoImplicit false

open Matrix MatrixGroups groupCohomology

namespace SL2TraceZeroH1Aux

variable {F : Type*} [Field F]

private def uni (a : F) : SL(2, F) :=
  ⟨!![1, a; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

private def tor (s : Fˣ) : SL(2, F) :=
  ⟨!![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_fin_two_of, Units.mul_inv]; ring⟩

@[scoped simp] private lemma coe_uni (a : F) :
    ((uni a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

@[scoped simp] private lemma coe_tor (s : Fˣ) :
    ((tor s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] :=
  rfl

private lemma uni_add (a b : F) : uni (a + b) = uni a * uni b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

private lemma uni_zero : uni (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma uni_inv (a : F) : (uni a)⁻¹ = uni (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [← uni_add, add_neg_cancel, uni_zero])

private lemma tor_mul (s s' : Fˣ) : tor (s * s') = tor s * tor s' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

private lemma tor_one : tor (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma tor_inv (s : Fˣ) : (tor s)⁻¹ = tor s⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← tor_mul, mul_inv_cancel, tor_one])

private lemma tor_mul_uni (s : Fˣ) (a : F) : tor s * uni a = uni ((s : F) ^ 2 * a) * tor s := by
  have hs : (s : F) * (s : F)⁻¹ = 1 := mul_inv_cancel₀ s.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val]
  linear_combination (-(a * (s : F))) * hs

private lemma conj_uni (a : F) (X : Matrix (Fin 2) (Fin 2) F) :
    (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) * X * !![1, -a; 0, 1] =
      !![X 0 0 + a * X 1 0, X 0 1 + a * X 1 1 - a * X 0 0 - a ^ 2 * X 1 0;
         X 1 0, X 1 1 - a * X 1 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

private lemma conj_tor (s t : F) (X : Matrix (Fin 2) (Fin 2) F) :
    (!![s, 0; 0, t] : Matrix (Fin 2) (Fin 2) F) * X * !![t, 0; 0, s] =
      !![s * t * X 0 0, s ^ 2 * X 0 1; t ^ 2 * X 1 0, s * t * X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

omit [Field F] in
private lemma entries_eq {X Y : Matrix (Fin 2) (Fin 2) F} (h : X = Y) :
    X 0 0 = Y 0 0 ∧ X 0 1 = Y 0 1 ∧ X 1 0 = Y 1 0 ∧ X 1 1 = Y 1 1 := by
  subst h; exact ⟨rfl, rfl, rfl, rfl⟩

private lemma three_eq_zero [CharP F 3] : (3 : F) = 0 := by
  have := CharP.cast_eq_zero F 3
  exact_mod_cast this

private lemma two_ne_zero' [CharP F 3] : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F 3] at h'
  omega

private lemma dichotomy [CharP F 3] :
    (∃ s : F, s ≠ 0 ∧ s ^ 4 ≠ 1) ∨ ∀ a : F, a = 0 ∨ a = 1 ∨ a = -1 := by
  by_cases h : ∃ s : F, s ≠ 0 ∧ s ^ 4 ≠ 1
  · exact Or.inl h
  right
  push Not at h
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  have h3 : (3 : F) = 0 := three_eq_zero
  intro a
  by_cases ha : a = 0
  · exact Or.inl ha
  have h4 : a ^ 4 = 1 := h a ha
  have hfac : (a ^ 2 - 1) * (a ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 hfac with h1 | h1
  · have hfac' : (a - 1) * (a + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 hfac' with h' | h'
    · exact Or.inr (Or.inl (by linear_combination h'))
    · exact Or.inr (Or.inr (by linear_combination h'))
  · by_cases hb : a + 1 = 0
    · exact Or.inr (Or.inr (by linear_combination hb))
    · have hb4 : (a + 1) ^ 4 = 1 := h (a + 1) hb
      exfalso
      apply h2
      linear_combination (-1 : F) * hb4 + (a ^ 2 + 4 * a + 5) * h1 - h3

private theorem key [CharP F 3] (f : F → Matrix (Fin 2) (Fin 2) F)
    (hadd : ∀ a b, f (a + b) = !![1, a; 0, 1] * f b * !![1, -a; 0, 1] + f a)
    (htor : ∀ s a : F, s ≠ 0 → f (s ^ 2 * a) = !![s, 0; 0, s⁻¹] * f a * !![s⁻¹, 0; 0, s])
    (htr : ∀ a, f a 1 1 = - f a 0 0) :
    ∃ m : Matrix (Fin 2) (Fin 2) F, m 1 1 = - m 0 0 ∧
      ∀ a, f a = !![1, a; 0, 1] * m * !![1, -a; 0, 1] - m := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero'
  have h3 : (3 : F) = 0 := three_eq_zero
  obtain ⟨α, hα⟩ : ∃ α : F → F, ∀ a, f a 0 1 = α a := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : F → F, ∀ a, f a 0 0 = β a := ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : F → F, ∀ a, f a 1 0 = γ a := ⟨_, fun _ => rfl⟩
  have hδ : ∀ a, f a 1 1 = - β a := fun a => by rw [htr a, hβ]
  have hfa : ∀ a, f a = !![β a, α a; γ a, -β a] := fun a => by
    rw [Matrix.eta_fin_two (f a), hα, hβ, hγ, hδ]
  have E00 : ∀ a b, β (a + b) = β b + a * γ b + β a := fun a b => by
    have h := hadd a b
    rw [hfa (a + b), hfa b, hfa a, conj_uni] at h
    obtain ⟨h00, -, -, -⟩ := entries_eq h
    simp at h00
    linear_combination h00
  have E01 : ∀ a b, α (a + b) = α b - 2 * a * β b - a ^ 2 * γ b + α a := fun a b => by
    have h := hadd a b
    rw [hfa (a + b), hfa b, hfa a, conj_uni] at h
    obtain ⟨-, h01, -, -⟩ := entries_eq h
    simp at h01
    linear_combination h01
  have E10 : ∀ a b, γ (a + b) = γ b + γ a := fun a b => by
    have h := hadd a b
    rw [hfa (a + b), hfa b, hfa a, conj_uni] at h
    obtain ⟨-, -, h10, -⟩ := entries_eq h
    simpa using h10
  have T00 : ∀ s a : F, s ≠ 0 → β (s ^ 2 * a) = β a := fun s a hs => by
    have h := htor s a hs
    rw [hfa (s ^ 2 * a), hfa a, conj_tor] at h
    obtain ⟨h00, -, -, -⟩ := entries_eq h
    simp [mul_inv_cancel₀ hs] at h00
    exact h00
  have T01 : ∀ s a : F, s ≠ 0 → α (s ^ 2 * a) = s ^ 2 * α a := fun s a hs => by
    have h := htor s a hs
    rw [hfa (s ^ 2 * a), hfa a, conj_tor] at h
    obtain ⟨-, h01, -, -⟩ := entries_eq h
    simpa using h01
  have T10 : ∀ s a : F, s ≠ 0 → s ^ 2 * γ (s ^ 2 * a) = γ a := fun s a hs => by
    have h := htor s a hs
    rw [hfa (s ^ 2 * a), hfa a, conj_tor] at h
    obtain ⟨-, -, h10, -⟩ := entries_eq h
    simp at h10
    rw [h10]
    field_simp
  have hβ00 : β 0 = 0 := by
    have h := E00 0 0
    rw [add_zero] at h
    linear_combination -h
  have hγ00 : γ 0 = 0 := by
    have h := E10 0 0
    rw [add_zero] at h
    linear_combination -h
  have hα00 : α 0 = 0 := by
    have h := E01 0 0
    rw [add_zero] at h
    linear_combination -h
  rcases dichotomy (F := F) with ⟨s, hs, hs4⟩ | hB
  ·
    have hs2 : s ^ 2 ≠ 1 := fun h => hs4 (by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow])
    have hγlin : ∀ a, γ a = a * γ 1 := fun a => by
      have h1 := E00 a 1
      have h1' : β (a + 1) = β a + 1 * γ a + β 1 := by rw [add_comm a 1]; exact E00 1 a
      linear_combination h1 - h1'
    have hγ1 : γ 1 = 0 := by
      have hA := T10 s 1 hs
      rw [hγlin (s ^ 2 * 1)] at hA
      have h0 : (s ^ 4 - 1) * γ 1 = 0 := by linear_combination hA
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hs4
      · exact h
    have hγ0 : ∀ a, γ a = 0 := fun a => by rw [hγlin, hγ1, mul_zero]
    have hβlin : ∀ a, β a = a * β 1 := fun a => by
      have h1 := E01 a 1
      have h1' : α (a + 1) = α a - 2 * 1 * β a - 1 ^ 2 * γ a + α 1 := by
        rw [add_comm a 1]; exact E01 1 a
      have h22 : (2 : F) * (β a - a * β 1) = 0 := by
        linear_combination h1' - h1 + a ^ 2 * hγ0 1 - hγ0 a
      rcases mul_eq_zero.1 h22 with h | h
      · exact absurd h h2
      · linear_combination h
    have hβ1 : β 1 = 0 := by
      have hA := T00 s 1 hs
      rw [hβlin (s ^ 2 * 1)] at hA
      have h0 : (s ^ 2 - 1) * β 1 = 0 := by linear_combination hA
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hs2
      · exact h
    have hβ0 : ∀ a, β a = 0 := fun a => by rw [hβlin, hβ1, mul_zero]
    have hαadd : ∀ a b, α (a + b) = α a + α b := fun a b => by
      linear_combination E01 a b - 2 * a * hβ0 b - a ^ 2 * hγ0 b
    have hαneg : ∀ a, α (-a) = - α a := fun a => by
      have h := hαadd a (-a)
      rw [add_neg_cancel, hα00] at h
      linear_combination -h
    have hαsq : ∀ s a : F, α (s ^ 2 * a) = s ^ 2 * α a := fun s a => by
      by_cases hs0 : s = 0
      · rw [hs0, zero_pow two_ne_zero, zero_mul, zero_mul, hα00]
      · exact T01 s a hs0
    have hαlin : ∀ c a : F, α (c * a) = c * α a := fun c a => by
      have hh : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have hpm : ((c + 1) * 2⁻¹) ^ 2 - ((c - 1) * 2⁻¹) ^ 2 = c := by
        linear_combination (c * (2 * 2⁻¹ + 1)) * hh
      calc α (c * a) = α (((c + 1) * 2⁻¹) ^ 2 * a + -(((c - 1) * 2⁻¹) ^ 2 * a)) := by
            rw [← sub_eq_add_neg, ← sub_mul, hpm]
        _ = ((c + 1) * 2⁻¹) ^ 2 * α a + -(((c - 1) * 2⁻¹) ^ 2 * α a) := by
            rw [hαadd, hαneg, hαsq, hαsq]
        _ = c * α a := by rw [← sub_eq_add_neg, ← sub_mul, hpm]
    have hα1 : ∀ a, α a = a * α 1 := fun a => by rw [← hαlin, mul_one]
    refine ⟨!![α 1, 0; 0, -α 1], by simp, fun a => ?_⟩
    rw [hfa a, conj_uni]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hβ0]
    · simp
      linear_combination hα1 a + (a * α 1) * h3
    · simp [hγ0]
    · simp [hβ0]
  ·
    have hneg : (-1 : F) = 1 + 1 := by linear_combination -h3
    have hγ2 : γ (1 + 1) = γ 1 + γ 1 := E10 1 1
    have hβ2 : β (1 + 1) = β 1 + 1 * γ 1 + β 1 := E00 1 1
    have hα2 : α (1 + 1) = α 1 - 2 * 1 * β 1 - 1 ^ 2 * γ 1 + α 1 := E01 1 1
    have h1110 : (1 : F) + (1 + 1) = 0 := by linear_combination h3
    have hα3 : α (1 + (1 + 1)) = α (1 + 1) - 2 * 1 * β (1 + 1) - 1 ^ 2 * γ (1 + 1) + α 1 :=
      E01 1 (1 + 1)
    rw [h1110, hα00] at hα3
    have hg : γ 1 = 0 := by
      linear_combination -hα3 - hα2 + 2 * hβ2 + hγ2 + (2 * γ 1 - α 1 + 2 * β 1) * h3
    have hg2 : γ (1 + 1) = 0 := by rw [hγ2, hg, add_zero]
    have e1 : β (-1) = -β 1 := by
      rw [hneg, hβ2, hg]
      linear_combination (β 1) * h3
    have e2 : α (-1) = -α 1 + β 1 := by
      rw [hneg, hα2, hg]
      linear_combination (α 1 - β 1) * h3
    have e3 : γ (-1) = 0 := by rw [hneg, hg2]
    refine ⟨!![α 1 + β 1, 0; β 1, -(α 1 + β 1)], by simp, fun a => ?_⟩
    rw [hfa a, conj_uni]
    rcases hB a with rfl | rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hα00, hβ00, hγ00]
    · ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp
        linear_combination (α 1 + β 1) * h3
      · simp [hg]
      · simp
    · ext i j
      fin_cases i <;> fin_cases j
      · simp [e1]
      · simp [e2]
        linear_combination (-α 1) * h3
      · simp [e3]
      · simp [e1]

open Classical in
private noncomputable def sec (v : Fin 2 → F) : SL(2, F) :=
  if h0 : v 0 ≠ 0 then
    ⟨!![v 0, 0; v 1, (v 0)⁻¹], by rw [Matrix.det_fin_two_of, mul_inv_cancel₀ h0]; ring⟩
  else if h1 : v 1 ≠ 0 then
    ⟨!![v 0, -(v 1)⁻¹; v 1, 0], by
      rw [Matrix.det_fin_two_of, mul_zero, neg_mul, sub_neg_eq_add, zero_add,
        inv_mul_cancel₀ h1]⟩
  else 1

private lemma sec_zero : sec (0 : Fin 2 → F) = 1 := by
  simp [sec]

private lemma sec_col {v : Fin 2 → F} (hv : v ≠ 0) :
    (sec v : Matrix (Fin 2) (Fin 2) F) 0 0 = v 0 ∧
      (sec v : Matrix (Fin 2) (Fin 2) F) 1 0 = v 1 := by
  by_cases h0 : v 0 ≠ 0
  · simp [sec, h0]
  · by_cases h1 : v 1 ≠ 0
    · simp [sec, h0, h1]
    · exfalso
      apply hv
      funext i
      fin_cases i
      · exact not_not.mp h0
      · exact not_not.mp h1

private lemma exists_eq_mul_uni (p r : SL(2, F))
    (h0 : (p : Matrix (Fin 2) (Fin 2) F) 0 0 = (r : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h1 : (p : Matrix (Fin 2) (Fin 2) F) 1 0 = (r : Matrix (Fin 2) (Fin 2) F) 1 0) :
    ∃ a : F, r = p * uni a := by
  have hp := p.det_coe
  have hr := r.det_coe
  rw [Matrix.det_fin_two] at hp hr
  refine ⟨(p : Matrix (Fin 2) (Fin 2) F) 1 1 * (r : Matrix (Fin 2) (Fin 2) F) 0 1 -
    (p : Matrix (Fin 2) (Fin 2) F) 0 1 * (r : Matrix (Fin 2) (Fin 2) F) 1 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -h0
  · linear_combination (-(r : Matrix (Fin 2) (Fin 2) F) 0 1) * hp +
      (p : Matrix (Fin 2) (Fin 2) F) 0 1 * hr +
      ((p : Matrix (Fin 2) (Fin 2) F) 0 1 * (r : Matrix (Fin 2) (Fin 2) F) 1 1) * h0 +
      (-((p : Matrix (Fin 2) (Fin 2) F) 0 1 * (r : Matrix (Fin 2) (Fin 2) F) 0 1)) * h1
  · linear_combination -h1
  · linear_combination (-(r : Matrix (Fin 2) (Fin 2) F) 1 1) * hp +
      (p : Matrix (Fin 2) (Fin 2) F) 1 1 * hr +
      ((p : Matrix (Fin 2) (Fin 2) F) 1 1 * (r : Matrix (Fin 2) (Fin 2) F) 1 1) * h0 +
      (-((p : Matrix (Fin 2) (Fin 2) F) 1 1 * (r : Matrix (Fin 2) (Fin 2) F) 0 1)) * h1

private lemma exists_mul_sec (h : SL(2, F)) {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ a : F, h * sec v = sec ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ v) * uni a := by
  have hhv : (h : Matrix (Fin 2) (Fin 2) F) *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    have : ((h⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [← this, h0, Matrix.mulVec_zero]
  obtain ⟨hc0, hc1⟩ := sec_col hv
  obtain ⟨hd0, hd1⟩ := sec_col hhv
  apply exists_eq_mul_uni
  · rw [hd0, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc0, hc1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · rw [hd1, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc0, hc1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section Rep

variable (A : Rep F SL(2, F))

private def IsCoc (c : SL(2, F) → A) : Prop := ∀ g h, c (g * h) = A.ρ g (c h) + c g

variable {A}

private lemma IsCoc.apply_one {c : SL(2, F) → A} (hc : IsCoc A c) : c 1 = 0 := by
  have h := hc 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  linear_combination (norm := abel) -h

private lemma isCoc_sub {c c' : SL(2, F) → A} (hc : IsCoc A c) (m : A)
    (h : ∀ g, c' g = c g - (A.ρ g m - m)) : IsCoc A c' := by
  intro g k
  rw [h, h, h, hc]
  simp only [map_mul, map_sub, Module.End.mul_apply]
  abel

private lemma torus_coboundary [Finite F] {c : SL(2, F) → A} (hc : IsCoc A c) :
    ∃ m : A, ∀ s : Fˣ, c (tor s) = A.ρ (tor s) m - m := by
  classical
  haveI := Fintype.ofFinite F
  refine ⟨∑ s : Fˣ, c (tor s), fun s₀ => ?_⟩
  have hsum : ∑ s : Fˣ, c (tor (s₀ * s)) = ∑ s : Fˣ, c (tor s) :=
    Fintype.sum_equiv (Equiv.mulLeft s₀) _ _ (fun s => rfl)
  have hterm : ∀ s : Fˣ, c (tor (s₀ * s)) = A.ρ (tor s₀) (c (tor s)) + c (tor s₀) := fun s => by
    rw [tor_mul, hc]
  have hcard : ((Fintype.card Fˣ : ℕ) : F) = -1 := by
    have h := congrArg (Nat.cast : ℕ → F) (Fintype.card_eq_card_units_add_one (α := F))
    rw [FiniteField.cast_card_eq_zero, Nat.cast_add, Nat.cast_one] at h
    linear_combination -h
  simp_rw [hterm] at hsum
  rw [Finset.sum_add_distrib, ← map_sum, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, hcard, neg_one_smul, add_neg_eq_iff_eq_add] at hsum
  rw [hsum]
  abel

private lemma coboundary_of_vanish_uni [Finite F] {c : SL(2, F) → A} (hc : IsCoc A c)
    (hu : ∀ a, c (uni a) = 0) : ∃ m : A, ∀ g, c g = A.ρ g m - m := by
  classical
  haveI := Fintype.ofFinite F
  have c_one : c 1 = 0 := hc.apply_one
  refine ⟨∑ v : Fin 2 → F, c (sec v), fun g => ?_⟩
  have hpt : ∀ v : Fin 2 → F,
      c (sec ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) + (if v = 0 then c g else 0) =
        A.ρ g (c (sec v)) + c g := by
    intro v
    by_cases hv : v = 0
    · subst hv
      simp [sec_zero, c_one, Matrix.mulVec_zero]
    · rw [ite_eq_right hv, add_zero]
      obtain ⟨a, ha⟩ := exists_mul_sec g hv
      have h : c (g * sec v) = c (sec ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v) * uni a) := by
        rw [ha]
      rw [hc, hc, hu, map_zero, zero_add] at h
      exact h.symm
  have h1 : ∑ v : Fin 2 → F, c (sec ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) =
      ∑ v : Fin 2 → F, c (sec v) :=
    Fintype.sum_equiv (Matrix.SpecialLinearGroup.toLin' g).toEquiv _ _ (fun v => by
      simp [Matrix.SpecialLinearGroup.toLin'_apply])
  have h2 : ∑ v : Fin 2 → F, (if v = 0 then c g else (0 : A)) = c g := by simp
  have h3 : ∑ _v : Fin 2 → F, c g = (0 : A) := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul F, Fintype.card_fun,
      Nat.cast_pow, FiniteField.cast_card_eq_zero]
    simp
  have hsum : ∑ v : Fin 2 → F,
      (c (sec ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ v)) + (if v = 0 then c g else 0)) =
        ∑ v : Fin 2 → F, (A.ρ g (c (sec v)) + c g) :=
    Finset.sum_congr rfl (fun v _ => hpt v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, h3, ← map_sum, add_zero] at hsum
  rw [← hsum]
  abel

variable (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) F)

private lemma uni_coboundary [CharP F 3] (he_inj : Function.Injective e)
    (he_range : LinearMap.range e = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F))
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = (g : Matrix (Fin 2) (Fin 2) F) * e a *
        ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))
    {c : SL(2, F) → A} (hc : IsCoc A c) (hT : ∀ s : Fˣ, c (tor s) = 0) :
    ∃ m : A, ∀ a, c (uni a) = A.ρ (uni a) m - m := by
  have htr0 : ∀ a : A, Matrix.trace (e a) = 0 := fun a => by
    have h : e a ∈ LinearMap.range e := LinearMap.mem_range_self e a
    rw [he_range, LinearMap.mem_ker, Matrix.traceLinearMap_apply] at h
    exact h
  have hadd : ∀ a b, e (c (uni (a + b))) =
      !![1, a; 0, 1] * e (c (uni b)) * !![1, -a; 0, 1] + e (c (uni a)) := fun a b => by
    rw [uni_add, hc, map_add, he_act, uni_inv, coe_uni, coe_uni]
  have htor : ∀ s a : F, s ≠ 0 →
      e (c (uni (s ^ 2 * a))) = !![s, 0; 0, s⁻¹] * e (c (uni a)) * !![s⁻¹, 0; 0, s] := by
    intro s a hs
    set S : Fˣ := Units.mk0 s hs with hS
    have hmul : tor S * uni a = uni (s ^ 2 * a) * tor S := tor_mul_uni S a
    have h1 : c (tor S * uni a) = A.ρ (tor S) (c (uni a)) := by rw [hc, hT, add_zero]
    have h2 : c (uni (s ^ 2 * a) * tor S) = c (uni (s ^ 2 * a)) := by
      rw [hc, hT, map_zero, zero_add]
    rw [hmul, h2] at h1
    rw [h1, he_act, tor_inv, coe_tor, coe_tor]
    simp [hS, Units.val_inv_eq_inv_val]
  have htr : ∀ a, (e (c (uni a))) 1 1 = - (e (c (uni a))) 0 0 := fun a => by
    have h := htr0 (c (uni a))
    rw [Matrix.trace_fin_two] at h
    linear_combination h
  obtain ⟨M, hM11, hM⟩ := key (fun a => e (c (uni a))) hadd htor htr
  have hMtr : M ∈ LinearMap.range e := by
    rw [he_range, LinearMap.mem_ker, Matrix.traceLinearMap_apply, Matrix.trace_fin_two, hM11,
      add_neg_cancel]
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 hMtr
  refine ⟨m, fun a => he_inj ?_⟩
  rw [map_sub, he_act, hm, uni_inv, coe_uni, coe_uni]
  exact hM a

private theorem exists_eq_coboundary [Finite F] [CharP F 3] (he_inj : Function.Injective e)
    (he_range : LinearMap.range e = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F))
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = (g : Matrix (Fin 2) (Fin 2) F) * e a *
        ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))
    (x : cocycles₁ A) : ∃ m : A, ∀ g, x g = A.ρ g m - m := by
  have hx : IsCoc A x := (mem_cocycles₁_iff x).1 x.2
  obtain ⟨m₁, h₁⟩ := torus_coboundary hx
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : SL(2, F) → A, ∀ g, c₁ g = x g - (A.ρ g m₁ - m₁) :=
    ⟨_, fun _ => rfl⟩
  have hc₁coc : IsCoc A c₁ := isCoc_sub hx m₁ hc₁
  have hc₁T : ∀ s : Fˣ, c₁ (tor s) = 0 := fun s => by rw [hc₁, h₁, sub_self]
  obtain ⟨m₂, h₂⟩ := uni_coboundary e he_inj he_range he_act hc₁coc hc₁T
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : SL(2, F) → A, ∀ g, c₂ g = c₁ g - (A.ρ g m₂ - m₂) :=
    ⟨_, fun _ => rfl⟩
  have hc₂coc : IsCoc A c₂ := isCoc_sub hc₁coc m₂ hc₂
  have hc₂U : ∀ a, c₂ (uni a) = 0 := fun a => by rw [hc₂, h₂, sub_self]
  obtain ⟨m₃, h₃⟩ := coboundary_of_vanish_uni hc₂coc hc₂U
  refine ⟨m₁ + m₂ + m₃, fun g => ?_⟩
  have h := h₃ g
  rw [hc₂, hc₁] at h
  rw [map_add, map_add]
  linear_combination (norm := abel) h

end Rep

end SL2TraceZeroH1Aux

/-- For a finite field `F` of characteristic `3`, `H^1` of `SL(2, F)` with
coefficients in a representation identified equivariantly and injectively
with the trace-zero `2 x 2` matrices (conjugation action) is a subsingleton,
hence zero. -/
theorem groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three
    {F : Type*} [Field F] [Finite F] [CharP F 3]
    (A : Rep F (Matrix.SpecialLinearGroup (Fin 2) F)) (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (he_inj : Function.Injective e)
    (he_range : LinearMap.range e = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F))
    (he_act : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (a : A),
      e (A.ρ g a) = (g : Matrix (Fin 2) (Fin 2) F) * e a *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    Subsingleton (groupCohomology.H1 A) := by
  have h0 : ∀ z : groupCohomology.H1 A, z = 0 := fun z => by
    refine groupCohomology.H1_induction_on (C := fun z => z = 0) z fun x => ?_
    beta_reduce
    rw [groupCohomology.H1π_eq_zero_iff]
    obtain ⟨m, hm⟩ := SL2TraceZeroH1Aux.exists_eq_coboundary e he_inj he_range he_act x
    exact LinearMap.mem_range.2 ⟨m, funext fun g => by
      rw [groupCohomology.d₀₁_hom_apply]; exact (hm g).symm⟩
  exact ⟨fun a b => (h0 a).trans (h0 b).symm⟩
