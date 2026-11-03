/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.lean`
and
`P2M/Sol/S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.lean`
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

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Parabolic elements of the modular group

Every element of `SL(2, ℤ)` whose trace squares to `4` is, up to a sign,
conjugate to a power of the translation `T = [[1, 1], [0, 1]]`.
-/

@[expose] public section

open scoped MatrixGroups

namespace ParabolicClassificationAux

private theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

private theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem inv_entries (A : SL(2, ℤ)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  have h : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h]

private theorem exists_col_eq {p r : ℤ} (h : IsCoprime p r) :
    ∃ δ : SL(2, ℤ), δ 0 0 = p ∧ δ 1 0 = r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![p, -v; r, u], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination huv

private theorem eq_T_zpow_of_col {M : SL(2, ℤ)} (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) :
    M = ModularGroup.T ^ (M 0 1) := by
  have hdet := det_entries M
  rw [h00, h10, one_mul, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [ModularGroup.coe_T_zpow]

private theorem exists_isCoprime_fixed {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hc : γ 1 0 ≠ 0) :
    ∃ p r : ℤ, IsCoprime p r ∧
      γ 0 0 * p + γ 0 1 * r = p ∧ γ 1 0 * p + γ 1 1 * r = r := by
  rw [Matrix.trace_fin_two] at htr
  have hdet := det_entries γ
  have hgcd_pos : 0 < Int.gcd (γ 0 0 - 1) (γ 1 0) := by
    rcases Nat.eq_zero_or_pos (Int.gcd (γ 0 0 - 1) (γ 1 0)) with h | h
    · exact absurd (Int.gcd_eq_zero_iff.mp h).2 hc
    · exact h
  obtain ⟨p, r, hpr, hp, hr⟩ := Int.exists_gcd_one hgcd_pos
  set g : ℤ := (Int.gcd (γ 0 0 - 1) (γ 1 0) : ℤ) with hgdef
  have hgne : g ≠ 0 := by
    rw [hgdef]
    exact_mod_cast hgcd_pos.ne'
  refine ⟨p, r, Int.isCoprime_iff_gcd_eq_one.mpr hpr, ?_, ?_⟩
  · have key : g * (γ 0 0 * p + γ 0 1 * r - p) = 0 := by
      linear_combination (-(γ 0 0 - 1)) * hp - γ 0 1 * hr + γ 0 0 * htr - hdet
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith
  · have key : g * (γ 1 0 * p + γ 1 1 * r - r) = 0 := by
      linear_combination (-(γ 1 0)) * hp - (γ 1 1 - 1) * hr + γ 1 0 * htr
    have h0 := (mul_eq_zero.mp key).resolve_left hgne
    linarith

private theorem exists_conj_T_zpow_of_trace_eq_two {γ : SL(2, ℤ)}
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) :
    ∃ (δ : SL(2, ℤ)) (n : ℤ), γ = δ * ModularGroup.T ^ n * δ⁻¹ := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hdet := det_entries γ
    rw [hc, mul_zero, sub_zero] at hdet
    rw [Matrix.trace_fin_two] at htr
    have hsq : (γ 0 0 - 1) ^ 2 = 0 := by
      linear_combination γ 0 0 * htr - hdet
    have ha : γ 0 0 = 1 := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    refine ⟨1, γ 0 1, ?_⟩
    rw [inv_one, mul_one, one_mul]
    exact eq_T_zpow_of_col ha hc
  · obtain ⟨p, r, hpr, hfix1, hfix2⟩ := exists_isCoprime_fixed htr hc
    obtain ⟨δ, hδ00, hδ10⟩ := exists_col_eq hpr
    obtain ⟨hi00, hi01, hi10, hi11⟩ := inv_entries δ
    have hδdet := det_entries δ
    rw [hδ00, hδ10] at hδdet
    have hγδ0 : (γ * δ) 0 0 = δ 0 0 := by
      rw [mul_entry γ δ 0 0, hδ00, hδ10]; exact hfix1
    have hγδ1 : (γ * δ) 1 0 = δ 1 0 := by
      rw [mul_entry γ δ 1 0, hδ00, hδ10]; exact hfix2
    have hM00 : (δ⁻¹ * (γ * δ)) 0 0 = 1 := by
      rw [mul_entry δ⁻¹ (γ * δ) 0 0, hγδ0, hγδ1, hi00, hi01, hδ00, hδ10]
      linear_combination hδdet
    have hM10 : (δ⁻¹ * (γ * δ)) 1 0 = 0 := by
      rw [mul_entry δ⁻¹ (γ * δ) 1 0, hγδ0, hγδ1, hi10, hi11, hδ00, hδ10]
      ring
    refine ⟨δ, (δ⁻¹ * (γ * δ)) 0 1, ?_⟩
    rw [← eq_T_zpow_of_col hM00 hM10]
    group

private theorem classification (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (n : ℤ), (ε = 1 ∨ ε = -1) ∧
      γ = ε * (δ * ModularGroup.T ^ n * δ⁻¹) := by
  have hsplit : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination hγ
  rcases mul_eq_zero.mp hsplit with h | h
  · obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two (γ := γ) (by linarith)
    exact ⟨1, δ, n, Or.inl rfl, by rw [one_mul]; exact hδ⟩
  · have htrneg : ((-γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]
      linarith
    obtain ⟨δ, n, hδ⟩ := exists_conj_T_zpow_of_trace_eq_two htrneg
    refine ⟨-1, δ, n, Or.inr rfl, ?_⟩
    rw [neg_one_mul, ← hδ, neg_neg]

end ParabolicClassificationAux

namespace ModularGroup

/-- Every element of `SL(2, ℤ)` whose trace squares to `4` is, up to a sign,
conjugate to a power of the translation `T`. -/
theorem exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧
      γ = ε * (δ * ModularGroup.T ^ h * δ⁻¹) :=
  ParabolicClassificationAux.classification γ hγ

end ModularGroup
