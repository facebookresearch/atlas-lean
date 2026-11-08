/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.SU2Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conjugacy in `SU₂` is determined by the trace

Every element of `SU₂` is conjugate in `SU₂` to a diagonal matrix
`diag(z, conj z)` with `z * conj z = 1`, and two elements of `SU₂` with the
same trace are conjugate in `SU₂`. Thus trace distinguishes conjugacy
classes and takes real values in `[-2, 2]` (see
`Matrix.trace_im_eq_zero_of_mem_specialUnitaryGroup_fin_two` and
`Matrix.norm_trace_le_two_of_mem_specialUnitaryGroup_fin_two` in
`MathlibExt/LinearAlgebra/Matrix/SpecialUnitaryFinTwo.lean`).

Source: `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean` (theorems
`su2_conj_to_diag`, `su2_trace_conj_inv`, `su2_diag_conj_of_trace`, and
`su2_conj_of_trace_eq`). The `SU₂` simplicity material in that file, which
depends on the unproved `su2_normal_contains_all_traces` and
`longitude_iso`, is not ported.
-/

@[expose] public section

namespace SU2

open Matrix

set_option maxHeartbeats 1600000 in
/-- Every element of `SU₂` is conjugate in `SU₂` to a diagonal matrix
`diag(z, conj z)` with `z * conj z = 1`. -/
theorem su2_conj_to_diag (A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ∃ (D : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      (∃ z : ℂ, z * starRingEnd ℂ z = 1 ∧
        (D : Matrix (Fin 2) (Fin 2) ℂ) =
          !![z, (0 : ℂ); 0, starRingEnd ℂ z]) ∧ IsConj A D := by
  obtain ⟨α, β, hA, hnorm⟩ :=
    Matrix.exists_eq_of_mem_specialUnitaryGroup_fin_two A.val A.2
  by_cases hβ : β = 0
  ·
    have hα_norm : Complex.normSq α = 1 := by simp [hβ] at hnorm; exact hnorm
    have hz : α * starRingEnd ℂ α = 1 := by
      rw [Complex.mul_conj]; exact_mod_cast hα_norm
    have hA_diag : (A : Matrix (Fin 2) (Fin 2) ℂ) =
        !![α, (0 : ℂ); 0, starRingEnd ℂ α] := by
      rw [hA, hβ]; simp
    exact ⟨A, ⟨α, hz, hA_diag⟩, IsConj.refl A⟩
  ·
    have hβ_pos : Complex.normSq β > 0 := Complex.normSq_pos.mpr hβ
    have hα_lt : Complex.normSq α < 1 := by linarith
    have h_re_lt : α.re ^ 2 < 1 := by
      calc α.re ^ 2 ≤ Complex.normSq α := by
            rw [Complex.normSq_apply]; linarith [sq_nonneg α.im]
        _ < 1 := hα_lt
    set s := Real.sqrt (1 - α.re ^ 2)
    have hs_pos : s > 0 := Real.sqrt_pos.mpr (by linarith)
    have hs_sq : s ^ 2 = 1 - α.re ^ 2 := Real.sq_sqrt (by linarith)
    set z : ℂ := ⟨α.re, s⟩
    have hz : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj]; apply Complex.ext
      · simp [Complex.normSq_apply]; nlinarith [hs_sq]
      · simp
    have hz' : (starRingEnd ℂ) z * z = 1 := by rw [mul_comm]; exact hz
    set D_val : Matrix (Fin 2) (Fin 2) ℂ := !![z, 0; 0, starRingEnd ℂ z]
    have hD_mem : D_val ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [D_val, z, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map]
        · exact hz'
        · left; rfl
        · left; rfl
        · exact hz
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [D_val, z, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map]
        · exact hz
        · right; rfl
        · right; rfl
        · exact hz'
      · simp [D_val, z, det_fin_two]; linear_combination hz
    set D : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := ⟨D_val, hD_mem⟩
    have hN_pos_r : Complex.normSq β + (s - α.im) ^ 2 > 0 := by
      linarith [Complex.normSq_nonneg β, sq_nonneg (s - α.im)]
    set N := Real.sqrt (Complex.normSq β + (s - α.im) ^ 2)
    have hN_pos : N > 0 := Real.sqrt_pos.mpr hN_pos_r
    have hN_sq : N ^ 2 = Complex.normSq β + (s - α.im) ^ 2 :=
      Real.sq_sqrt (by linarith)
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
    set p1 : ℂ := β / (↑N : ℂ)
    set p2 : ℂ := ⟨0, (s - α.im) / N⟩
    have hP_norm : Complex.normSq p1 + Complex.normSq p2 = 1 := by
      simp only [p1, p2, Complex.normSq_apply, Complex.div_ofReal_re,
        Complex.div_ofReal_im]
      have hN_sq' : N * N = Complex.normSq β + (s - α.im) ^ 2 := by
        nlinarith [hN_sq]
      field_simp
      nlinarith [Complex.normSq_apply β, sq_nonneg β.re, sq_nonneg β.im]
    set P_val : Matrix (Fin 2) (Fin 2) ℂ :=
      !![p1, p2; -starRingEnd ℂ p2, starRingEnd ℂ p1]
    have hP_mem : P_val ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
      have hpq : p1 * (starRingEnd ℂ) p1 + p2 * (starRingEnd ℂ) p2 = 1 := by
        rw [Complex.mul_conj, Complex.mul_conj]; exact_mod_cast hP_norm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [P_val, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
        (apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hpq ⊢ <;>
          nlinarith [congr_arg Complex.re hpq, congr_arg Complex.im hpq,
                    Complex.normSq_apply p1, Complex.normSq_apply p2])
      · ext i j; fin_cases i <;> fin_cases j <;>
        simp [P_val, mul_apply, star, conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
        (apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hpq ⊢ <;>
          nlinarith [congr_arg Complex.re hpq, congr_arg Complex.im hpq,
                    Complex.normSq_apply p1, Complex.normSq_apply p2])
      · simp [P_val, det_fin_two]
        linear_combination hpq
    set P : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) := ⟨P_val, hP_mem⟩
    refine ⟨D, ⟨z, hz, rfl⟩, ?_⟩
    rw [isConj_iff]
    refine ⟨P⁻¹, ?_⟩
    apply Subtype.ext
    simp only [Submonoid.coe_mul]
    have hPinv_val : (P⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
        P.val⁻¹ := by
      symm; apply Matrix.inv_eq_left_inv
      have h' := congr_arg Subtype.val
        (show (P⁻¹ * P : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = 1 from
          inv_mul_cancel P)
      simp only [Submonoid.coe_mul, Submonoid.coe_one] at h'; exact h'
    have hPinvinv : ((P⁻¹)⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
        P.val := by rw [inv_inv]
    rw [hPinv_val, hPinvinv]
    have hPdet : P.val.det = 1 := by
      have := P.2.2; simp [MonoidHom.mem_mker] at this; exact this
    have hPunit : IsUnit P.val.det := by rw [hPdet]; exact isUnit_one
    have hPinv_mul : P.val⁻¹ * P.val = 1 := Matrix.nonsing_inv_mul P.val hPunit
    have hnorm_re : α.re ^ 2 + α.im ^ 2 + β.re ^ 2 + β.im ^ 2 = 1 := by
      have := hnorm; rw [Complex.normSq_apply, Complex.normSq_apply] at this; linarith
    have hAP_eq : A.val * P.val = P.val * D.val := by
      rw [show A.val = !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] from hA]
      show !![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α] *
        !![p1, p2; -(starRingEnd ℂ) p2, (starRingEnd ℂ) p1] =
        !![p1, p2; -(starRingEnd ℂ) p2, (starRingEnd ℂ) p1] *
          !![z, 0; 0, (starRingEnd ℂ) z]
      ext i j; fin_cases i <;> fin_cases j <;>
      simp only [mul_apply, Fin.sum_univ_two, of_apply, cons_val_zero, cons_val_one] <;>
      (apply Complex.ext <;>
        simp [p1, p2, z, Complex.mul_re, Complex.mul_im, Complex.conj_re,
          Complex.conj_im] <;>
        field_simp <;>
        nlinarith [hnorm_re, hs_sq, sq_nonneg α.re, sq_nonneg α.im,
          sq_nonneg β.re, sq_nonneg β.im, sq_nonneg s,
          sq_nonneg N, sq_nonneg (s - α.im)])
    calc P.val⁻¹ * A.val * P.val
        = P.val⁻¹ * (A.val * P.val) := by rw [Matrix.mul_assoc]
      _ = P.val⁻¹ * (P.val * D.val) := by rw [hAP_eq]
      _ = (P.val⁻¹ * P.val) * D.val := by rw [Matrix.mul_assoc]
      _ = 1 * D.val := by rw [hPinv_mul]
      _ = D.val := by rw [Matrix.one_mul]

/-- The trace is invariant under conjugation in `SU₂`. -/
theorem su2_trace_conj_inv (P A : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Matrix.trace ((P * A * P⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hval : (P * A * P⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
      P.val * A.val * (P⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val := by
    simp [Submonoid.coe_mul]
  have hinv : (P⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val = P.val⁻¹ := by
    symm; apply Matrix.inv_eq_left_inv
    have h' := congr_arg Subtype.val
      (show (P⁻¹ * P : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = 1 from
        inv_mul_cancel P)
    simp only [Submonoid.coe_mul, Submonoid.coe_one] at h'
    exact h'
  rw [hval, hinv]
  have hunit : IsUnit P.val := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : P.val.det = 1 := by
      have := P.2.2; simp [MonoidHom.mem_mker] at this; exact this
    rw [hdet]; exact isUnit_one
  exact Matrix.trace_conj hunit A.val

/-- Two diagonal elements `diag(z₁, conj z₁)` and `diag(z₂, conj z₂)` of `SU₂`
with the same trace are conjugate in `SU₂`: either `z₁ = z₂`, or
`z₁ = conj z₂` and conjugation by the anti-diagonal matrix swaps the
diagonal entries. -/
theorem su2_diag_conj_of_trace (D₁ D₂ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (z₁ z₂ : ℂ) (hz₁ : z₁ * starRingEnd ℂ z₁ = 1)
    (hz₂ : z₂ * starRingEnd ℂ z₂ = 1)
    (hD₁ : (D₁ : Matrix (Fin 2) (Fin 2) ℂ) =
      !![z₁, (0 : ℂ); 0, starRingEnd ℂ z₁])
    (hD₂ : (D₂ : Matrix (Fin 2) (Fin 2) ℂ) =
      !![z₂, (0 : ℂ); 0, starRingEnd ℂ z₂])
    (htrace : Matrix.trace (D₁ : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace (D₂ : Matrix (Fin 2) (Fin 2) ℂ)) :
    IsConj D₁ D₂ := by
  have ht1 : Matrix.trace (D₁ : Matrix (Fin 2) (Fin 2) ℂ) =
      z₁ + starRingEnd ℂ z₁ := by
    rw [hD₁]; simp [trace_fin_two]
  have ht2 : Matrix.trace (D₂ : Matrix (Fin 2) (Fin 2) ℂ) =
      z₂ + starRingEnd ℂ z₂ := by
    rw [hD₂]; simp [trace_fin_two]
  have hsum : z₁ + starRingEnd ℂ z₁ = z₂ + starRingEnd ℂ z₂ := by
    rw [← ht1, ← ht2]; exact htrace
  have hre : z₁.re = z₂.re := by
    have h := congr_arg Complex.re hsum
    simp [Complex.add_re, Complex.conj_re] at h; linarith
  have him_sq : z₁.im * z₁.im = z₂.im * z₂.im := by
    have h1' := congr_arg Complex.re hz₁; have h2' := congr_arg Complex.re hz₂
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at h1' h2'
    have h3 : z₁.re * z₁.re = z₂.re * z₂.re := by rw [hre]
    linarith
  rcases mul_self_eq_mul_self_iff.mp him_sq with him_eq | him_neg
  ·
    have heq : z₁ = z₂ := Complex.ext hre him_eq
    have hD_eq : D₁ = D₂ := by ext1; rw [hD₁, hD₂, heq]
    rw [hD_eq]
  ·
    have hconj : z₁ = starRingEnd ℂ z₂ := by
      simp [Complex.ext_iff, Complex.conj_re, Complex.conj_im, hre, him_neg]
    let W : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
      ⟨!![(0 : ℂ), 1; -1, 0], antidiag_mem⟩
    rw [isConj_iff]
    refine ⟨W, ?_⟩
    ext1
    have hW_val : (W : Matrix (Fin 2) (Fin 2) ℂ) = !![(0 : ℂ), 1; -1, 0] := rfl
    have hWinv_val : (W⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
        (!![(0 : ℂ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
      have hinv : (W⁻¹ : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).val =
          (W.val)⁻¹ := by
        symm; apply Matrix.inv_eq_left_inv
        have h' := congr_arg Subtype.val
          (show (W⁻¹ * W : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = 1 from
            inv_mul_cancel W)
        simp only [Submonoid.coe_mul, Submonoid.coe_one] at h'
        exact h'
      rw [hinv]
    simp only [Submonoid.coe_mul, hW_val, hD₁, hD₂, hconj, hWinv_val]
    simp [inv_def, adjugate_fin_two, det_fin_two]

/-- **Conjugacy in `SU₂` is determined by the trace.** Two elements of `SU₂`
with the same trace are conjugate in `SU₂`. -/
theorem su2_conj_of_trace_eq (A B : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℂ)) :
    IsConj A B := by
  obtain ⟨D_A, ⟨z_A, hz_A, hD_A⟩, hconj_A⟩ := su2_conj_to_diag A
  obtain ⟨D_B, ⟨z_B, hz_B, hD_B⟩, hconj_B⟩ := su2_conj_to_diag B
  have htrace_D : Matrix.trace (D_A : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace (D_B : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [isConj_iff] at hconj_A hconj_B
    obtain ⟨P_A, hP_A⟩ := hconj_A
    obtain ⟨P_B, hP_B⟩ := hconj_B
    have h1 : Matrix.trace D_A.val = Matrix.trace A.val := by
      rw [← hP_A]; exact su2_trace_conj_inv P_A A
    have h2 : Matrix.trace D_B.val = Matrix.trace B.val := by
      rw [← hP_B]; exact su2_trace_conj_inv P_B B
    rw [show (D_A : Matrix (Fin 2) (Fin 2) ℂ) = D_A.val from rfl,
        show (D_B : Matrix (Fin 2) (Fin 2) ℂ) = D_B.val from rfl]
    rw [h1, h2]; exact h
  have hconj_D := su2_diag_conj_of_trace D_A D_B z_A z_B hz_A hz_B hD_A hD_B htrace_D
  exact hconj_A.trans (hconj_D.trans hconj_B.symm)

end SU2
