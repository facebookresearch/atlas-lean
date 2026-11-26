/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.BlockEncoding
import Mathlib.Tactic.FinCases

/-!
# Tests: block encodings
-/

@[expose] public section

namespace MathlibExtTest.Quantum.BlockEncoding

set_option autoImplicit false

open MathlibExt.Quantum.BlockEncoding
open scoped Matrix Matrix.Norms.L2Operator Kronecker

private theorem fin01_ne : (0 : Fin 2) ≠ 1 := by decide

private theorem fin10_ne : (1 : Fin 2) ≠ 0 := by decide

private theorem norm_two : ‖(2 : ℂ)‖ = (2 : ℝ) := by
  simp only [RCLike.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]

private theorem norm_four : ‖(4 : ℂ)‖ = (4 : ℝ) := by
  simp only [RCLike.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num)]

private theorem norm_five : ‖(5 : ℂ)‖ = (5 : ℝ) := by
  simp only [RCLike.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num)]

private theorem star_three_fifths : star (3 / 5 : ℂ) = (3 / 5 : ℂ) := by
  show starRingEnd ℂ (3 / 5 : ℂ) = _
  simp only [map_div₀, map_ofNat]

private theorem star_four_fifths : star (4 / 5 : ℂ) = (4 / 5 : ℂ) := by
  show starRingEnd ℂ (4 / 5 : ℂ) = _
  simp only [map_div₀, map_ofNat]

private theorem star_neg_four_fifths : star (-4 / 5 : ℂ) = (-4 / 5 : ℂ) := by
  show starRingEnd ℂ (-4 / 5 : ℂ) = _
  simp only [map_neg, map_div₀, map_ofNat]

private theorem pauliX_mem : !![(0 : ℂ), 1; 1, 0] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_unitaryGroup_iff.mpr ?_
  ext i j
  show (∑ k : Fin 2, !![(0 : ℂ), 1; 1, 0] i k * star (!![(0 : ℂ), 1; 1, 0] j k)) =
    (if i = j then (1 : ℂ) else 0)
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      star_zero, star_one, fin01_ne, fin10_ne] <;> ring

private theorem rot1_mem :
    !![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_unitaryGroup_iff.mpr ?_
  ext i j
  show (∑ k : Fin 2, !![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] i k *
      star (!![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] j k)) =
    (if i = j then (1 : ℂ) else 0)
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      star_three_fifths, star_four_fifths, star_neg_four_fifths, fin01_ne, fin10_ne,
      map_div₀, map_neg, map_ofNat] <;> ring

-- trivial encoding (Definition 44) on Pauli X
example : IsBlockEncoding !![(0 : ℂ), 1; 1, 0] 1 0 (0 : Fin 1) (trivialEncoding !![(0 : ℂ), 1; 1, 0]) := by
  exact isBlockEncoding_self pauliX_mem

-- order sensitivity: the product unitary encodes `A * B`, not `B * A`
example :
    ancillaBlock ((0 : Fin 1), (0 : Fin 1))
        (ancillaMul (trivialEncoding !![(0 : ℂ), 1; 1, 0]) (trivialEncoding !![(1 : ℂ), 0; 0, -1])) =
      !![(0 : ℂ), 1; 1, 0] * !![(1 : ℂ), 0; 0, -1] := by
  rw [ancillaBlock_ancillaMul, ancillaBlock_trivialEncoding, ancillaBlock_trivialEncoding]
example : !![(0 : ℂ), 1; 1, 0] * !![(1 : ℂ), 0; 0, -1] ≠ !![(1 : ℂ), 0; 0, -1] * !![(0 : ℂ), 1; 1, 0] := by
  intro h
  have h01 := congrFun (congrFun h 0) (1 : Fin 2)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, zero_mul, one_mul, mul_zero, mul_one, zero_add, add_zero] at h01
  have h2 := congrArg Complex.re h01
  simp at h2
  norm_num at h2

-- subnormalization: a rotation on one ancilla qubit encodes (3/5) • 1 with α = 1, ε = 0
example : IsBlockEncoding ((3 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 (0 : Fin 2)
    (!![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (by simp)
  have hR : (!![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∈
      Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker_mem_unitary rot1_mem h1
  refine ⟨hR, ?_, zero_le_one, le_rfl⟩
  have h0 : (3 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - ((1 : ℝ) : ℂ) • ancillaBlock (0 : Fin 2)
      (!![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
    ext i j
    show (3 / 5 : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j) - ((1 : ℝ) : ℂ) *
        (!![(3 / 5 : ℂ), -4 / 5; 4 / 5, 3 / 5] 0 0 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)) = 0
    simp [Matrix.cons_val_zero, Matrix.head_cons, map_one]
  rw [h0]
  simp

-- zero-error boundary
example {A B : Matrix (Fin 2) (Fin 2) ℂ} {U V : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ}
    (hU : IsBlockEncoding A 1 0 (0 : Fin 1) U) (hV : IsBlockEncoding B 1 0 (0 : Fin 1) V) :
    IsBlockEncoding (A * B) (1 * 1) 0 ((0 : Fin 1), (0 : Fin 1)) (ancillaMul U V) := by
  simpa using IsBlockEncoding.mul hU hV zero_le_one zero_le_one

private theorem t6a : IsBlockEncoding ((3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 1 (1 / 2)
    (0 : Fin 1) (trivialEncoding 1) := by
  have h1mem : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Matrix.unitaryGroup (Fin 1) ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (by simp)
  obtain ⟨hmem, -, -, -⟩ := isBlockEncoding_self h1mem
  refine ⟨hmem, ?_, zero_le_one, by norm_num⟩
  rw [ancillaBlock_trivialEncoding, Complex.ofReal_one]
  have h32 : (3 / 2 : ℂ) - 1 = 1 / 2 := by ring
  have hsub : (3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) - (1 : ℂ) • 1 = (1 / 2 : ℂ) • 1 := by
    ext i j
    show (3 / 2 : ℂ) * ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j) -
        1 * ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j) = (1 / 2 : ℂ) * ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
    rw [← sub_mul, h32]
  rw [hsub]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, norm_two]
  have h1norm : ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary h1mem
  simp [norm_smul, h12, h1norm]

-- erratum witness: the stated bound α ε + β δ fails without ‖B‖ ≤ β
example :
    IsBlockEncoding ((3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) 1 (1 / 2) (0 : Fin 1)
        (trivialEncoding 1) ∧
    ¬ IsBlockEncoding (((3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((3 / 2 : ℂ) • 1)) (1 * 1)
        (1 * (1 / 2) + 1 * (1 / 2)) ((0 : Fin 1), (0 : Fin 1))
        (ancillaMul (trivialEncoding (1 : Matrix (Fin 1) (Fin 1) ℂ)) (trivialEncoding 1)) := by
  refine ⟨t6a, ?_⟩
  intro h
  obtain ⟨-, hnorm, -, -⟩ := h
  have h3232 : (3 / 2 : ℂ) * (3 / 2) = 9 / 4 := by ring
  have hAB : ((3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((3 / 2 : ℂ) • 1) =
      (9 / 4 : ℂ) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, mul_one, smul_eq_mul, h3232]
  have hblk : ancillaBlock ((0 : Fin 1), (0 : Fin 1))
      (ancillaMul (trivialEncoding (1 : Matrix (Fin 1) (Fin 1) ℂ)) (trivialEncoding 1)) =
      1 := by
    rw [ancillaBlock_ancillaMul, ancillaBlock_trivialEncoding, mul_one]
  have h94 : (9 / 4 : ℂ) - 1 = 5 / 4 := by ring
  have hsub' : (9 / 4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) - (1 : ℂ) • 1 = (5 / 4 : ℂ) • 1 := by
    ext i j
    show (9 / 4 : ℂ) * ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j) -
        1 * ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j) = (5 / 4 : ℂ) * ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
    rw [← sub_mul, h94]
  have hdiff : ((3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((3 / 2 : ℂ) • 1) -
      ((1 * 1 : ℝ) : ℂ) • ancillaBlock ((0 : Fin 1), (0 : Fin 1))
        (ancillaMul (trivialEncoding (1 : Matrix (Fin 1) (Fin 1) ℂ)) (trivialEncoding 1)) =
      (5 / 4 : ℂ) • 1 := by
    rw [hAB, hblk, Complex.ofReal_mul, Complex.ofReal_one, mul_one, hsub']
  have h54 : ‖(5 / 4 : ℂ)‖ = 5 / 4 := by rw [norm_div, norm_five, norm_four]
  have h1mem : (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Matrix.unitaryGroup (Fin 1) ℂ :=
    Matrix.mem_unitaryGroup_iff.mpr (by simp)
  have hnorm5 : ‖(5 / 4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)‖ = 5 / 4 := by
    have h1norm : ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary h1mem
    simp [norm_smul, h54, h1norm]
  rw [hdiff, hnorm5] at hnorm
  norm_num at hnorm

-- tightness of the corrected term on the same instance
example :
    IsBlockEncoding (((3 / 2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) * ((3 / 2 : ℂ) • 1)) (1 * 1)
        (1 * (1 / 2) + 1 * (1 / 2) + 1 / 2 * (1 / 2)) ((0 : Fin 1), (0 : Fin 1))
        (ancillaMul (trivialEncoding (1 : Matrix (Fin 1) (Fin 1) ℂ)) (trivialEncoding 1)) := by
  exact IsBlockEncoding.mul t6a t6a zero_le_one zero_le_one

private def diagProj : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]

private theorem diagProj_star : IsStarProjection diagProj := by
  show IsStarProjection (Matrix.diagonal ![1, 0])
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

private theorem smul_projection_diag_example :
    IsStarProjection diagProj ∧
      projEncoding diagProj ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ ∧
      IsBlockEncoding ((2 : ℂ) • diagProj) 2 0 (0 : Fin 2) (projEncoding diagProj) := by
  exact ⟨diagProj_star, projEncoding_mem_unitaryGroup diagProj_star,
    isBlockEncoding_smul_projection diagProj_star 2 (by norm_num)⟩

private theorem qubit_product_diag_example :
    IsQubitBlockEncoding (s := 1) (a := 1 + 1)
      (((2 : ℂ) • diagProj) * ((3 : ℂ) • diagProj)) (2 * 3) (2 * 0 + 3 * 0 + 0 * 0)
      (Matrix.reindex ((qubitAncillaEquiv 1 1).prodCongr (Equiv.refl _))
        ((qubitAncillaEquiv 1 1).prodCongr (Equiv.refl _))
        (ancillaMul (projEncoding diagProj) (projEncoding diagProj))) := by
  have hU : IsQubitBlockEncoding (s := 1) (a := 1) ((2 : ℂ) • diagProj) 2 0
      (projEncoding diagProj) :=
    isBlockEncoding_smul_projection diagProj_star 2 (by norm_num)
  have hV : IsQubitBlockEncoding (s := 1) (a := 1) ((3 : ℂ) • diagProj) 3 0
      (projEncoding diagProj) :=
    isBlockEncoding_smul_projection diagProj_star 3 (by norm_num)
  exact IsQubitBlockEncoding.mul hU hV (by norm_num) (by norm_num)

end MathlibExtTest.Quantum.BlockEncoding
