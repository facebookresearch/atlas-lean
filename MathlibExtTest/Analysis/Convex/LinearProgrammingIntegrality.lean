/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Convex.LinearProgrammingIntegrality

/-! Clients and countermodels for integral TU basic solutions. -/

open Matrix

namespace TUIntegralityTests

private theorem identity_tu (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ).IsTotallyUnimodular := by
  have h := (emptyRows_isTotallyUnimodular
    (0 : Matrix (Fin 0) (Fin n) ℝ)).fromRows_one
  exact h.submatrix Sum.inr id

private def oneRow : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]

private theorem oneRow_tu : oneRow.IsTotallyUnimodular := by
  convert (identity_tu 1).submatrix id (fun _ : Fin 2 => (0 : Fin 1))
  ext i j
  fin_cases i; fin_cases j <;> norm_num [oneRow, one_apply]

-- A signed basis with determinant -1 and a negative coordinate.
private theorem signed_solution : ∃ z : Fin 1 → ℤ, ∀ i,
    (z i : ℝ) = (![(-3 : ℝ)] : Fin 1 → ℝ) i := by
  have hneg : (!![-1] : Matrix (Fin 1) (Fin 1) ℝ).IsTotallyUnimodular := by
    have h := (emptyRows_isTotallyUnimodular
      (0 : Matrix (Fin 0) (Fin 1) ℝ)).fromRows_unitlike
      (B := !![-1]) (fun _ i => ⟨0, -1, by
        ext j
        fin_cases i; fin_cases j; simp⟩)
    exact h.submatrix Sum.inr id
  apply hneg.exists_int_vec (by norm_num [det_fin_one]) ![3]
  ext i
  fin_cases i
  norm_num [mulVec, dotProduct]

-- Both coordinates are constrained by the original supplied solution.
private theorem two_coordinates : ∃ z : Fin 2 → ℤ, ∀ i,
    (z i : ℝ) = (![(-2 : ℝ), 5] : Fin 2 → ℝ) i := by
  apply (identity_tu 2).exists_int_vec (by simp) ![-2, 5]
  ext i
  fin_cases i <;> norm_num

-- A genuine rectangular TU matrix with a selected 2-by-2 basis.
private theorem rectangular_basis : ∃ z : Fin 2 → ℤ, ∀ i,
    (z i : ℝ) = (![(-2 : ℝ), 5] : Fin 2 → ℝ) i := by
  let A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) ℝ := fromRows 1 1
  have hA : A.IsTotallyUnimodular := (identity_tu 2).fromRows_one
  have hB := hA.submatrix Sum.inr id
  apply hB.exists_int_vec (by
    change (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0
    simp) ![-2, 5]
  ext i
  fin_cases i <;> norm_num [A, submatrix, mulVec, dotProduct, Fin.sum_univ_two]

-- No positive-dimension assumption, even on the solution's type.
private theorem empty_system (x : Fin 0 → ℝ) :
    ∃ z : Fin 0 → ℤ, ∀ i, (z i : ℝ) = x i := by
  apply (emptyRows_isTotallyUnimodular
    (0 : Matrix (Fin 0) (Fin 0) ℝ)).exists_int_vec (by simp) (fun _ => 0)
  ext i
  exact Fin.elim0 i

private def activeRows : Fin 2 → Fin 1 ⊕ Fin 2 := ![Sum.inl 0, Sum.inr 1]

private theorem active_det :
    ((fromRows oneRow (-1)).submatrix activeRows id).det = -1 := by
  norm_num [det_fin_two, oneRow, activeRows, submatrix, one_apply]

private theorem active_tight :
    ((fromRows oneRow (-1)).submatrix activeRows id) *ᵥ ![(3 : ℝ), 0] =
      fun i => ((Sum.elim (![3] : Fin 1 → ℤ) (fun _ => 0)
        (activeRows i) : ℤ) : ℝ) := by
  ext i
  fin_cases i <;>
    norm_num [mulVec, dotProduct, Fin.sum_univ_two, oneRow, activeRows,
      submatrix, one_apply]

-- x=(3,0): the A row and the second nonnegativity row are tight.
private theorem active_nonnegativity : ∃ z : Fin 2 → ℤ, ∀ i,
    (z i : ℝ) = (![(3 : ℝ), 0] : Fin 2 → ℝ) i := by
  apply oneRow_tu.exists_int_vec_of_basic_feasible ![3]
    (by intro j; fin_cases j <;> norm_num)
    (by
      intro i; fin_cases i
      norm_num [oneRow, mulVec, dotProduct, Fin.sum_univ_two])
    activeRows
  · rw [active_det]
    norm_num
  · exact active_tight

-- With no original inequalities, nonnegativity rows alone give the zero basis.
private theorem nonnegativity_only : ∃ z : Fin 1 → ℤ,
    ∀ i, (z i : ℝ) = (0 : Fin 1 → ℝ) i := by
  apply (emptyRows_isTotallyUnimodular
    (0 : Matrix (Fin 0) (Fin 1) ℝ)).exists_int_vec_of_basic_feasible
      (fun _ => 0) (by simp) (by intro i; exact Fin.elim0 i) Sum.inr
  · norm_num [det_fin_one, submatrix, one_apply]
  · ext i
    fin_cases i
    simp [submatrix, mulVec, dotProduct]

-- Empty variables and empty inequalities are admitted by the LP consumer.
private theorem empty_lp (x : Fin 0 → ℝ) :
    ∃ z : Fin 0 → ℤ, ∀ i, (z i : ℝ) = x i := by
  apply (emptyRows_isTotallyUnimodular
    (0 : Matrix (Fin 0) (Fin 0) ℝ)).exists_int_vec_of_basic_feasible
      (fun _ => 0) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) Fin.elim0
      (by simp)
  ext i
  exact Fin.elim0 i

private theorem half_not_integral : ¬ ∃ z : ℤ, (z : ℝ) = 1 / 2 := by
  rintro ⟨z, hz⟩
  have hpos : (0 : ℝ) < z := by rw [hz]; norm_num
  have hlt : (z : ℝ) < 1 := by rw [hz]; norm_num
  have hp : (0 : ℤ) < z := by exact_mod_cast hpos
  have hl : z < (1 : ℤ) := by exact_mod_cast hlt
  omega

-- Omitting TU permits the nonsingular integer equation 2x=1.
private theorem non_tu_system :
    (!![2] : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0 ∧
    (!![2] : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1 / 2] = ![1] ∧
    ¬ ∃ z : ℤ, (z : ℝ) = 1 / 2 := by
  exact ⟨by norm_num [det_fin_one], by
    ext i; fin_cases i; norm_num [mulVec, dotProduct], half_not_integral⟩

private theorem two_not_tu :
    ¬ (!![2] : Matrix (Fin 1) (Fin 1) ℝ).IsTotallyUnimodular := by
  intro h
  obtain ⟨s, hs⟩ := h.apply 0 0
  cases s <;> norm_num at hs

-- Omitting nonsingularity permits 0x=0 with the same fractional x.
private theorem singular_system :
    (0 : Matrix (Fin 1) (Fin 1) ℝ).IsTotallyUnimodular ∧
    (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1 / 2] = 0 ∧
    ¬ ∃ z : ℤ, (z : ℝ) = 1 / 2 := by
  refine ⟨?_, by simp, half_not_integral⟩
  have h := (emptyRows_isTotallyUnimodular
    (0 : Matrix (Fin 0) (Fin 1) ℝ)).fromRows_unitlike
    (B := (0 : Matrix (Fin 1) (Fin 1) ℝ))
    (fun _ _ => ⟨0, 0, by ext j; simp⟩)
  exact h.submatrix Sum.inr id

-- Omitting the integer RHS permits x=1/2 for the identity system.
private theorem fractional_rhs :
    (1 : Matrix (Fin 1) (Fin 1) ℝ).IsTotallyUnimodular ∧
    (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0 ∧
    (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ![1 / 2] = ![1 / 2] ∧
    ¬ ∃ z : ℤ, (z : ℝ) = 1 / 2 := by
  exact ⟨identity_tu 1, by simp, by simp, half_not_integral⟩

-- The fractional point is feasible and optimal for objective (1,1).
-- Neither feasibility nor optimality replaces a nonsingular tight basis.
private theorem fractional_optimum :
    (∀ j, 0 ≤ (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) j) ∧
    (∀ i, (oneRow *ᵥ ![(1 / 2 : ℝ), 1 / 2]) i ≤ 1) ∧
    (∀ y : Fin 2 → ℝ, (∀ i, (oneRow *ᵥ y) i ≤ 1) →
      (![1, 1] : Fin 2 → ℝ) ⬝ᵥ y ≤
        (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![(1 / 2 : ℝ), 1 / 2]) ∧
    ¬ ∃ z : Fin 2 → ℤ, ∀ i,
      (z i : ℝ) = (![(1 / 2 : ℝ), 1 / 2] : Fin 2 → ℝ) i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num
  · intro i
    fin_cases i
    norm_num [oneRow, mulVec, dotProduct, Fin.sum_univ_two]
  · intro y hy
    have hy0 := hy 0
    norm_num [oneRow, mulVec, dotProduct, Fin.sum_univ_two] at hy0 ⊢
    exact hy0
  · rintro ⟨z, hz⟩
    exact half_not_integral ⟨z 0, hz 0⟩

end TUIntegralityTests
