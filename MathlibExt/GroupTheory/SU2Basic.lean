/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Basic structure of `SU₂`

An element of `SU₂`, the special unitary group of `2 × 2` complex matrices,
has the form `!![α, β; -conj β, conj α]` with `‖α‖² + ‖β‖² = 1`. Its center
is `{1, -1}`, its trace is real, and its trace has norm at most `2`.

Source: `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean` (theorems
`su2_matrix_form`, `su2_center_mem_iff`, `su2_trace_real`, and
`su2_trace_bound`, with the auxiliary membership lemmas `D_mem_SU2` and
`W_mem_SU2`). The `SU₂` simplicity material in that file, which depends on
the unproved `su2_normal_contains_all_traces` and `longitude_iso`, is not
ported here; see `MathlibExt/GroupTheory/SU2Conjugacy.lean` for the
fully proved conjugacy-by-trace results from the same file.
-/

@[expose] public section

namespace SU2

open Matrix

/-- The diagonal matrix `diag(I, -I)` lies in `SU₂`. It is used to show that
a central element of `SU₂` is diagonal. -/
theorem diag_I_mem :
    !![Complex.I, (0 : ℂ); 0, -Complex.I] ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
          Matrix.map, Complex.I] <;>
    first | (apply Complex.ext <;> simp) | left; (apply Complex.ext <;> simp)
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
          Matrix.map, Complex.I] <;>
    first | (apply Complex.ext <;> simp) | right; (apply Complex.ext <;> simp)
  · simp [Matrix.detMonoidHom, Matrix.det_fin_two, Complex.I]
    apply Complex.ext <;> simp

/-- The anti-diagonal matrix `!![0, 1; -1, 0]` lies in `SU₂`. It is used to
show that a central element of `SU₂` has equal diagonal entries, and to
conjugate one diagonal element of `SU₂` to its conjugate. -/
theorem antidiag_mem :
    !![(0 : ℂ), 1; -1, 0] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
    (apply Complex.ext <;> simp)
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
    (apply Complex.ext <;> simp)
  · simp [Matrix.detMonoidHom, Matrix.det_fin_two]

/-- **Matrix form of `SU₂`.** Every `M ∈ SU₂` is `!![α, β; -conj β, conj α]`
with `‖α‖² + ‖β‖² = 1`, where `α = M 0 0` and `β = M 0 1`. -/
theorem su2_matrix_form (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : M ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ (α β : ℂ), M = !![α, β; -starRingEnd ℂ β, starRingEnd ℂ α] ∧
      Complex.normSq α + Complex.normSq β = 1 := by
  set α := M 0 0
  set β := M 0 1
  have hdet : M.det = 1 := by
    have := hU.2; simp [MonoidHom.mem_mker] at this; exact this
  have hunit : star M * M = 1 := hU.1.1
  have hstarM : star M = M⁻¹ := (Matrix.inv_eq_left_inv hunit).symm
  have hinv : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet]; simp [Ring.inverse_one]
  have hstarAdj := hstarM.trans hinv
  refine ⟨α, β, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [α, β]
    ·
      have h := congr_fun (congr_fun hstarAdj 0) 1
      simp [Matrix.adjugate_fin_two] at h
      have := congr_arg (starRingEnd ℂ) h
      simp [map_neg] at this
      exact this
    ·
      have h := congr_fun (congr_fun hstarAdj 0) 0
      simp [Matrix.adjugate_fin_two] at h
      exact h.symm
  ·
    have hunit2 := hU.1.2
    have h00 := congr_fun (congr_fun hunit2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    rw [Complex.mul_conj, Complex.mul_conj] at h00
    exact_mod_cast h00

/-- **Center of `SU₂`.** A matrix in `SU₂` is central iff it is `1` or `-1`. -/
theorem su2_center_mem_iff (M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    M ∈ Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) ↔
    (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∨
      (M : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  constructor
  · intro hM
    rw [Subgroup.mem_center_iff] at hM
    have comm_of (g_val : Matrix (Fin 2) (Fin 2) ℂ)
        (g_mem : g_val ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        (M : Matrix (Fin 2) (Fin 2) ℂ) * g_val =
          g_val * (M : Matrix (Fin 2) (Fin 2) ℂ) := by
      have h := hM ⟨g_val, g_mem⟩
      have hv := congr_arg Subtype.val h
      simp only [Submonoid.coe_mul] at hv
      exact hv.symm
    have hDcomm := comm_of _ diag_I_mem
    have hM01 : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      have h := congr_fun (congr_fun hDcomm 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      have h1 : Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
        have heq : -(Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) =
            Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
          rw [mul_comm ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1)] at h; exact h
        have h2 : (2 : ℂ) * (Complex.I * (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 0 := by
          linear_combination -heq
        exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
      exact (mul_eq_zero.mp h1).resolve_left Complex.I_ne_zero
    have hM10 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      have h := congr_fun (congr_fun hDcomm 1) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      rw [mul_comm Complex.I ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0)] at h
      have h2 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * Complex.I = 0 := by
        have : (2 : ℂ) * ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * Complex.I) = 0 := by
          linear_combination h
        exact (mul_eq_zero.mp this).resolve_left (by norm_num)
      exact (mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero
    have hWcomm := comm_of _ antidiag_mem
    have hdiag : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
        (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
      have h := congr_fun (congr_fun hWcomm 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at h
      exact h
    have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
      have := M.2.2; simp [MonoidHom.mem_mker] at this; exact this
    rw [Matrix.det_fin_two] at hdet
    rw [hM01, hM10] at hdet
    simp at hdet
    rw [hdiag] at hdet
    have ha := mul_self_eq_one_iff.mp hdet
    rcases ha with ha1 | ha_neg1
    · left
      ext i j; fin_cases i <;> fin_cases j <;> simp [hM01, hM10, hdiag, ha1]
    · right
      ext i j; fin_cases i <;> fin_cases j <;> simp [hM01, hM10, hdiag, ha_neg1]
  · intro hM_eq
    rw [Subgroup.mem_center_iff]
    intro g
    ext1
    simp only [Submonoid.coe_mul]
    rcases hM_eq with h1 | h_neg1
    · simp [h1]
    · simp [h_neg1]

/-- The center of `SU₂` is a proper subgroup: `diag(I, -I)` is not central. -/
theorem su2_center_ne_top :
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) ≠ ⊤ := by
  intro heq
  have hmem : (⟨!![Complex.I, (0 : ℂ); 0, -Complex.I], diag_I_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    heq ▸ Subgroup.mem_top _
  rw [su2_center_mem_iff] at hmem
  rcases hmem with h | h
  · have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
    have him := congr_arg Complex.im h00
    simp at him
  · have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
    have him := congr_arg Complex.im h00
    simp at him

/-- The trace of a matrix in `SU₂` is real. -/
theorem su2_trace_real (M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    (Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ)).im = 0 := by
  rw [Matrix.trace_fin_two]
  have hU := M.2
  have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    have := hU.2; simp [MonoidHom.mem_mker] at this; exact this
  have hunit : star (M : Matrix (Fin 2) (Fin 2) ℂ) *
      (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 := hU.1.1
  have hstarM : star (M : Matrix (Fin 2) (Fin 2) ℂ) =
      (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
    (Matrix.inv_eq_left_inv hunit).symm
  have hinv : (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
      (M : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    rw [Matrix.inv_def, hdet]; simp [Ring.inverse_one]
  have hstarAdj := hstarM.trans hinv
  have h00 := congr_fun (congr_fun hstarAdj 0) 0
  simp [Matrix.adjugate_fin_two] at h00
  rw [show (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
    (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
      (starRingEnd ℂ) ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
    from by rw [← h00]]
  rw [Complex.add_conj]
  simp

/-- The trace of a matrix in `SU₂` has norm at most `2`. -/
theorem su2_trace_bound (M : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    ‖Matrix.trace (M : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 := by
  rw [Matrix.trace_fin_two]
  have hU := M.2
  have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    have := hU.2; simp [MonoidHom.mem_mker] at this; exact this
  have hstarAdj : star (M : Matrix (Fin 2) (Fin 2) ℂ) =
      (M : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    have hunit : star (M : Matrix (Fin 2) (Fin 2) ℂ) *
        (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 := hU.1.1
    have hstarM : star (M : Matrix (Fin 2) (Fin 2) ℂ) =
        (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
      (Matrix.inv_eq_left_inv hunit).symm
    have hinv : (M : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
        (M : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
      rw [Matrix.inv_def, hdet]; simp [Ring.inverse_one]
    exact hstarM.trans hinv
  have h00 := congr_fun (congr_fun hstarAdj 0) 0
  simp [Matrix.adjugate_fin_two] at h00
  rw [show (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
    (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
      (starRingEnd ℂ) ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
    from by rw [← h00]]
  rw [Complex.add_conj]
  simp [Real.norm_eq_abs]
  have hunit2 := hU.1.2
  have h00' := congr_fun (congr_fun hunit2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00'
  rw [Complex.mul_conj, Complex.mul_conj] at h00'
  have h00_real : (Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) : ℝ) +
    (Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1) : ℝ) = 1 := by
    exact_mod_cast h00'
  have hnsq : Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ≤ 1 := by
    linarith [Complex.normSq_nonneg ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1)]
  have hre_sq : ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 ≤ 1 ^ 2 := by
    calc ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2
        ≤ ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ^ 2 +
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im ^ 2 := by
          linarith [sq_nonneg ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im]
      _ = Complex.normSq ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
          rw [Complex.normSq_apply]; ring
      _ ≤ 1 := hnsq
      _ = 1 ^ 2 := by ring
  exact abs_le_of_sq_le_sq hre_sq (by norm_num)

end SU2
