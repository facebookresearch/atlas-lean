/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Probability.Statistics.Measurement.StructuralEquation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Tests for DAG-supported nilpotency and Gaussian covariance-fit discrepancy

Boundary tests for `MathlibExt.Probability.Statistics.Measurement.StructuralEquation`:
a 3-chain, which is nilpotent, and a 2-cycle, which is not nilpotent and has no
topological order.

Boundary tests for `gaussianDiscrepancy`: one-two, singular, two-one, and
identity cases (Bartlett, STAT 241A (2007), Lemma 2).

Boundary tests for the three-time-point linear growth model (D08.1): an
identity-covariance example, a two-time-point non-identification witness,
and an inadmissible input (Duncan and Duncan (2009)).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement.Test

open MathlibExt.Probability.Statistics.Measurement

/-- The chain `0 → 1 → 2` as a coefficient matrix. -/
def chain3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 2, 0, 0; 0, 3, 0]

/-- The 2-cycle as a coefficient matrix. -/
def cycle2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem chain3_hord : ∀ v : Fin 3, v.val < Fintype.card (Fin 3) := by
  intro v
  rw [Fintype.card_fin]
  exact v.isLt

private theorem chain3_hB : ∀ i j, chain3 i j ≠ 0 → j.val < i.val := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [chain3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- `chain3 ^ 2 ≠ 0`: the `(2, 0)` entry is `6`. -/
theorem chain3_sq_ne_zero : chain3 ^ 2 ≠ 0 := by
  intro h
  have h20 : (chain3 ^ 2) 2 0 = (0 : Matrix (Fin 3) (Fin 3) ℝ) 2 0 := by rw [h]
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three, chain3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.zero_apply] at h20

/-- `chain3 ^ 3 = 0` by nilpotency with `ord i = i.val`. -/
theorem chain3_cube : chain3 ^ 3 = 0 := by
  have h := pow_card_eq_zero_of_topologicalOrder (B := chain3)
    (ord := fun i => i.val) chain3_hord chain3_hB
  rwa [Fintype.card_fin] at h

/-- `(1 - chain3)⁻¹` is the finite geometric series. -/
theorem chain3_inv : (1 - chain3)⁻¹ = !![1, 0, 0; 2, 1, 0; 6, 3, 1] := by
  have h := inv_one_sub_eq_sum_pow_of_topologicalOrder (B := chain3)
    (ord := fun i => i.val) chain3_hord chain3_hB
  rw [h, Fintype.card_fin]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, pow_zero, pow_one, pow_two, chain3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two];
    norm_num

/-- `cycle2 ^ 2 = 1`. -/
theorem cycle2_sq : cycle2 ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, cycle2, Matrix.cons_val_zero,
      Matrix.cons_val_one]

/-- No power of `cycle2` vanishes. -/
theorem cycle2_not_nilpotent : ∀ n, cycle2 ^ n ≠ 0 := by
  intro n
  have hsq := cycle2_sq
  have hne : cycle2 ≠ 0 := by
    intro hcon
    have h01 : cycle2 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by rw [hcon]
    simp [cycle2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h01
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul, pow_mul, hsq, one_pow]
    exact one_ne_zero
  · rw [pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]
    exact hne

/-- `cycle2` has no topological order. -/
theorem cycle2_no_topologicalOrder :
    ¬ ∃ ord : Fin 2 → ℕ, ∀ i j, cycle2 i j ≠ 0 → ord j < ord i := by
  rintro ⟨ord, h⟩
  have h01 : cycle2 0 1 ≠ 0 := by
    simp [cycle2, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h10 : cycle2 1 0 ≠ 0 := by
    simp [cycle2, Matrix.cons_val_zero, Matrix.cons_val_one]
  have g01 := h 0 1 h01
  have g10 := h 1 0 h10
  omega

/-- One-two discrepancy value. -/
theorem discrepancy_one_two :
    gaussianDiscrepancy (1 : Matrix (Fin 1) (Fin 1) ℝ) 2
      = Real.log 2 - 1 / 2 := by
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have h2 : (2 : Matrix (Fin 1) (Fin 1) ℝ) = !![2] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.ofNat_apply]
  have hdet1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).det = 1 := by
    rw [h1]
    exact Matrix.det_fin_one_of 1
  have hdet2 : (2 : Matrix (Fin 1) (Fin 1) ℝ).det = 2 := by
    rw [h2]
    exact Matrix.det_fin_one_of 2
  have htrace : ((1 : Matrix (Fin 1) (Fin 1) ℝ)
      * (2 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).trace = 1 / 2 := by
    rw [h1, h2]
    have hinv : (!![2] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
        = !![(2 : ℝ)⁻¹] := by
      rw [Matrix.inv_subsingleton]
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hinv]
    have hmul : (!![1] : Matrix (Fin 1) (Fin 1) ℝ)
        * !![(2 : ℝ)⁻¹] = !![(2 : ℝ)⁻¹] := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply]
    rw [hmul, Matrix.trace_fin_one_of]
    norm_num
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by simp
  unfold gaussianDiscrepancy
  rw [hdet2, htrace, hdet1, Real.log_one, hcard]
  ring

/-- One-two discrepancy is positive. -/
theorem discrepancy_one_two_pos :
    0 < gaussianDiscrepancy (1 : Matrix (Fin 1) (Fin 1) ℝ) 2 := by
  rw [discrepancy_one_two]
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h := Real.lt_log_one_add_of_pos h1
  norm_num at h
  linarith

/-- Singular `S` gives negative discrepancy. -/
theorem discrepancy_singular_neg :
    gaussianDiscrepancy (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 < 0 := by
  have h0 : (0 : Matrix (Fin 1) (Fin 1) ℝ) = !![0] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hdet0 : (0 : Matrix (Fin 1) (Fin 1) ℝ).det = 0 := by
    rw [h0]
    exact Matrix.det_fin_one_of 0
  have hdet1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).det = 1 := by
    rw [h1]
    exact Matrix.det_fin_one_of 1
  have htrace : ((0 : Matrix (Fin 1) (Fin 1) ℝ)
      * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).trace = 0 := by
    rw [Matrix.zero_mul, Matrix.trace_zero]
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by simp
  unfold gaussianDiscrepancy
  rw [hdet1, htrace, hdet0, Real.log_one, Real.log_zero, hcard]
  norm_num

/-- Two-one discrepancy is positive. -/
theorem discrepancy_two_one_pos :
    0 < gaussianDiscrepancy (2 : Matrix (Fin 1) (Fin 1) ℝ) 1 := by
  have h2 : (2 : Matrix (Fin 1) (Fin 1) ℝ) = !![2] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.ofNat_apply]
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![1] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hdet2 : (2 : Matrix (Fin 1) (Fin 1) ℝ).det = 2 := by
    rw [h2]
    exact Matrix.det_fin_one_of 2
  have hdet1 : (1 : Matrix (Fin 1) (Fin 1) ℝ).det = 1 := by
    rw [h1]
    exact Matrix.det_fin_one_of 1
  have htrace : ((2 : Matrix (Fin 1) (Fin 1) ℝ)
      * (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).trace = 2 := by
    have hinv1 : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
        = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      rw [h1, Matrix.inv_subsingleton]
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hinv1]
    have hmul : (2 : Matrix (Fin 1) (Fin 1) ℝ)
        * (1 : Matrix (Fin 1) (Fin 1) ℝ)
        = (2 : Matrix (Fin 1) (Fin 1) ℝ) := Matrix.mul_one _
    rw [hmul, h2, Matrix.trace_fin_one_of]
  have hcard : (Fintype.card (Fin 1) : ℝ) = 1 := by simp
  have hval : gaussianDiscrepancy (2 : Matrix (Fin 1) (Fin 1) ℝ) 1
      = 1 - Real.log 2 := by
    unfold gaussianDiscrepancy
    rw [hdet1, htrace, hdet2, Real.log_one, hcard]
    ring
  rw [hval]
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2ne : (2 : ℝ) ≠ 1 := by norm_num
  have hlt := Real.log_lt_sub_one_of_pos h2pos h2ne
  norm_num at hlt
  linarith

/-- Two-one discrepancy is nonzero. -/
theorem discrepancy_two_one_ne_zero :
    gaussianDiscrepancy (2 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ 0 :=
  ne_of_gt discrepancy_two_one_pos

/-- Identity discrepancy vanishes. -/
theorem discrepancy_identity_zero :
    gaussianDiscrepancy (1 : Matrix (Fin 3) (Fin 3) ℝ) 1 = 0 := by
  apply gaussianDiscrepancy_self
  rw [Matrix.det_one]
  exact isUnit_one

/-- `diagonal ![1]` is positive definite. -/
private theorem diag_one_pd :
    (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff, Fin.forall_fin_one]
  norm_num [Matrix.cons_val_zero]

/-- `diagonal ![2]` is positive definite. -/
private theorem diag_two_pd :
    (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  rw [Matrix.posDef_diagonal_iff, Fin.forall_fin_one]
  norm_num [Matrix.cons_val_zero]

/-- Nonnegativity on a concrete diagonal positive-definite pair. -/
theorem discrepancy_nonneg_diag :
    0 ≤ gaussianDiscrepancy (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ) :=
  gaussianDiscrepancy_nonneg diag_one_pd diag_two_pd

/-- Forward direction of the equality case on a concrete diagonal
positive-definite pair. -/
theorem discrepancy_eq_zero_iff_mp_diag :
    (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  have h1 : (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)
      = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.diagonal]
  have h0 : gaussianDiscrepancy (Matrix.diagonal ![1] : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
    rw [h1]
    apply gaussianDiscrepancy_self
    rw [Matrix.det_one]
    exact isUnit_one
  have hS : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := Matrix.PosDef.one
  exact (gaussianDiscrepancy_eq_zero_iff diag_one_pd hS).mp h0

/-- Backward direction of the equality case on a concrete diagonal
positive-definite pair. -/
theorem discrepancy_eq_zero_iff_mpr_diag :
    gaussianDiscrepancy (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ)
      (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℝ) = 0 :=
  (gaussianDiscrepancy_eq_zero_iff diag_two_pd diag_two_pd).mpr rfl

open scoped Matrix

/-- Two-time-point loading matrix: Intercept loadings `1, 1`, Slope loadings
`0, 1` (underidentified comparison case for D08.1). -/
def growthLoading2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- First covariance decomposition of the two-time-point example. -/
def twoG1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]

/-- Second covariance decomposition of the two-time-point example. -/
noncomputable def twoG2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3 / 2, -1 / 2; -1 / 2, 3 / 2]

/-- Error variances for the first two-time-point decomposition. -/
def twoTheta1 : Fin 2 → ℝ := ![1, 1]

/-- Error variances for the second two-time-point decomposition. -/
noncomputable def twoTheta2 : Fin 2 → ℝ := ![1 / 2, 1]

/-- Covariance with no symmetric nonnegative-error decomposition: the
recovery forces `θ 0 = -4 / 5`. -/
noncomputable def badInput : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 9 / 10, 0; 9 / 10, 1, 0; 0, 0, 1]

/-- The identity-covariance growth example gives
`!![2, 1, 1; 1, 3, 3; 1, 3, 6]`. -/
theorem growth_example_cov :
    ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
      + Matrix.diagonal ![1, 1, 1] :
      Matrix (Fin 3) (Fin 3) ℝ)) = !![2, 1, 1; 1, 3, 3; 1, 3, 6] := by
  rw [Matrix.one_fin_two]
  have h1 : ((!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have e := growthLoading_cov_apply _ h1 ![1, 1, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> rw [e _ _] <;> simp <;> norm_num

/-- The recovery on the identity-covariance example gives `G 0 0 = 1`,
`G 0 1 = 0`, `G 1 1 = 1`. -/
theorem growth_example_recovered :
    ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
      + Matrix.diagonal ![1, 1, 1] :
      Matrix (Fin 3) (Fin 3) ℝ)) 0 2
      - ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
        + Matrix.diagonal ![1, 1, 1] :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 1 = 0
    ∧ 2 * ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
        + Matrix.diagonal ![1, 1, 1] :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 1
      - ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
        + Matrix.diagonal ![1, 1, 1] :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 2 = 1
    ∧ ((((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
        + Matrix.diagonal ![1, 1, 1] :
        Matrix (Fin 3) (Fin 3) ℝ)) 1 2
      + ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
        + Matrix.diagonal ![1, 1, 1] :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 1
      - 2 * ((growthLoading * (1 : Matrix (Fin 2) (Fin 2) ℝ) * growthLoadingᵀ
        + Matrix.diagonal ![1, 1, 1] :
        Matrix (Fin 3) (Fin 3) ℝ)) 0 2)) / 2 = 1 := by
  rw [growth_example_cov]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> norm_num

/-- Both two-time-point decompositions give `!![2, 1; 1, 3]`. -/
theorem two_time_same_cov :
    ((growthLoading2 * twoG1 * growthLoading2ᵀ + Matrix.diagonal twoTheta1 :
      Matrix (Fin 2) (Fin 2) ℝ)) = !![2, 1; 1, 3]
    ∧ ((growthLoading2 * twoG2 * growthLoading2ᵀ + Matrix.diagonal twoTheta2 :
      Matrix (Fin 2) (Fin 2) ℝ)) = !![2, 1; 1, 3] := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rw [Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.diagonal_apply] <;> simp [growthLoading2, twoG1, twoTheta1]
      <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> rw [Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.diagonal_apply] <;> simp [growthLoading2, twoG2, twoTheta2]
      <;> ring

/-- The two two-time-point covariance parameters differ. -/
theorem two_time_params_ne : twoG1 ≠ twoG2 := by
  intro h
  have h00 : twoG1 0 0 = twoG2 0 0 := by rw [h]
  simp [twoG1, twoG2] at h00
  norm_num at h00

/-- Both two-time-point decompositions are admissible: symmetric `G` with
positive diagonal and determinant, positive `θ`. -/
theorem two_time_admissible :
    twoG1.IsSymm ∧ 0 < twoG1 0 0 ∧ 0 < twoG1 1 1 ∧ 0 < twoG1.det ∧
      twoG2.IsSymm ∧ 0 < twoG2 0 0 ∧ 0 < twoG2 1 1 ∧ 0 < twoG2.det ∧
      0 < twoTheta1 0 ∧ 0 < twoTheta1 1 ∧ 0 < twoTheta2 0 ∧
      0 < twoTheta2 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [twoG1, Matrix.transpose_apply]
  · simp [twoG1]
  · simp [twoG1]
  · simp only [twoG1, Matrix.det_fin_two_of]
    norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [twoG2, Matrix.transpose_apply]
  · simp [twoG2]
  · simp [twoG2]
  · simp only [twoG2, Matrix.det_fin_two_of]
    norm_num
  · simp [twoTheta1]
  · simp [twoTheta1]
  · simp [twoTheta2]
  · simp [twoTheta2]

/-- `badInput` is symmetric with leading principal minors `1`, `19 / 100`,
`19 / 100`. -/
theorem inadmissible_input_minors :
    badInput.IsSymm ∧ badInput 0 0 = 1 ∧
      ((!![1, 9 / 10; 9 / 10, 1] : Matrix (Fin 2) (Fin 2) ℝ)).det
        = 19 / 100 ∧
      badInput.det = 19 / 100 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [badInput, Matrix.transpose_apply]
  · simp [badInput]
  · rw [Matrix.det_fin_two_of]
    norm_num
  · rw [Matrix.det_fin_three]
    simp [badInput]
    ring

/-- `badInput` has no symmetric `G` with nonnegative `θ` giving it: the
recovery forces `θ 0 = -4 / 5`. -/
theorem inadmissible_input : ¬ ∃ (G : Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Fin 3 → ℝ),
    G.IsSymm ∧ (∀ s, 0 ≤ θ s) ∧
      ((growthLoading * G * growthLoadingᵀ + Matrix.diagonal θ :
        Matrix (Fin 3) (Fin 3) ℝ)) = badInput := by
  rintro ⟨G, θ, hG, hθ, hM⟩
  have r := growth_recover G hG θ
  obtain ⟨g01, g00, g11, t0, t1, t2⟩ := r
  rw [hM] at g01 g00 t0
  simp [badInput] at g01 g00 t0
  have hneg : θ 0 = -(4 / 5) := by linarith
  have hpos := hθ 0
  linarith

end MathlibExt.Probability.Statistics.Measurement.Test

end
