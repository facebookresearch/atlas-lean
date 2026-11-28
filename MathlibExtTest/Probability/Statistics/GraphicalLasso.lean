/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GraphicalLasso

@[expose] public section

open Matrix
open MathlibExt.Probability.Statistics.GraphicalLasso

namespace MathlibExtTest.Probability.Statistics.GraphicalLasso

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a diagonal `S = diag d` with `d ≥ 0` (singular when some `dᵢ = 0`) and `ρ > 0`, the
graphical lasso estimate is `diag ((dᵢ + ρ)⁻¹)`: `Γ = 1` satisfies the optimality conditions. -/
theorem isGraphicalLassoEstimate_diagonal {ρ : ℝ} (hρ : 0 < ρ) {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) :
    IsGraphicalLassoEstimate (of fun _ _ => ρ) (diagonal d) (diagonal fun i => (d i + ρ)⁻¹) := by
  have hpos : ∀ i, 0 < d i + ρ := fun i => by linarith [hd i]
  have hΘ : (diagonal fun i => (d i + ρ)⁻¹).PosDef :=
    posDef_diagonal_iff.2 fun i => inv_pos.2 (hpos i)
  have hinv : (diagonal fun i => (d i + ρ)⁻¹)⁻¹ = diagonal fun i => d i + ρ := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext fun i => mul_inv_cancel₀ (hpos i).ne')
  rw [isGraphicalLassoEstimate_const_iff hρ.le (isSymm_diagonal d) hΘ, hinv]
  refine ⟨1, fun i j h => ?_, fun i j _ => ?_, ?_⟩
  · by_cases hij : i = j
    · subst hij
      simp [Real.sign_of_pos (inv_pos.2 (hpos i))]
    · exact absurd (diagonal_apply_ne _ hij) h
  · rw [Matrix.one_apply]
    split_ifs <;> norm_num
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

/-- Every graphical lasso estimate of a diagonal `S ≥ 0` is that diagonal matrix
(uniqueness). -/
example {ρ : ℝ} (hρ : 0 < ρ) {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) {Θ : Matrix ι ι ℝ}
    (h : IsGraphicalLassoEstimate (of fun _ _ => ρ) (diagonal d) Θ) :
    Θ = diagonal fun i => (d i + ρ)⁻¹ :=
  (existsUnique_isGraphicalLassoEstimate_const hρ (posSemidef_diagonal_iff.2 hd)).unique h
    (isGraphicalLassoEstimate_diagonal hρ hd)

/-- For `S = 0` the estimate has `(Θ⁻¹)ᵢᵢ = ρ`. -/
example {ρ : ℝ} {Θ : Matrix ι ι ℝ} (h : IsGraphicalLassoEstimate (of fun _ _ => ρ) 0 Θ)
    (i : ι) : Θ⁻¹ i i = ρ := by
  simpa using h.inv_apply_self_const i

/-- A weak correlation is thresholded to zero: for `S = [[1, 1/2], [1/2, 1]]` and `ρ = 1` the
estimate is `I / 2`, with `Γ₀₁ = -1/2`. -/
example : IsGraphicalLassoEstimate (of fun _ _ => (1 : ℝ)) !![1, 1 / 2; 1 / 2, 1]
    ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hΘ : ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef :=
    PosDef.one.smul (by norm_num)
  have hinv : ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = (2 : ℝ) • 1 := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.one_mul]
    norm_num
  have hS : (!![1, 1 / 2; 1 / 2, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsSymm :=
    IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
  rw [isGraphicalLassoEstimate_const_iff zero_le_one hS hΘ, hinv]
  refine ⟨!![1, -1 / 2; -1 / 2, 1], fun i j => ?_, fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [Real.sign_of_pos]
  · fin_cases i <;> fin_cases j <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num

/-- A strong correlation survives, shrunk: for `S = [[1, 1/2], [1/2, 1]]` and `ρ = 1/4` the
estimate is `Θ = [[5/6, -1/6], [-1/6, 5/6]]`, with `W = Θ⁻¹ = [[5/4, 1/4], [1/4, 5/4]]` and
`Γ₀₁ = sign Θ₀₁ = -1`. -/
example : IsGraphicalLassoEstimate (of fun _ _ => (1 / 4 : ℝ)) !![1, 1 / 2; 1 / 2, 1]
    !![5 / 6, -1 / 6; -1 / 6, 5 / 6] := by
  have hΘ : (!![5 / 6, -1 / 6; -1 / 6, 5 / 6] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        simp only [not_or, not_not] at h
        exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
      simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, of_apply, cons_val',
        cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      rcases hx' with h | h
      · have := pow_pos (abs_pos.2 h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1), sq_abs (x 0)]
      · have := pow_pos (abs_pos.2 h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0), sq_abs (x 1)]
  have hinv : (!![5 / 6, -1 / 6; -1 / 6, 5 / 6] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      !![5 / 4, 1 / 4; 1 / 4, 5 / 4] := by
    refine inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hS : (!![1, 1 / 2; 1 / 2, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsSymm :=
    IsSymm.ext fun i j => by fin_cases i <;> fin_cases j <;> rfl
  rw [isGraphicalLassoEstimate_const_iff (by norm_num) hS hΘ, hinv]
  refine ⟨!![1, -1; -1, 1], fun i j => ?_, fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [Real.sign_of_pos, Real.sign_of_neg]
  · fin_cases i <;> fin_cases j <;> norm_num
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num

/-- With the diagonal left out of the penalty, `(Θ⁻¹)ᵢᵢ = Sᵢᵢ` at the estimate. -/
example {ρ : ℝ} {S Θ : Matrix ι ι ℝ}
    (h : IsGraphicalLassoEstimate (of fun i j => if i = j then 0 else ρ) S Θ) (i : ι) :
    Θ⁻¹ i i = S i i := by
  simpa using h.inv_apply_self i

/-- Non-vacuity of the weighted existence theorem: unequal positive penalties. -/
example {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef) :
    ∃! Θ, IsGraphicalLassoEstimate !![1, 2; 2, 3] S Θ :=
  existsUnique_isGraphicalLassoEstimate (fun i j => by fin_cases i <;> fin_cases j <;> norm_num)
    (fun i => by fin_cases i <;> norm_num) hS

end MathlibExtTest.Probability.Statistics.GraphicalLasso
