/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.CovarianceBridge

@[expose] public section

open Matrix MathlibExt.Probability.Statistics.PCA MathlibExt.Biology.Omics.CovarianceBridge

namespace MathlibExtTest.Biology.Omics.CovarianceBridge

/-! ### Smoke test: the reused PCA API -/

/-- Three samples of two features on the affine line `x₀ = 1`: `(1, 0), (1, 1), (1, 2)`. -/
def X : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]

example : colMean X 0 = 1 ∧ colMean X 1 = 1 := by
  simp [colMean, X, Fin.sum_univ_three]; norm_num

example : sampleCov X 0 0 = 0 ∧ sampleCov X 1 1 = 1 ∧ sampleCov X 0 1 = 0 := by
  simp only [sampleCov_apply, colMean, X, Fin.sum_univ_three]
  norm_num

/-! ### `secondMoment` and the bridge -/

/-- The uncentered second moment of `X` is `3⁻¹ !![3, 3; 3, 5]`. -/
example : secondMoment X = !![1, 1; 1, 5 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondMoment, X, mul_apply, Fin.sum_univ_three] <;> norm_num

/-- Bessel's correction instantiated at `n = 3`: `S = (3/2) • (n⁻¹ Xᵀ X - x̄ x̄ᵀ)`. -/
example : sampleCov X = ((3 : ℝ) / 2) • (secondMoment X - vecMulVec (colMean X) (colMean X)) := by
  rw [sampleCov_eq_secondMoment X (by norm_num)]
  norm_num

/-- **Singular covariance, nonsingular second moment.** The samples lie on the affine line
`x₀ = 1`, which misses the origin: `det S = 0` while `det (n⁻¹ Xᵀ X) = 2/3`. -/
example : (sampleCov X).det = 0 ∧ (secondMoment X).det = 2 / 3 := by
  refine ⟨(det_sampleCov_eq_zero_iff X).mpr ⟨![1, 0], by simp, 1, ?_⟩, ?_⟩
  · ext i
    fin_cases i <;> simp [X, mulVec, dotProduct, Fin.sum_univ_two]
  · rw [det_fin_two]
    simp [secondMoment, X, mul_apply, Fin.sum_univ_three]
    norm_num

/-- The null direction of `S` is `w = (1, 0)`, along which every sample projects to `1`. -/
example : sampleCov X *ᵥ ![1, 0] = 0 := by
  rw [sampleCov_mulVec_eq_zero_iff X]
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [X, mulVec, dotProduct, Fin.sum_univ_two]

/-! ### Location invariance: `S` forgets a common shift, the second moment does not -/

example : sampleCov (X + vecMulVec (fun _ => 1) ![1, 0]) = sampleCov X :=
  sampleCov_add_vecMulVec_one X _

example : secondMoment (X + vecMulVec (fun _ => 1) ![1, 0]) 0 0 = 4 ∧ secondMoment X 0 0 = 1 := by
  have hX : X + vecMulVec (fun _ => 1) ![1, 0] = !![2, 0; 2, 1; 2, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X] <;> norm_num
  rw [hX]
  simp [secondMoment, X, mul_apply, Fin.sum_univ_three]
  norm_num

/-! ### Rank drop: identical samples -/

/-- Three identical samples `(1, 2)`: the data have rank `1`, the centered covariance is `0`. -/
def Y : Matrix (Fin 3) (Fin 2) ℝ := vecMulVec (fun _ => 1) ![1, 2]

example : sampleCov Y = 0 := by
  have h := sampleCov_add_vecMulVec_one (0 : Matrix (Fin 3) (Fin 2) ℝ) ![1, 2]
  rw [zero_add] at h
  rw [Y, h]
  ext j k
  simp [sampleCov_apply, colMean]

example : secondMoment Y 0 0 = 1 := by
  simp [secondMoment, Y, mul_apply]

/-- Centering `Y` gives the zero matrix. -/
theorem center_Y : center Y = 0 := by
  have h := center_add_vecMulVec_one (0 : Matrix (Fin 3) (Fin 2) ℝ) ![1, 2]
  rw [zero_add] at h
  rw [Y, h]
  ext i j
  simp [center, colMean]

/-- **The rank drop is attained.** `rank (Y - 𝟙 ȳᵀ) = 0` and `rank Y = 1`, so
`rank Y ≤ rank (Y - 𝟙 ȳᵀ) + 1` holds with equality. -/
example : (center Y).rank = 0 ∧ Y.rank = 1 ∧ Y.rank = (center Y).rank + 1 := by
  have hc : (center Y).rank = 0 := by rw [center_Y, rank_zero]
  have hle : Y.rank ≤ 1 := by simpa [hc] using rank_le_rank_center_add_one Y
  have hpos : 0 < Y.rank := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    unfold Matrix.rank at h
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    have := congrFun (LinearMap.congr_fun h (Pi.single 0 1)) 0
    simp [Y, mulVec, dotProduct] at this
  refine ⟨hc, by omega, by omega⟩

/-- The general bound `rank (Y - 𝟙 ȳᵀ) ≤ n - 1 = 2`. -/
example : (center Y).rank ≤ 2 := rank_center_le Y

/-! ### High-dimensional boundary: `n ≤ p` -/

example (Z : Matrix (Fin 2) (Fin 5) ℝ) : (sampleCov Z).det = 0 :=
  det_sampleCov_eq_zero_of_le Z (by norm_num) (by norm_num)

/-! ### A positive definite case -/

/-- Four samples `(1, 0), (-1, 0), (0, 2), (0, -2)` lie in no affine line, so `S` is positive
definite. -/
def W : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; -1, 0; 0, 2; 0, -2]

example : (sampleCov W).PosDef := by
  rw [posDef_sampleCov_iff W]
  intro w hw c h
  apply hw
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [W, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1 h2 h3
  ext i
  fin_cases i <;> simp <;> linarith

/-! ### Confounded batch design -/

/-- Two batches of two samples each; the condition indicator equals the batch indicator. -/
def b : Fin 4 → ℝ := ![0, 0, 1, 1]

/-- "All batch" and "all biology" explanations give the same data, hence the same covariance. -/
example (E : Matrix (Fin 4) (Fin 1) ℝ) (μ : Fin 1 → ℝ) :
    sampleCov (batchModel E μ b b ![1] 0) = sampleCov (batchModel E 0 b b 0 ![1]) :=
  sampleCov_batchModel_eq_of_add_eq E μ 0 b (by simp)

/-- The combined effect is visible: the noiseless covariance is `var(b) = 1/3`, not `0`. -/
example : sampleCov (batchModel 0 0 b b ![1] 0) 0 0 = 1 / 3 := by
  rw [sampleCov_batchModel_confounded_noiseless]
  simp [b, Fin.sum_univ_four]
  norm_num

/-- The noiseless confounded covariance has rank at most one. -/
example : (sampleCov (batchModel 0 0 b b ![1] 0)).rank ≤ 1 :=
  rank_sampleCov_batchModel_confounded_noiseless_le 0 b _ _

/-- No estimator of the batch effect (or of the signal) from `S` exists. -/
example (E : Matrix (Fin 4) (Fin 1) ℝ) (μ : Fin 1 → ℝ) :
    (¬ ∃ f : Matrix (Fin 1) (Fin 1) ℝ → Fin 1 → ℝ,
      ∀ β δ, f (sampleCov (batchModel E μ b b β δ)) = β) ∧
    (¬ ∃ f : Matrix (Fin 1) (Fin 1) ℝ → Fin 1 → ℝ,
      ∀ β δ, f (sampleCov (batchModel E μ b b β δ)) = δ) :=
  ⟨not_exists_batch_estimator (by norm_num) E μ b,
    not_exists_signal_estimator (by norm_num) E μ b⟩

/-- With a single sample `S = 0`, and the null-direction criterion still holds. -/
example (Z : Matrix (Fin 1) (Fin 2) ℝ) (w : Fin 2 → ℝ) :
    sampleCov Z = 0 ∧ ∃ c : ℝ, Z *ᵥ w = fun _ => c :=
  ⟨sampleCov_eq_zero_of_le_one Z le_rfl,
    (sampleCov_mulVec_eq_zero_iff Z w).mp (by simp [sampleCov_eq_zero_of_le_one Z le_rfl])⟩

/-- `S(-X) = S(X)`. -/
example : sampleCov (-X) = sampleCov X := sampleCov_neg X

end MathlibExtTest.Biology.Omics.CovarianceBridge
