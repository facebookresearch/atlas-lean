/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.FittedProjection
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

open Matrix WithLp
open MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExtTest.Probability.Statistics.LinearModel.FittedProjection

private def duplicateCols : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 0]

private theorem duplicateCols_apply (β : EuclideanSpace ℝ (Fin 2)) :
    duplicateCols.toEuclideanLin β = toLp 2 ![β 0 + β 1, 0] := by
  ext i
  fin_cases i <;> simp [duplicateCols, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]

-- Two distinct minimizers fit (3, 0) to the response (3, 4), leaving a nonzero residual.
example :
    let A := duplicateCols.toEuclideanLin
    let y : EuclideanSpace ℝ (Fin 2) := toLp 2 ![3, 4]
    let β₁ : EuclideanSpace ℝ (Fin 2) := toLp 2 ![3, 0]
    let β₂ : EuclideanSpace ℝ (Fin 2) := toLp 2 ![0, 3]
    β₁ ≠ β₂ ∧ (∀ γ, ‖y - A β₁‖ ≤ ‖y - A γ‖) ∧
      (∀ γ, ‖y - A β₂‖ ≤ ‖y - A γ‖) ∧ A β₁ = toLp 2 ![3, 0] := by
  intro A y β₁ β₂
  have h₁ : A β₁ = toLp 2 ![3, 0] := by
    change duplicateCols.toEuclideanLin β₁ = _
    rw [duplicateCols_apply]
    norm_num [β₁]
  have h₂ : A β₂ = toLp 2 ![3, 0] := by
    change duplicateCols.toEuclideanLin β₂ = _
    rw [duplicateCols_apply]
    norm_num [β₂]
  have hproj : A.range.starProjection y = toLp 2 ![3, 0] := by
    apply A.range.eq_starProjection_of_mem_of_inner_eq_zero ⟨β₁, h₁⟩
    rintro w ⟨γ, rfl⟩
    change inner ℝ (y - toLp 2 ![3, 0]) (duplicateCols.toEuclideanLin γ) = 0
    rw [duplicateCols_apply, PiLp.inner_apply, Fin.sum_univ_two]
    norm_num [y]
  have h := (least_squares_fitted_projection duplicateCols y).1
  refine ⟨?_, (h β₁).mpr (h₁.trans hproj.symm), (h β₂).mpr (h₂.trans hproj.symm), h₁⟩
  intro heq
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) heq
  norm_num [β₁, β₂] at h0

-- A full-rank design has a unique coefficient minimizer for every response.
example (y : EuclideanSpace ℝ (Fin 2)) :
    ∃! β : EuclideanSpace ℝ (Fin 2),
      ∀ γ, ‖y - (1 : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin β‖ ≤
        ‖y - (1 : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin γ‖ :=
  (least_squares_fitted_projection (1 : Matrix (Fin 2) (Fin 2) ℝ) y).2.2.mpr Matrix.rank_one

end MathlibExtTest.Probability.Statistics.LinearModel.FittedProjection
