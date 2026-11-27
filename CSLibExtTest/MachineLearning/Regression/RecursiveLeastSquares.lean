/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Regression.RecursiveLeastSquares

@[expose] public section

open Matrix MathlibExt.Analysis.Control.RecursiveLeastSquares Cslib.MachineLearning.LeastSquares
  Cslib.MachineLearning.RecursiveLeastSquares

namespace CSLibExtTest.MachineLearning.Regression.RecursiveLeastSquares

/-- The design matrix of a constant scalar regressor has `Xᵀ X = t`. -/
example (t : ℕ) :
    (designMatrix (fun _ _ => (1 : ℝ)) t)ᵀ * designMatrix (fun _ _ => (1 : ℝ)) t =
      (t : ℝ) • vecMulVec (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
  rw [designMatrix_transpose_mul]
  simp [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]

/-- Non-vacuity: with `λ = 1` the RLS estimate started at `θ_0 = 0`, `P_0 = I` minimises the ridge
objective of the data seen so far, for every `t`. -/
example (φ : ℕ → Fin 2 → ℝ) (y : ℕ → ℝ) (t : ℕ) (θ : Fin 2 → ℝ) :
    ridge (designMatrix φ t) (fun k : Fin t => y (k + 1)) 1
        (rls φ y 0 ((1 : ℝ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t).1 ≤
      ridge (designMatrix φ t) (fun k : Fin t => y (k + 1)) 1 θ :=
  ridge_le_rls_fst φ y one_pos t θ

end CSLibExtTest.MachineLearning.Regression.RecursiveLeastSquares
