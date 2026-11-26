/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.LinearAlgebra.Pi
import MathlibExt.Analysis.FunctionalAnalysis.PointwiseDual

-- An infinite product with a functional that uses two of its coordinates.
example : ∃ (n : ℕ) (t : Fin n → ℕ) (a : Fin n → ℝ), ∀ x : ℕ → ℝ,
    2 * x 3 - 5 * x 7 = ∑ i, a i * x (t i) := by
  let f : (ℕ → ℝ) →ₗ[ℝ] ℝ := (2 : ℝ) • LinearMap.proj 3 - (5 : ℝ) • LinearMap.proj 7
  have h3 : Continuous (fun x : ℕ → ℝ => 2 * x 3) := (continuous_apply 3).const_mul 2
  have h7 : Continuous (fun x : ℕ → ℝ => 5 * x 7) := (continuous_apply 7).const_mul 5
  have hf : Continuous f := by
    have heq : (fun x : ℕ → ℝ => f x) = (fun x => 2 * x 3 - 5 * x 7) := by
      funext x
      simp [f, smul_eq_mul]
    change Continuous (fun x : ℕ → ℝ => f x)
    rw [heq]
    exact h3.sub h7
  simpa [f, smul_eq_mul] using f.exists_fin_sum_mul_apply_of_continuous ℕ hf
