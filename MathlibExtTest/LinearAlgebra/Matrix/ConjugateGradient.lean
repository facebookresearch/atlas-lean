/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.ConjugateGradient
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

open Matrix MathlibExt.LinearAlgebra.Matrix.ConjugateGradient

namespace MathlibExtTest.LinearAlgebra.Matrix.ConjugateGradient

/-! ### Concrete runs -/

/-- For `A = I` the energy norm is the Euclidean norm: `‖(3, 4)‖_I = 5`. -/
example : energyNorm (1 : Matrix (Fin 2) (Fin 2) ℝ) ![3, 4] = 5 := by
  rw [energyNorm, one_mulVec]
  simp [dotProduct, Fin.sum_univ_two]
  rw [show (3 : ℝ) * 3 + 4 * 4 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- For `A = I`, one CG step from `x₀ = 0` solves `x = b` exactly (`α₀ = 1`). -/
example : (iterate (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2] 0 1).x = ![1, 2] := by
  simp [iterate, init, step, dotProduct, Fin.sum_univ_two]
  norm_num

/-- Boundary: with a zero residual (`b = 0`, `x₀ = 0`) every step keeps `x = 0`; the step sizes
are the junk quotients `0 / 0 = 0`. -/
example (k : ℕ) : (iterate (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 k).x = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate, Function.iterate_succ_apply']
    have hs : (step (1 : Matrix (Fin 2) (Fin 2) ℝ))^[k] (init 1 0 0) =
        iterate (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 k := rfl
    have hr : ∀ k, (iterate (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 k).r = 0 ∧
        (iterate (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 k).d = 0 := by
      intro k
      induction k with
      | zero => simp [iterate, init]
      | succ k ihk =>
        rw [iterate, Function.iterate_succ_apply']
        change (step 1 (iterate 1 0 0 k)).r = 0 ∧ (step 1 (iterate 1 0 0 k)).d = 0
        simp [step, ihk.1, ihk.2]
    rw [hs]
    simp [step, ih, (hr k).1, (hr k).2]

/-- The starting residual spans the first Krylov space. -/
example (A : Matrix (Fin 2) (Fin 2) ℝ) (r : Fin 2 → ℝ) : r ∈ krylov A r 1 :=
  Submodule.subset_span ⟨0, by simp⟩

/-! ### The theorems apply to a positive definite matrix -/

example (b x₀ : Fin 2 → ℝ) (k : ℕ) {z : Fin 2 → ℝ}
    (hz : z ∈ krylov (1 : Matrix (Fin 2) (Fin 2) ℝ) (b - (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x₀) k) :
    energyNorm 1 ((iterate 1 b x₀ k).x - b) ≤ energyNorm 1 (x₀ + z - b) :=
  energyNorm_iterate_le PosDef.one (one_mulVec b) x₀ k hz

example (b x₀ : Fin 2 → ℝ) (k : ℕ) :
    energyNorm 1 ((iterate 1 b x₀ k).x - b) ≤
      2 * ((√(condNum (PosDef.one (n := Fin 2) (R := ℝ))) - 1) /
        (√(condNum (PosDef.one (n := Fin 2) (R := ℝ))) + 1)) ^ k * energyNorm 1 (x₀ - b) :=
  energyNorm_iterate_sub_le_condNum (by norm_num) PosDef.one (one_mulVec b) x₀ k

end MathlibExtTest.LinearAlgebra.Matrix.ConjugateGradient
