/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared
import MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the bounded Green square-root identity

Retain the original bounded constant-map and coefficient checks. Exercise the
actual canonical sine basis and the supplied Green operator under its exact
kernel/self-adjoint hypotheses. Continuous-map operations and an unbounded
coefficient rejection check the repaired diagonal constructor's contract.
-/

open MeasureTheory
open scoped lp
open MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
open MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared
open MathlibExt.Analysis.ODE.GreensOperator

namespace MathlibExtTest.Analysis.ODE.GreensOperatorSqrtSquaredTests

private lemma twoCoeff_bound (_i : ℕ) : ‖(2 : ℝ)‖ ≤ 2 := by norm_num

/-- A bounded constant diagonal map scales the first basis vector. -/
example : diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
    twoCoeff_bound ((default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0) =
    (2 : ℝ) • (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0 :=
  diagonalOperator_apply_basis twoCoeff_bound 0

/-- Squaring a bounded constant diagonal map squares its coefficient. -/
example (x : ℓ²(ℕ, ℝ)) :
    diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
        twoCoeff_bound
        (diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
          twoCoeff_bound x) =
      diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ) ^ 2)
        (C := (2 : ℝ) ^ 2) (fun _ => by norm_num) x :=
  diagonalOperator_sq twoCoeff_bound x

/-- The first Green square-root coefficient squares to its eigenvalue. -/
example : ((1 : ℝ) / Real.pi) ^ 2 = 1 / Real.pi ^ 2 := by
  rw [div_pow, one_pow]

/-- The second Green square-root coefficient squares to its eigenvalue. -/
example : ((1 : ℝ) / ((2 : ℝ) * Real.pi)) ^ 2 = 1 / (4 * Real.pi ^ 2) := by
  field_simp [Real.pi_ne_zero]
  ring

/-- The canonical sine-basis square root squares to the actual supplied Green map. -/
example (A : Module.End ℝ L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t))
    (f : L2UnitInterval) :
    greensOperatorSqrt sineHilbertBasis sineHilbertBasis_coe
        (greensOperatorSqrt sineHilbertBasis sineHilbertBasis_coe f) = A f :=
  greensOperatorSqrt_sq A sineHilbertBasis hA_sa sineHilbertBasis_coe hA_greens f

private lemma greenCoeff_bound (k : ℕ+) : ‖greensEigenvalueSqrt k‖ ≤ 1 / Real.pi := by
  unfold greensEigenvalueSqrt
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hk1, hpi])

/-- Genuine canonical sine modes are eigenvectors of the square root. -/
example (k : ℕ+) :
    greensOperatorSqrt sineHilbertBasis sineHilbertBasis_coe (sineHilbertBasis k) =
      greensEigenvalueSqrt k • sineHilbertBasis k := by
  rw [greensOperatorSqrt_eq_diagonal sineHilbertBasis sineHilbertBasis_coe greenCoeff_bound]
  exact diagonalOperator_apply_basis greenCoeff_bound k

/-- The repaired constructor exposes actual continuity. -/
example : Continuous
    (diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
      twoCoeff_bound) :=
  (diagonalOperator _ _ twoCoeff_bound).continuous

/-- The repaired constructor exposes actual linearity. -/
example (x y : ℓ²(ℕ, ℝ)) :
    diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
        twoCoeff_bound (x + y) =
      diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
          twoCoeff_bound x +
        diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
          twoCoeff_bound y :=
  (diagonalOperator _ _ twoCoeff_bound).map_add x y

/-- The review's unbounded coefficient family cannot satisfy the constructor's bound. -/
example : ¬ ∃ C : ℝ, ∀ n : ℕ, ‖(n : ℝ) + 1‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  linarith

end MathlibExtTest.Analysis.ODE.GreensOperatorSqrtSquaredTests
