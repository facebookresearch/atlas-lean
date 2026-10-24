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
# Tests for the Green's operator's square root squared

* A constant-coefficient diagonal operator on `ℓ²(ℕ, ℝ)` acts on the
  first basis vector by scalar multiplication, and squaring it squares the
  coefficient.
* The Green's coefficient identity at `k = 1` and `k = 2`.
* The Green's square-root squaring identity applied to an abstract sine
  Hilbert basis of `L²([0, 1])`.
-/

open MeasureTheory
open scoped lp
open MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
open MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared

namespace MathlibExtTest.Analysis.ODE.GreensOperatorSqrtSquaredTests

/-- A constant diagonal operator on `ℓ²(ℕ, ℝ)` scales the first basis vector. -/
example : diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
    ((default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0) =
    (2 : ℝ) • (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) 0 :=
  diagonalOperator_apply_basis 0

/-- Squaring a constant diagonal operator on `ℓ²(ℕ, ℝ)` squares its coefficient. -/
example (x : ℓ²(ℕ, ℝ)) :
    diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ))
        (diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ)) x) =
      diagonalOperator (default : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ)) (fun _ => (2 : ℝ) ^ 2) x :=
  diagonalOperator_sq (C := (2 : ℝ)) (fun _ => by norm_num) x

/-- The first Green's square-root coefficient squares to the first Green's eigenvalue. -/
example : ((1 : ℝ) / Real.pi) ^ 2 = 1 / Real.pi ^ 2 := by
  rw [div_pow, one_pow]

/-- The second Green's square-root coefficient squares to the second Green's eigenvalue. -/
example : ((1 : ℝ) / ((2 : ℝ) * Real.pi)) ^ 2 = 1 / (4 * Real.pi ^ 2) := by
  field_simp [Real.pi_ne_zero]
  ring

/-- The Green's square-root squaring identity, for an abstract sine Hilbert basis. -/
example (b : HilbertBasis ℕ+ ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    diagonalOperator b (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) * Real.pi))
        (diagonalOperator b (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) * Real.pi)) f) =
      diagonalOperator b (fun k : ℕ+ => (1 : ℝ) / ((k : ℝ) ^ 2 * Real.pi ^ 2)) f :=
  greensOperatorSqrt_sq b f

end MathlibExtTest.Analysis.ODE.GreensOperatorSqrtSquaredTests
