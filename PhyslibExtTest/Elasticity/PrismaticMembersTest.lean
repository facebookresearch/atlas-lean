/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Elasticity.PrismaticMembers

/-!
# Tests for `PhyslibExt.Elasticity.PrismaticMembers`

* a nonzero uniform axial load with exact endpoint values;
* the uniform-load displacement as a fixed-fixed solution at concrete data;
* a fixed-free displacement at concrete data, which is not a fixed-fixed solution.
-/

@[expose] public section

namespace PhyslibExtTest.Elasticity.PrismaticMembers

open _root_.Elasticity.PrismaticMembers

/-! ## A. Uniform axial load -/

-- Nonzero uniform axial load `q = 4`, `EA = 2`, `L = 2`: the displacement is `x * (2 - x)`,
-- exactly `0` at both ends and `1` at midspan.
example :
    axialDisplacement 2 2 4 0 = 0 ∧ axialDisplacement 2 2 4 2 = 0 ∧
      axialDisplacement 2 2 4 1 = 1 := by
  unfold axialDisplacement
  norm_num

-- The same data give a solution of the fixed-fixed bar problem.
example : IsFixedFixedSolution 2 2 (fun _ => 4) (axialDisplacement 2 2 4) :=
  isFixedFixedSolution_axialDisplacement (by norm_num) (by norm_num) 4

/-! ## B. Traction-free end -/

-- With the right end traction-free instead of fixed, the displacement `4 * x * (4 - x) / 4`
-- is not a fixed-fixed solution.
example : ¬ IsFixedFixedSolution 2 2 (fun _ => 4) (fixedFreeDisplacement 2 2 4) :=
  (fixedFreeDisplacement_not_isFixedFixedSolution (by norm_num) (by norm_num)
    (by norm_num)).2.2.2

/-! ## C. Clamped-free cantilever -/

-- Tip-force fixture `EI = 2`, `L = 3`, `q = 0`, `P = 4`: tip deflection
-- `P * L ^ 3 / (3 * EI) = 18`.
example : cantileverDeflection 2 3 0 4 3 = 18 := by
  unfold cantileverDeflection
  norm_num

-- Nonzero-load fixture `EI = 2`, `L = 3`, `q = 4`, `P = 5`: all four boundary conditions and
-- the equation hold, and the tip deflection is `q * L ^ 4 / (8 * EI) + P * L ^ 3 / (3 * EI)`
-- `= 81 / 4 + 45 / 2 = 171 / 4`.
example :
    cantileverDeflection 2 3 4 5 0 = 0 ∧ deriv (cantileverDeflection 2 3 4 5) 0 = 0 ∧
      2 * iteratedDeriv 2 (cantileverDeflection 2 3 4 5) 3 = 0 ∧
      -(2 * iteratedDeriv 3 (cantileverDeflection 2 3 4 5) 3) = 5 ∧
      (∀ x : ℝ, 2 * iteratedDeriv 4 (cantileverDeflection 2 3 4 5) x = 4) ∧
      cantileverDeflection 2 3 4 5 3 = 171 / 4 := by
  refine ⟨cantileverDeflection_zero 2 3 4 5, deriv_cantileverDeflection_zero 2 3 4 5,
    cantileverDeflection_moment_right 2 3 4 5,
    cantileverDeflection_shear_right (by norm_num) 3 4 5,
    fun x => cantileverDeflection_iteratedDeriv_four (by norm_num) 3 4 5 x, ?_⟩
  unfold cantileverDeflection
  norm_num

end PhyslibExtTest.Elasticity.PrismaticMembers

end
