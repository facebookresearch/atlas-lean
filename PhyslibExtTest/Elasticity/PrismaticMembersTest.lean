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

end PhyslibExtTest.Elasticity.PrismaticMembers

end
