/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.HurwitzBranchModels
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.TrivSqZeroExt.Basic

open CategoryTheory
open MathlibExt.Algebra.Homology.PerfectTorsionDeterminants
open scoped Polynomial

namespace HurwitzBranchOriginsTest
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Dual := TrivSqZeroExt ℚ ℚ
def epsilon : Dual := TrivSqZeroExt.inr 1
def branchEquation : Polynomial Dual := Polynomial.X - Polynomial.C epsilon

-- The Cartier equation is a nonzero divisor even over this genuinely nonreduced base.
example : branchEquation ∈ nonZeroDivisors (Polynomial Dual) :=
  (Polynomial.monic_X_sub_C epsilon).mem_nonZeroDivisors

-- Total quotients keep the infinitesimal coefficient rather than reducing it away.
example : algebraMap Dual (TotalQuotient Dual) epsilon ≠ 0 := by
  intro h
  have inj := IsLocalization.injective (TotalQuotient Dual)
    (show nonZeroDivisors Dual ≤ nonZeroDivisors Dual from le_rfl)
  have he : epsilon = 0 := inj (by simpa using h)
  have hs := congrArg TrivSqZeroExt.snd he
  norm_num [epsilon] at hs

-- The first-order branch equation differs from the equation of its reduced geometric point.
example : Ideal.span ({branchEquation} : Set (Polynomial Dual)) ≠
    Ideal.span ({Polynomial.X} : Set (Polynomial Dual)) := by
  intro h
  have mem : branchEquation ∈ Ideal.span ({Polynomial.X} : Set (Polynomial Dual)) := by
    rw [← h]
    exact Ideal.subset_span (by simp)
  have hker : Ideal.span ({Polynomial.X} : Set (Polynomial Dual)) ≤
      RingHom.ker (Polynomial.evalRingHom (0 : Dual)) := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp
  have hz := hker mem
  change Polynomial.eval 0 branchEquation = 0 at hz
  simp [branchEquation] at hz
  have hs := congrArg TrivSqZeroExt.snd hz
  norm_num [epsilon] at hs

end
end HurwitzBranchOriginsTest
