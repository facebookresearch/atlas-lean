/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Bootstrapping discount factors from a triangular cash-flow matrix

Bonds sorted by maturity give a lower-triangular cash-flow matrix `C`: bond
`i` pays only at dates `≤ i`. With a nonzero payment at each bond's own
maturity (nonzero diagonal), `det C = ∏ diag ≠ 0`, so `C` is invertible and
`C.mulVec D` is injective: observed prices determine the discount factors uniquely.

## Main results

* `MathlibExt.Economics.Finance.bootstrap_discountFactors_unique`: uniqueness
  of discount factors (`Matrix.det_of_isLowerTriangular`,
  `Matrix.isUnit_iff_isUnit_det`, `Matrix.mulVec_injective_iff_isUnit`).

Positivity of the discount factors is NOT implied: the theorem is uniqueness
only, for arbitrary prices.

## References

SOA Exam FM syllabus (bootstrapping spot rates). Atlas roadmap target FI03.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Bootstrapping uniqueness: a lower-triangular cash-flow matrix with nonzero
diagonal determines the discount factors uniquely from observed prices
(Atlas roadmap FI03.T03). No positivity is claimed. -/
theorem bootstrap_discountFactors_unique {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    {D₁ D₂ : Fin n → ℝ} (hC : C.IsLowerTriangular) (hdiag : ∀ i, C i i ≠ 0)
    (h : C.mulVec D₁ = C.mulVec D₂) : D₁ = D₂ := by
  have hdet : C.det = ∏ i, C i i := Matrix.det_of_isLowerTriangular C hC
  have hprod : (∏ i, C i i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro a _
    exact hdiag a
  have hdet_ne : C.det ≠ 0 := by
    rw [hdet]
    exact hprod
  have hunit_det : IsUnit C.det := isUnit_iff_ne_zero.mpr hdet_ne
  have hunit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr hunit_det
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  exact hinj h

end MathlibExt.Economics.Finance
