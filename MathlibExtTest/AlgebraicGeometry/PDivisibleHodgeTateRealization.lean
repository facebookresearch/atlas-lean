/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PDivisibleHodgeTateRealization

/-!
# Checks for `p`-adic completeness of the valuation ring

The prime `p` lies in the Jacobson radical of `O_C`, and `O_C` is
`p`-adically separated in ideal-membership form.
-/

@[expose] public section

namespace MathlibExtTest.AlgebraicGeometry.PDivisibleHodgeTateRealization

open WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization
open MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests

/-- The prime `p` lies in the Jacobson radical of `O_C`. -/
example (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    Ideal.span {(p : integers p C)} ≤ Ring.jacobson (integers p C) := by
  have hC := integers_adic_complete p C
  exact IsAdicComplete.le_jacobson _

/-- `O_C` is `p`-adically separated in ideal-membership form. -/
example (p : ℕ) [Fact p.Prime] (C : FieldTest p) (x : integers p C)
    (hx : ∀ n : ℕ, x ∈ Ideal.span ({((p : integers p C) ^ n)} : Set (integers p C))) :
    x = 0 := by
  have hC := integers_adic_complete p C
  refine IsHausdorff.haus hC.toIsHausdorff x fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, SModEq.zero]
  exact hx n

end MathlibExtTest.AlgebraicGeometry.PDivisibleHodgeTateRealization
