/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.ExoticUnitsC2C2C2C6

open MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted
open AddMonoidAlgebra (single)

/- A negative basis element has inverse supported at the additive inverse. -/
example (g : OWRGroup) : IsUnit (single g (-1) : OWRGroupRing) := by
  apply IsUnit.of_mul_eq_one (single (-g) (-1))
  simp [AddMonoidAlgebra.one_def]

/- The coefficients of 2[0] − [g] sum to one, but it cannot be a unit for nonzero g. -/
example (g : OWRGroup) (hg : g ≠ 0) :
    ¬ IsUnit (single 0 2 - single g 1 : OWRGroupRing) := by
  rintro ⟨u, hu⟩
  apply conjecture_refuted
  refine ⟨u, fun h s heq => ?_⟩
  rw [hu] at heq
  have hcoeff := congrArg (fun x : OWRGroupRing => x.coeff 0) heq
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hg] at hcoeff
  rcases Int.isUnit_iff.1 s.isUnit with hs | hs <;> split_ifs at hcoeff <;> omega
