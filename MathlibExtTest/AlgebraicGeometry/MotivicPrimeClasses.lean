/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MotivicPrimeClasses

/-!
# Bidegrees of the classes `c` and `d` of `BΣ_ℓ`

The class `d` has bidegree `(2(ℓ - 1), ℓ - 1)` and `c` has bidegree `(2ℓ - 3, ℓ - 1)`
(Voevodsky, *Reduced power operations in motivic cohomology*, §6): for `ℓ = 2` these are
`(2, 1)` and `(1, 1)`, and for `ℓ = 3` they are `(4, 2)` and `(3, 2)`.
-/

open MathlibExt.AlgebraicGeometry.MotivicPrimeClasses

example : primeWeight 2 = 1 ∧ dDegree 2 = 2 ∧ cDegree 2 = 1 := by decide
example : primeWeight 3 = 2 ∧ dDegree 3 = 4 ∧ cDegree 3 = 3 := by decide

/-- For every prime the weight is `ℓ - 1` as an integer (no truncated subtraction). -/
example (ell : ℕ) (h : ell.Prime) : primeWeight ell = (ell : ℤ) - 1 := by
  have := h.one_lt
  simp only [primeWeight]
  omega

/-- `cDegree` is one less than `dDegree`, and both have weight `primeWeight`. -/
example (ell : ℕ) : cDegree ell + 1 = dDegree ell ∧ dDegree ell = 2 * primeWeight ell := by
  simp [cDegree, dDegree]
