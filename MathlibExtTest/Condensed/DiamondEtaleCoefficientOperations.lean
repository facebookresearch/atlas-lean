/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.DiamondEtaleCoefficientOperations

/-!
# Geometric-point data of diamond étale coefficient operations

The original Huber ring of an `IntegralGeometricInclusion` is a field with its own ring operations,
so it has no nontrivial idempotents (a product of two fields is excluded), and its algebraic
closedness refers to that field structure.
-/

namespace MathlibExtTest.DiamondEtaleCoefficientOperations

open MathlibExt.Condensed.DiamondEtaleCoefficientOperations

variable {p : ℕ} [Fact p.Prime]

/-- The original ring of a geometric inclusion has no nontrivial idempotent. -/
theorem idempotent_eq_zero_or_one (T : IntegralGeometricInclusion p) (e : T.original.pair.ring)
    (he : e * e = e) : e = 0 ∨ e = 1 := by
  letI := T.isField.toField
  exact IsIdempotentElem.iff_eq_zero_or_one.mp he

/-- Algebraic closedness is stated for the field structure of the original ring operations. -/
example (T : IntegralGeometricInclusion p) :
    letI := T.isField.toField; IsAlgClosed T.original.pair.ring := T.closed

end MathlibExtTest.DiamondEtaleCoefficientOperations
