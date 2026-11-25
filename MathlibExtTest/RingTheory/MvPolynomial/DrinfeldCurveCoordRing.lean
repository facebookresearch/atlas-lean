/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.DrinfeldCurveCoordRing

@[expose] public section

namespace MathlibExtTest.RingTheory.MvPolynomial.DrinfeldCurveCoordRing

universe u

/-- Consumer with the original binders: every field and every `q ≠ 1`. -/
theorem exactSource (q : ℕ) (hq : q ≠ 1) (k : Type u) [Field k] :
    IsDomain (DrinfeldCurve.CoordRing q k) :=
  DrinfeldCurve.isDomain_coordRing_of_ne_one q hq k

/-- Higher-universe consumer. -/
example (q : ℕ) (hq : q ≠ 1) (k : Type (u + 1)) [Field k] :
    IsDomain (DrinfeldCurve.CoordRing q k) :=
  DrinfeldCurve.isDomain_coordRing_of_ne_one q hq k

/-- The boundary case `q = 0` is included. -/
example (k : Type u) [Field k] : IsDomain (DrinfeldCurve.CoordRing 0 k) :=
  DrinfeldCurve.isDomain_coordRing_of_ne_one 0 (by norm_num) k

/-- The hypothesis `q ≠ 1` matters: for `q = 1` the defining polynomial is
zero, so the coordinate ring is the full polynomial ring modulo `(-1)`,
which is the zero ring and hence not a domain. Concretely the defining
ideal is the unit ideal. -/
example (k : Type u) [Field k] : DrinfeldCurve.drinfeldIdeal 1 k = ⊤ := by
  rw [DrinfeldCurve.drinfeldIdeal, Ideal.span_singleton_eq_top]
  have h : DrinfeldCurve.drinfeldPoly 1 k - 1 = -1 := by
    simp [DrinfeldCurve.drinfeldPoly]
  rw [h]
  exact isUnit_one.neg

end MathlibExtTest.RingTheory.MvPolynomial.DrinfeldCurveCoordRing
