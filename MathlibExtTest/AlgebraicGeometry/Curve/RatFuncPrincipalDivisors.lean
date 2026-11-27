/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPrincipalDivisors

/-! # Tests for principal divisors on the rational function field -/

@[expose] public section

namespace AlgebraicCurve.RationalFunctionField

-- `exactSource` consumer with the original binders.
example (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  hasPrincipalDivisors K

example {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite :=
  finite_setOf_ord_ne_zero hf

example {K : Type*} [Field K] (v : Place K (RatFunc K)) : Module.Finite K v.ResidueField :=
  finite_residueField v

-- Consequence: the divisor of a nonzero rational function has degree zero.
example {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) :
    ∃ D : Divisor K (RatFunc K), (∀ v, D v = v.ord f) ∧ Divisor.degree D = 0 :=
  (hasPrincipalDivisors K).exists_divisor f hf

-- Boundary: the hypothesis `f ≠ 0` matters only formally, since `ord 0 = 0` everywhere.
example {K : Type*} [Field K] : {v : Place K (RatFunc K) | v.ord (0 : RatFunc K) ≠ 0} = ∅ := by
  ext v
  simp

-- Universe check.
universe u in
example (K : Type u) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  hasPrincipalDivisors K

end AlgebraicCurve.RationalFunctionField
