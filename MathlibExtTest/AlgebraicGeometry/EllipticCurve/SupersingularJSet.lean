/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.SupersingularJSet

@[expose] public section

namespace ModularCurve

/-- Consumer with the original binders. -/
theorem exactSource (q : ℕ) [Fact q.Prime]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (ssJSet q K).Finite :=
  ssJSet_finite q K

/-- Every supersingular `j`-invariant lies in the field with `q ^ 2` elements. -/
example (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K q]
    [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    E.j ^ (q ^ 2) = E.j :=
  E.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero q hss

end ModularCurve
