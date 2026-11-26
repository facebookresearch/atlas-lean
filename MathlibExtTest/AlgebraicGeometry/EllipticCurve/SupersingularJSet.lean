/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.SupersingularJSet
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

@[expose] public section

namespace ModularCurve

/-- Consumer: for a prime `p`, the supersingular `j`-invariants in an algebraic closure of
`ZMod p` form a finite set. -/
private theorem ssJSet_finite_consumer (p : ℕ) [Fact p.Prime] : (ssJSet p).Finite :=
  ssJSet_finite p

/-- Consumer with the source's binders: an elliptic curve with no nonzero point killed by `q`,
over an algebraically closed field of characteristic `q`, has `j ^ q ^ 2 = j`. -/
example (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [IsAlgClosed K] [CharP K q]
    [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic]
    (hss : ∀ P : E.toAffine.Point, (q : ℤ) • P = 0 → P = 0) :
    E.j ^ (q ^ 2) = E.j :=
  E.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero q hss

/-- The theorem applies to `ssJSet p`, whose curves are supersingular in the sense of
`WeierstrassCurve.Affine.IsSupersingular`: every supersingular `j`-invariant lies in the subfield
with `p ^ 2` elements of the algebraic closure of `ZMod p`. -/
example (p : ℕ) [Fact p.Prime] (j : AlgebraicClosure (ZMod p)) (hj : j ∈ ssJSet p) :
    j ^ (p ^ 2) = j := by
  classical
  have h := (WeierstrassCurve.ofJ j).j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero p fun P hP =>
    mem_ssJSet_iff.mp hj _ (WeierstrassCurve.ofJ_j j) P (by rwa [natCast_zsmul] at hP)
  rwa [WeierstrassCurve.ofJ_j] at h

end ModularCurve
