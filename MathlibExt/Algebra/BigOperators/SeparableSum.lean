/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

/-!
# Separable multiple sums

Reindexing and factorisation lemmas for double and quadruple sums whose summand separates
into factors depending on disjoint groups of indices.

Extracted from the absolutely-maximally-entangled-state development now in
`PhyslibExt.QuantumInfo.AbsolutelyMaximallyEntangled`.
-/

namespace MetaMathlibExt

/-- Reorder a quadruple sum over finite index types `U`, `V`, `A`, `B` with values in an
additive commutative monoid, moving the last two indices to the front:
`∑ u, ∑ v, ∑ a, ∑ b, f u v a b = ∑ a, ∑ b, ∑ u, ∑ v, f u v a b`. -/
lemma sum_four_comm {R U V A B : Type*} [AddCommMonoid R]
    [Fintype U] [Fintype V] [Fintype A] [Fintype B]
    (f : U → V → A → B → R) :
    (∑ u, ∑ v, ∑ a, ∑ b, f u v a b) =
      ∑ a, ∑ b, ∑ u, ∑ v, f u v a b := by
  calc
    _ = ∑ u, ∑ a, ∑ v, ∑ b, f u v a b := by
      apply Finset.sum_congr rfl; intro u hu; rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ v, ∑ b, f u v a b := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ u, ∑ b, ∑ v, f u v a b := by
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro u hu
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl; intro a ha; rw [Finset.sum_comm]

/-- Over finite index types `U`, `V` and a commutative ring, a double sum of a product that
separates in the two indices factors as a product of sums:
`∑ u, ∑ v, K * B u * Q v = K * (∑ u, B u) * (∑ v, Q v)`. -/
lemma sum_separable {R U V : Type*} [CommRing R] [Fintype U] [Fintype V]
    (K : R) (B : U → R) (Q : V → R) :
    (∑ u, ∑ v, K * B u * Q v) = K * (∑ u, B u) * (∑ v, Q v) := by
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v hv
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Over finite index types `U`, `V`, `A`, `B` and a commutative ring, a double sum of a
product of two separable bilinear expressions factors into a sum over the inner indices of
products of one-index sums:
`∑ u, ∑ v, (C * ∑ a, bx a u * qx a v) * (D * ∑ b, byy b u * qy b v)` equals
`C * D * ∑ a, ∑ b, (∑ u, bx a u * byy b u) * (∑ v, qx a v * qy b v)`. -/
lemma sum_product_separable {R U V A B : Type*} [CommRing R]
    [Fintype U] [Fintype V] [Fintype A] [Fintype B]
    (C D : R) (bx : A → U → R) (byy : B → U → R)
    (qx : A → V → R) (qy : B → V → R) :
    (∑ u, ∑ v, (C * ∑ a, bx a u * qx a v) *
      (D * ∑ b, byy b u * qy b v)) =
      C * D * ∑ a, ∑ b,
        (∑ u, bx a u * byy b u) * (∑ v, qx a v * qy b v) := by
  calc
    _ = ∑ u, ∑ v, ∑ a, ∑ b,
        C * D * (bx a u * byy b u) * (qx a v * qy b v) := by
      apply Finset.sum_congr rfl; intro u hu
      apply Finset.sum_congr rfl; intro v hv
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro b hb
      ring
    _ = ∑ a, ∑ b, ∑ u, ∑ v,
        C * D * (bx a u * byy b u) * (qx a v * qy b v) :=
      sum_four_comm _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b hb
      rw [show C * D * ((∑ u, bx a u * byy b u) *
          (∑ v, qx a v * qy b v)) =
          C * D * (∑ u, bx a u * byy b u) *
          (∑ v, qx a v * qy b v) by ring]
      exact sum_separable (C * D) _ _

end MetaMathlibExt
