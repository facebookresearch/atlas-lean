/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Mapping sums of squares

Ring homomorphisms preserve finite sums of squares. This algebraic fact uses
no order and allows the existing `IsSumSq.nonneg` theorem to be applied after
polynomial evaluation.
-/

@[expose] public section

/-- A ring homomorphism between semirings sends a sum of squares to a sum of
squares, without any order or commutativity assumption. -/
theorem IsSumSq.map {R S : Type*} [Semiring R] [Semiring S] {p : R}
    (hp : IsSumSq p) (f : R →+* S) : IsSumSq (f p) := by
  induction hp with
  | zero => simpa only [map_zero] using (IsSumSq.zero : IsSumSq (0 : S))
  | sq_add a hs ih => simpa only [map_add, map_mul] using IsSumSq.sq_add (f a) ih
