/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SemigroupLargeness
public import Mathlib.Algebra.Free

open MetaMathlibExt

/-! Tests for `MathlibExt.Combinatorics.SemigroupLargeness`. -/

-- The whole free semigroup on two letters is piecewise syndetic and a `J`-set.
example : IsMulPiecewiseSyndetic (Set.univ : Set (FreeSemigroup Bool)) :=
  isMulPiecewiseSyndetic_univ

example : IsMulJSet (Set.univ : Set (FreeSemigroup Bool)) := isMulJSet_univ

-- The empty set is not large.
example : ¬ IsMulPiecewiseSyndetic (∅ : Set (FreeSemigroup Bool)) :=
  not_isMulPiecewiseSyndetic_empty

example : ¬ IsMulJSet (∅ : Set (FreeSemigroup Bool)) := not_isMulJSet_empty

example : ¬ IsCentralSet (∅ : Set ℕ) := not_isCentralSet_empty

example : ¬ IsCSet (∅ : Set ℕ) := not_isCSet_empty

-- Boundary: over the empty semigroup every set, including `∅`, is vacuously a `J`-set,
-- which is why `not_isMulJSet_empty` assumes `[Nonempty S]`.
example : IsMulJSet (∅ : Set (FreeSemigroup Empty)) :=
  fun _ hF => (hF.choose 0).head.elim

-- Over the empty semigroup no set is piecewise syndetic.
example (D : Set (FreeSemigroup Empty)) : ¬ IsMulPiecewiseSyndetic D := by
  rintro ⟨G, hG⟩
  obtain ⟨x, -⟩ := hG ∅
  exact x.head.elim
