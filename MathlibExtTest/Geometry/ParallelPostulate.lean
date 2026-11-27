/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.ParallelPostulate

/-! # Tests for `MathlibExt.Geometry.ParallelPostulate` -/

namespace MathlibExtTest.ParallelPostulate

open MathlibExt.Geometry.ParallelPostulateWanted.Geometry

-- Test section: the axioms of `TarskiAbsolute`, through a few first consequences of them
-- derived in an arbitrary model.

-- Congruence is reflexive: `ab ≅ ba` twice, and transitivity (A1, A2).
example {M : Type*} (T : TarskiAbsolute M) (a b : M) : T.C a b a b :=
  T.congr_trans b a a b a b (T.congr_refl b a) (T.congr_refl b a)

-- `B a b b`: extend `ab` beyond `b` by a null segment (A4), which is a point (A3).
private theorem betw_right {M : Type*} (T : TarskiAbsolute M) (a b : M) : T.B a b b := by
  obtain ⟨x, hx, hbx⟩ := T.segment_construction a b b b
  rwa [← T.congr_id b x b hbx] at hx

-- Betweenness is symmetric: inner Pasch (A7) applied to `B a b c` and `B b c c` gives a
-- point between `b` and `b`, which is `b` (A6).
private theorem betw_symm {M : Type*} (T : TarskiAbsolute M) {a b c : M} (h : T.B a b c) :
    T.B c b a := by
  obtain ⟨x, hbx, hcx⟩ := T.inner_pasch a b c b c h (betw_right T b c)
  rwa [← T.betw_id b x hbx] at hcx

-- `B a a b`, from the two previous facts.
example {M : Type*} (T : TarskiAbsolute M) (a b : M) : T.B a a b :=
  betw_symm T (betw_right T b a)

-- A model has two distinct points: if the first two points `a, b` given by A8 were equal,
-- `B a a c` would contradict A8.
example {M : Type*} (T : TarskiAbsolute M) : ∃ a b : M, a ≠ b := by
  obtain ⟨a, b, c, h, -, -⟩ := T.lower_dim
  refine ⟨a, b, fun hab => h ?_⟩
  rw [← hab]
  exact betw_symm T (betw_right T c a)

-- Test section: independence of the parallel postulate.

-- The Euclidean axiom is not a consequence of the axioms of absolute plane geometry.
example : ¬ ∀ (M : Type) (T : TarskiAbsolute M), Euclidean M T := fun h => by
  obtain ⟨M, T, hT⟩ := parallel_postulate_independent.2
  exact hT (h M T)

-- Nor is its negation: absolute plane geometry decides neither.
example : ¬ ∀ (M : Type) (T : TarskiAbsolute M), ¬ Euclidean M T := fun h => by
  obtain ⟨M, T, hT⟩ := parallel_postulate_independent.1
  exact h M T hT

-- There are two models of absolute plane geometry that differ on the Euclidean axiom.
example : ∃ (M₁ M₂ : Type) (T₁ : TarskiAbsolute M₁) (T₂ : TarskiAbsolute M₂),
    Euclidean M₁ T₁ ∧ ¬ Euclidean M₂ T₂ := by
  obtain ⟨⟨M₁, T₁, h₁⟩, ⟨M₂, T₂, h₂⟩⟩ := parallel_postulate_independent
  exact ⟨M₁, M₂, T₁, T₂, h₁, h₂⟩

end MathlibExtTest.ParallelPostulate
