/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Kaehler.FormallySmoothPowLinearIndep

@[expose] public section

-- Consumer with the original binders.
universe u in
example {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) :=
  Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id p hp s hs

-- Higher-universe consumer: the statement is universe-polymorphic.
example {k K : Type 1} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) :=
  Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id p hp s hs

-- The independence hypothesis matters: `0` is never part of an independent
-- family, and its powers are not independent either.
example : ¬ LinearIndepOn (ZMod 2) (· ^ 2) (({0, 1} : Finset (ZMod 2)) : Set (ZMod 2)) := by
  rw [linearIndepOn_finset_iffₛ]
  push Not
  refine ⟨fun x => if x = 0 then 1 else 0, 0, ?_, 0, by simp, ?_⟩
  · simp [Finset.sum_pair (show (0 : ZMod 2) ≠ 1 by decide)]
  · simp
