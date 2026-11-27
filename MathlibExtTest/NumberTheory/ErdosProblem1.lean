/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem1

open MathlibExt.NumberTheory.ErdosProblem1Wanted

-- Pin the public abbreviation and its named arguments, including the closed interval.
example (A : Finset ℕ) (N : ℕ) :
    IsSumDistinctSet (A := A) (N := N) =
      (A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective) := rfl

-- Pin the historical proposition, including strictness and the separate `N ≠ 0` hypothesis.
example : conjecture = (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N) := rfl

-- Every positive constant admits a counterexample with a positive ambient bound.
example (C : ℝ) (hC : 0 < C) :
    ∃ (N : ℕ) (A : Finset ℕ), IsSumDistinctSet A N ∧ N ≠ 0 ∧ N ≤ C * 2 ^ A.card := by
  by_contra h
  apply conjecture_refuted
  refine ⟨C, hC, fun N A hA hN => lt_of_not_ge fun hle => h ?_⟩
  exact ⟨N, A, hA, hN, hle⟩
