/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.RealPartialFractions
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.Positivity

/-! # Tests for partial fraction decomposition over the reals -/

namespace MathlibExtTest.FieldTheory.RealPartialFractions

open scoped Polynomial RatFunc
open Polynomial MathlibExt.FieldTheory.RealPartialFractionsWanted

private def Decomposes (f : ℝ⟮X⟯) : Prop :=
  ∃ (q : ℝ[X]) (s : Finset ℝ[X]) (g : ℝ[X] → ℕ → ℝ[X]) (m : ℝ[X] → ℕ),
    (∀ p ∈ s, p.Monic ∧ (p.natDegree = 1 ∨ (p.natDegree = 2 ∧ Irreducible p)))
      ∧ (∀ p ∈ s, ∀ k < m p, (g p k).natDegree < p.natDegree)
      ∧ f = algebraMap ℝ[X] ℝ⟮X⟯ q
          + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
              algebraMap ℝ[X] ℝ⟮X⟯ (g p k) / algebraMap ℝ[X] ℝ⟮X⟯ p ^ (k + 1)

example (f : ℝ⟮X⟯) : Decomposes f := ratFunc_partial_fractions_real f

-- A polynomial, including zero, has a decomposition with empty support.
example (q : ℝ[X]) : Decomposes (algebraMap ℝ[X] ℝ⟮X⟯ q) := by
  exact ⟨q, ∅, 0, 0, by simp, by simp, by simp⟩

-- For X / (X² + 1)² the numerator at the first power is zero and at the second it is X.
example : Decomposes (algebraMap ℝ[X] ℝ⟮X⟯ X / algebraMap ℝ[X] ℝ⟮X⟯ (X ^ 2 + 1) ^ 2) := by
  classical
  let p : ℝ[X] := X ^ 2 + C 1
  have hd : p.natDegree = 2 := natDegree_X_pow_add_C
  have hi : Irreducible p := by
    apply irreducible_of_degree_le_three_of_not_isRoot (by simp [hd])
    intro x
    change ¬ eval x (X ^ 2 + C (1 : ℝ)) = 0
    simp only [eval_add, eval_pow, eval_X, eval_C]
    exact ne_of_gt (by positivity)
  refine ⟨0, {p}, fun _ k => if k = 1 then X else 0, fun _ => 2, ?_, ?_, ?_⟩
  · intro t ht
    obtain rfl := Finset.mem_singleton.mp ht
    exact ⟨monic_X_pow_add_C 1 two_ne_zero, Or.inr ⟨hd, hi⟩⟩
  · intro t ht k _
    obtain rfl := Finset.mem_singleton.mp ht
    by_cases hk : k = 1 <;> simp [hk, hd]
  · simp [Finset.sum_range_succ, p]

end MathlibExtTest.FieldTheory.RealPartialFractions
