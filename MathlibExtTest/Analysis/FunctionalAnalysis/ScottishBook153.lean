/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153

/-!
# Tests for the negative answer to Mazur's Problem 153

* `mazur153_refuted` unpacked into the explicit form of the wiki page: one continuous function
  and one `ε > 0` defeat every finite sum of products of sections.
* The claim of Mazur's Problem 153 is equivalent to `False`.
* Edge case: the approximation scheme does work for some functions, e.g. for a constant
  function, where one product of sections reproduces `f` exactly.
-/

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted.Tests

/-- The explicit form of the negative answer: a fixed continuous function and a fixed `ε > 0`
such that every finite sum `∑ k, c k * f (a k, y) * f (x, b k)` misses `f` by more than `ε`
somewhere on the square. -/
example : ∃ (f : C(↥(Set.Icc (0 : ℝ) 1) × ↥(Set.Icc (0 : ℝ) 1), ℝ)) (ε : ℝ), 0 < ε ∧
    ∀ (n : ℕ) (a b : Fin n → ↥(Set.Icc (0 : ℝ) 1)) (c : Fin n → ℝ),
      ∃ x y : ↥(Set.Icc (0 : ℝ) 1), ε < |f (x, y) - ∑ k, c k * f (a k, y) * f (x, b k)| := by
  by_contra h
  apply mazur153_refuted
  intro f ε hε
  by_contra h'
  apply h
  refine ⟨f, ε, hε, fun n a b c => ?_⟩
  by_contra h''
  apply h'
  refine ⟨n, a, b, c, fun x y => ?_⟩
  rw [Real.dist_eq]
  by_contra h3
  exact h'' ⟨x, y, lt_of_not_ge h3⟩

/-- The claim of Mazur's Problem 153 is false. -/
example : ScottishBookProblem153Claim ↔ False :=
  iff_false_intro mazur153_refuted

/-- The scheme is exact for the constant function `1`: one product of its sections, with
coefficient `1`, reproduces it. So the failure concerns particular functions only. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a b : Fin n → ↥(Set.Icc (0 : ℝ) 1)) (c : Fin n → ℝ),
      ∀ x y : ↥(Set.Icc (0 : ℝ) 1),
        dist (ContinuousMap.const _ (1 : ℝ) (x, y))
          (∑ k, c k * ContinuousMap.const _ (1 : ℝ) (a k, y) *
            ContinuousMap.const _ (1 : ℝ) (x, b k)) ≤ ε := by
  let z : ↥(Set.Icc (0 : ℝ) 1) := ⟨0, le_refl 0, zero_le_one⟩
  refine ⟨1, fun _ => z, fun _ => z, fun _ => 1, fun x y => ?_⟩
  simp [hε.le]

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook153Wanted.Tests
