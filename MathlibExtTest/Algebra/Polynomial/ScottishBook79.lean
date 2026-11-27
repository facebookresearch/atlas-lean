/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ScottishBook79

/-!
# A bijective polynomial map outside the affine group

Extract a counterexample from the refutation and check that its evaluated map is bijective.
-/

open MathlibExt.Algebra.Polynomial.ScottishBook79Wanted MvPolynomial

example : ∃ P : Fin 2 → MvPolynomial (Fin 2) ℝ,
    Function.Bijective (fun (x : Fin 2 → ℝ) i ↦ eval x (P i)) ∧
    ¬ ∃ (a : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ), a.det ≠ 0 ∧
      ∀ (x : Fin 2 → ℝ) (i : Fin 2), eval x (P i) = ∑ j, a i j * x j + c i := by
  have h := mazurOrlicz79_refuted
  simp only [ScottishBookProblem79Claim, not_forall] at h
  obtain ⟨P, Q, hQP, hPQ, hP⟩ := h
  refine ⟨P, ⟨?_, ?_⟩, hP⟩
  · exact Function.LeftInverse.injective (g := fun y i ↦ eval y (Q i)) hQP
  · exact Function.RightInverse.surjective (g := fun y i ↦ eval y (Q i)) hPQ
