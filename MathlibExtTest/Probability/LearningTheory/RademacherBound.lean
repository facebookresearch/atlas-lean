/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.RademacherBound

/-- Boundary check: the bound instantiates for a singleton class
on one sample point. -/
example :
    (∑ σ : Fin 1 → Bool,
      ({fun _ => true} : Finset (Fin 1 → Bool)).sup' (Finset.singleton_nonempty _)
        (fun h => ∑ i, (if σ i then (1 : ℝ) else -1) *
          (if h i then (1 : ℝ) else -1))) / 2 ^ 1 / ((1 : ℕ) : ℝ) ≤
    Real.sqrt (2 * Real.log ({fun _ => true} : Finset (Fin 1 → Bool)).card / ((1 : ℕ) : ℝ)) :=
  rademacher_finite_class (m := 1) (H := {fun _ => true}) (by norm_num) (Finset.singleton_nonempty _)
