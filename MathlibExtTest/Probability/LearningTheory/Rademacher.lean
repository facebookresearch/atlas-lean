/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.Rademacher

/-- Boundary check: for a singleton class the Massart bound applies
with `log 1 = 0` on the right side after simplification of the
statement shape. -/
example (v : Fin 2 → ℝ) :
    (∑ σ : Fin 2 → Bool,
      ({v} : Finset (Fin 2 → ℝ)).sup' (by simp)
        (fun w => ∑ i, (if σ i then (1 : ℝ) else -1) * w i)) / 2 ^ 2 ≤
    Real.sqrt (2 * Real.log (({v} : Finset (Fin 2 → ℝ)).card)) *
      ({v} : Finset (Fin 2 → ℝ)).sup' (by simp)
        (fun w => Real.sqrt (∑ i, w i ^ 2)) :=
  massart_finite_class (by simp)

/-- The zero class has Rademacher average zero: the bound is an
equality case at `0`. -/
example :
    (∑ σ : Fin 2 → Bool,
      ({0} : Finset (Fin 2 → ℝ)).sup' (by simp)
        (fun w => ∑ i, (if σ i then (1 : ℝ) else -1) * w i)) / 2 ^ 2 ≤
    Real.sqrt (2 * Real.log (({0} : Finset (Fin 2 → ℝ)).card)) *
      ({0} : Finset (Fin 2 → ℝ)).sup' (by simp)
        (fun w => Real.sqrt (∑ i, w i ^ 2)) :=
  massart_finite_class (by simp)
