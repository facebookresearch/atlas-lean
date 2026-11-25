/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook74
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! # Coefficient-bound regressions for Scottish Book Problem 74 -/

open MathlibExt.Analysis.ScottishBook74Wanted
open scoped BigOperators

-- In degree one the bound is exactly the normalization bound.
example (a : (Fin 1 → ℕ) → ℝ)
    (hnorm : ∀ t : Fin 1 → ℝ, (∑ i, |t i|) ≤ 1 → |EvalPoly 1 a t| ≤ 1) :
    |a ![1]| ≤ 1 := by
  simpa [Fin.prod_univ_one] using
    scottishBook74_holds 1 (by decide) a hnorm ![1] (by simp)

-- At degree two, the mixed and pure terms give different factorial factors.
example (a : (Fin 2 → ℕ) → ℝ)
    (hnorm : ∀ t : Fin 2 → ℝ, (∑ i, |t i|) ≤ 1 → |EvalPoly 2 a t| ≤ 1) :
    |a ![1, 1]| ≤ 4 ∧ |a ![2, 0]| ≤ 2 := by
  constructor
  · have h := scottishBook74_holds 2 (by decide) a hnorm ![1, 1] (by simp [Fin.sum_univ_two])
    norm_num [Fin.prod_univ_two, Nat.factorial] at h ⊢
    exact h
  · have h := scottishBook74_holds 2 (by decide) a hnorm ![2, 0] (by simp [Fin.sum_univ_two])
    norm_num [Fin.prod_univ_two, Nat.factorial] at h ⊢
    exact h

-- The degree-zero entry does not become a constant term in degree two.
example (c : ℝ) (t : Fin 2 → ℝ) :
    EvalPoly 2 (fun k ↦ if k = ![0, 0] then c else 0) t = 0 := by
  classical
  unfold EvalPoly
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  have hdegree := (Finset.mem_filter.mp hk).2
  have hne : k ≠ ![0, 0] := by
    intro h
    simp [h, Fin.sum_univ_two] at hdegree
  simp [hne]
