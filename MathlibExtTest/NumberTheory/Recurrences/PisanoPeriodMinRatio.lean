/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.PisanoPeriodMinRatio

open MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityWanted

-- The first nonempty interval contains only the modulus 1, whose ratio is 1.
example : (⨅ n : {n : ℕ // n ∈ Finset.Icc 1 (2 - 1)}, (pisanoPeriod n.1 : ℝ) / n.1) = 1 := by
  let i : {n : ℕ // n ∈ Finset.Icc 1 (2 - 1)} := ⟨1, by decide⟩
  have : Nonempty {n : ℕ // n ∈ Finset.Icc 1 (2 - 1)} := ⟨i⟩
  have hperiod : pisanoPeriod 1 = 1 := Function.minimalPeriod_eq_one_of_subsingleton
  have hratio (n : {n : ℕ // n ∈ Finset.Icc 1 (2 - 1)}) : (pisanoPeriod n.1 : ℝ) / n.1 = 1 := by
    have hn := Finset.mem_Icc.mp n.2
    have h : n.1 = 1 := by omega
    simp [h, hperiod]
  simp [hratio]

-- A concrete tolerance can be required uniformly for all sufficiently large cutoffs.
example : ∀ᶠ N : ℕ in Filter.atTop,
    (⨅ n : {n : ℕ // n ∈ Finset.Icc 1 (N - 1)}, (pisanoPeriod n.1 : ℝ) / n.1) < 1 / 10 :=
  tendsto_iInf_pisanoPeriod_div_atTop.eventually_lt_const (by positivity)
