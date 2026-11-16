/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Tactic.Linarith

/-!
# Bhattacharyya pairwise bound

The probability, under one output distribution, of the
region where another is at least as likely is at most the
Bhattacharyya coefficient. Random-coding averaging is not
included here.
-/

@[expose] public section

/-- Bhattacharyya pairwise error bound (QCI-33 core). For
two output distributions `p` and `q` on a finite alphabet,
the `p`-probability of the region where `q` is at least as
likely as `p` is at most `∑ √(p q)`. This is the pairwise
step of random-coding union bounds. -/
theorem pairwise_error_le {n : ℕ} (p q : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i) :
    ∑ i ∈ Finset.univ.filter (fun i => p i ≤ q i), p i
      ≤ ∑ i, Real.sqrt (p i * q i) := by
  calc
    ∑ i ∈ Finset.univ.filter (fun i => p i ≤ q i), p i
        ≤ ∑ i ∈ Finset.univ.filter (fun i => p i ≤ q i), Real.sqrt (p i * q i) := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have _hq := hq0 i
          have h1 : p i = Real.sqrt (p i) * Real.sqrt (p i) :=
            (Real.mul_self_sqrt (hp0 i)).symm
          have h2 : Real.sqrt (p i) * Real.sqrt (p i)
              ≤ Real.sqrt (p i) * Real.sqrt (q i) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (Real.sqrt_nonneg _)
          have h3 : Real.sqrt (p i) * Real.sqrt (q i) = Real.sqrt (p i * q i) :=
            (Real.sqrt_mul (hp0 i) _).symm
          linarith
    _ ≤ ∑ i, Real.sqrt (p i * q i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact Real.sqrt_nonneg _

end
