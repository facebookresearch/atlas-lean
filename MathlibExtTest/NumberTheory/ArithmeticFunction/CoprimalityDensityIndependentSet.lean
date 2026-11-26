/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.CoprimalityDensityIndependentSet

open Finset MetaMathlibExt

-- The empty vertex set contributes a single independent set of size zero.
example :
    (∏' p : Nat.Primes, ∑ m ∈ range 1,
      ((univ.filter fun S : Finset (Fin 0) =>
          S.card = m ∧ ∀ e ∈ (∅ : Finset (Fin 0 × Fin 0)), ¬ (e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) /
        ((p : ℕ) : ℝ) ^ m * (1 - 1 / ((p : ℕ) : ℝ)) ^ (0 - m)) = 1 := by
  rw [← coprimalityDensity_eq_independent_set_product ∅ (hE := by simp)]
  exact coprimalityDensity_empty 0

-- A single edge allows the empty set and both singletons, but excludes the full set.
example :
    coprimalityDensity ({(0, 1)} : Finset (Fin 2 × Fin 2)) =
      ∏' p : Nat.Primes, (1 - (1 / ((p : ℕ) : ℝ)) ^ 2) := by
  let E : Finset (Fin 2 × Fin 2) := {(0, 1)}
  let count (m : ℕ) :=
    (univ.filter fun S : Finset (Fin 2) =>
      S.card = m ∧ ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)).card
  have h0 : count 0 = 1 := by decide
  have h1 : count 1 = 2 := by decide
  have h2 : count 2 = 0 := by decide
  rw [coprimalityDensity_eq_independent_set_product E (hE := by decide)]
  refine tprod_congr fun p => ?_
  change (∑ m ∈ range 3, (count m : ℝ) / ((p : ℕ) : ℝ) ^ m *
    (1 - 1 / ((p : ℕ) : ℝ)) ^ (2 - m)) = _
  rw [sum_range_succ, sum_range_succ, sum_range_one, h0, h1, h2]
  norm_num
  ring
