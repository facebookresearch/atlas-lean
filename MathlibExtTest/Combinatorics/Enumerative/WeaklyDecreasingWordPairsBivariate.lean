/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WeaklyDecreasingWordPairsBivariate
import Mathlib.Tactic.NormNum

/-! # Coefficient tests for disjoint weakly decreasing word pairs -/

open MetaMathlibExt

private noncomputable def disjointSeries (k : ℕ) : MvPowerSeries (Fin 2) ℚ :=
  (MvPowerSeries.X 0 * (1 - MvPowerSeries.X 0)⁻¹ + (1 - MvPowerSeries.X 1)⁻¹) ^ k -
    ((1 - MvPowerSeries.X 0)⁻¹) ^ k - ((1 - MvPowerSeries.X 1)⁻¹) ^ k + 1

-- For each of the three one-letter second words, the first word can use either remaining letter
-- twice, or both in decreasing order.
example :
    MvPowerSeries.coeff (Finsupp.single 0 2 + Finsupp.single 1 1) (disjointSeries 3) = 9 := by
  unfold disjointSeries
  rw [weaklyDecreasingNonIntersectingPairs_generatingFunction, ite_eq_left (by decide)]
  suffices h : (Finset.univ.filter fun p : (Fin 2 → Fin 3) × (Fin 1 → Fin 3) =>
      Antitone p.1 ∧ Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
        9 by exact_mod_cast h
  decide

-- Neither axis counts any pairs, including the origin.
example (k : ℕ) : MvPowerSeries.coeff (Finsupp.single 0 2) (disjointSeries k) = 0 := by
  simpa [disjointSeries] using weaklyDecreasingNonIntersectingPairs_generatingFunction k 2 0

example (k : ℕ) : MvPowerSeries.coeff (Finsupp.single 1 2) (disjointSeries k) = 0 := by
  simpa [disjointSeries] using weaklyDecreasingNonIntersectingPairs_generatingFunction k 0 2

example (k : ℕ) : MvPowerSeries.constantCoeff (disjointSeries k) = 0 := by
  simp [disjointSeries, MvPowerSeries.constantCoeff_inv]

-- A positive bidegree over the empty alphabet.
example :
    MvPowerSeries.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) (disjointSeries 0) = 0 := by
  unfold disjointSeries
  rw [weaklyDecreasingNonIntersectingPairs_generatingFunction, ite_eq_left (by decide)]
  suffices h : (Finset.univ.filter fun p : (Fin 1 → Fin 0) × (Fin 1 → Fin 0) =>
      Antitone p.1 ∧ Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card =
        0 by exact_mod_cast h
  decide
