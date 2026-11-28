/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.CaptureRecapture
import Mathlib.Tactic.NormNum

open ProbabilityTheory WantedExt.Biology.Ecology.CaptureRecaptureWanted

-- With no marked animals, the count is zero and the estimate is the second sample size.
example : ∑ k ∈ Finset.range (1 + 1), hypergeometricReal 2 0 1 k * chapman 0 1 k = 1 := by
  rw [expectation_chapman (by decide) (by decide)]
  norm_num [Nat.choose]

-- The two possible recapture counts are equally likely and give estimates 3 and 1.
example : ∑ k ∈ Finset.range (1 + 1), hypergeometricReal 2 1 1 k * chapman 1 1 k = 2 := by
  rw [expectation_chapman (by decide) (by decide)]
  norm_num [Nat.choose]

-- Equality at the threshold is included in the unbiased regime.
example : ∑ k ∈ Finset.range (2 + 1), hypergeometricReal 3 1 2 k * chapman 1 2 k = 3 := by
  exact (chapman_unbiased_iff (N := 3) (n₁ := 1) (n₂ := 2) (by decide) (by decide)).1 (by decide)

-- Below the threshold the bias is strictly downward.
example : ∑ k ∈ Finset.range (1 + 1), hypergeometricReal 3 1 1 k * chapman 1 1 k < 3 := by
  exact (chapman_unbiased_iff (N := 3) (n₁ := 1) (n₂ := 1) (by decide) (by decide)).2 (by decide)

-- Exactly four of the six two-element samples meet the marked set {0, 1} once.
example : ((((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
    fun S => (S ∩ {0, 1}).card = 1).card : ℝ) / (Nat.choose 4 2 : ℝ) = 2 / 3 ∧
    hypergeometricReal 4 2 2 1 = 2 / 3 := by
  constructor
  · have hcount : (((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
        fun S => (S ∩ {0, 1}).card = 1).card = 4 := by decide
    rw [hcount]
    norm_num [Nat.choose]
  · rw [hypergeometricReal_of_le (by decide)]
    norm_num [Nat.choose]

-- There is only one unmarked individual, so a sample of three cannot include just one marked one.
example : ((Finset.univ : Finset (Fin 4)).powersetCard 3).filter
    (fun S => (S ∩ {0, 1, 2}).card = 1) = ∅ := by decide

-- Both individuals are marked, but the second sample contains only one individual.
example : ((Finset.univ : Finset (Fin 2)).powersetCard 1).filter
    (fun S => (S ∩ Finset.univ).card = 2) = ∅ := by decide

example : hypergeometricReal 2 2 1 2 = 0 :=
  hypergeometricReal_of_lt (by decide)

-- Omitting the cutoff would incorrectly assign mass 1/2 in that case.
example : ((Nat.choose 2 2 * Nat.choose (2 - 2) (1 - 2) : ℕ) : ℝ) /
    (Nat.choose 2 1 : ℝ) = 1 / 2 := by norm_num [Nat.choose]

-- There is one empty sample from an empty population, and its overlap is zero.
example : ((Finset.univ : Finset (Fin 0)).powersetCard 0).filter
    (fun S => (S ∩ ∅).card = 0) = {∅} := by decide

-- The theorem is also usable at concrete parameters through the production import alone.
example : ((((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
    fun S => (S ∩ {0, 1}).card = 1).card : ℝ) / (Nat.choose 4 2 : ℝ) =
    hypergeometricReal 4 2 2 1 :=
  card_filter_inter_eq {0, 1} (by decide) (by decide) 1
