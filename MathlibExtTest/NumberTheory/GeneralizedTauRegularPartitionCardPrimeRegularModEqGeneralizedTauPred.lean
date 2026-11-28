/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTauRegularPartitionCardPrimeRegularModEqGeneralizedTauPred

namespace MathlibExtTest.NumberTheory.GeneralizedTauRegularPartitionCardPrimeRegularModEqGeneralizedTauPred

open MetaMathlibExt

-- At `p = 2`, `n = 1`: the only partition of `1` is `2`-regular, so `τ_1(2)` is odd.
example : generalizedTau 1 2 ≡ 1 [ZMOD 2] := by
  have hcard : (Nat.Partition.restricted 1 (¬ 2 ∣ ·)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨default, ?_⟩
    ext x
    simp [Nat.Partition.restricted, Subsingleton.elim x default]
  have h := card_prime_regular_modEq_generalizedTau_pred 2 (by decide) 1
  rw [hcard] at h
  simpa using h.symm

open PowerSeries

private def pairOfOnes : Nat.Partition 2 :=
  ⟨{1, 1}, by simp, by decide⟩

-- The two distinct partitions exhaust the fintype: there are only two compositions of 2.
private theorem partitions_two :
    (Finset.univ : Finset (Nat.Partition 2)) = {Nat.Partition.indiscrete 2, pairOfOnes} := by
  apply Finset.eq_of_superset_of_card_ge (Finset.subset_univ _)
  have hcard := Fintype.card_le_of_surjective _ (Nat.Partition.ofComposition_surj (n := 2))
  rw [composition_card] at hcard
  rw [Finset.card_pair_eq_two_iff.mpr (by decide)]
  exact hcard

-- Both sides are exactly one for the empty partition, without the congruence theorem.
example : (Nat.Partition.restricted 0 (¬ 8 ∣ ·)).card = 1 ∧ generalizedTau 7 1 = 1 :=
  ⟨by decide, generalizedTau_one 7⟩

-- At `s = 1`, the part `2` is excluded, leaving the partition `1 + 1`.
example : (Nat.Partition.restricted 2 (¬ 2 ∣ ·)).card = 1 ∧ generalizedTau 1 3 = -1 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.Partition.restricted, partitions_two]
    decide
  change generalizedTau ((1 : ℕ) : ℤ) (2 + 1) = -1
  rw [generalizedTau_natCast, coeff_succ_X_mul, pow_one]
  simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ (-1)

-- At `s = 2`, both `2` and `1 + 1` are allowed, and the cubic coefficient is even.
example : (Nat.Partition.restricted 2 (¬ 4 ∣ ·)).card = 2 ∧ generalizedTau 3 3 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.Partition.restricted, partitions_two]
    decide
  change generalizedTau ((3 : ℕ) : ℤ) (2 + 1) = 0
  have h₁ : coeff 1 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ 1
  have h₂ : coeff 2 (pentagonalSeries ℤ) = -1 := by
    simpa [pentagonal_def] using coeff_pentagonalSeries_pentagonal ℤ (-1)
  have ha₁ : Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  have ha₂ : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [generalizedTau_natCast, coeff_succ_X_mul, show (3 : ℕ) = 2 + 1 by rfl, pow_succ,
    coeff_mul, ha₂, pow_two]
  norm_num [coeff_mul, ha₁, ha₂, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_pentagonalSeries_int, h₁, h₂]

-- API client at the first index where four-regularity excludes a part.
example : ((Nat.Partition.restricted 4 (¬ 4 ∣ ·)).card : ℤ) ≡ generalizedTau 3 5 [ZMOD 2] :=
  card_two_pow_regular_modEq_generalizedTau 2 (by decide) 4

end MathlibExtTest.NumberTheory.GeneralizedTauRegularPartitionCardPrimeRegularModEqGeneralizedTauPred
