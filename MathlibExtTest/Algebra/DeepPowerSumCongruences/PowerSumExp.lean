/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.DeepPowerSumCongruences.PowerSumExp

namespace MetaMathlibExt.PowerSumExpTest

private def degrees : Set ℕ := {0, 2}

private instance decidableMemDegrees : DecidablePred (· ∈ degrees) :=
  fun n ↦ inferInstanceAs (Decidable (n ∈ ({0, 2} : Set ℕ)))

private noncomputable def series (σ : Type*) [Fintype σ] :
    PowerSeries (MvPolynomial σ ℚ) :=
  (PowerSeries.exp ℚ).subst (PowerSeries.mk fun s ↦ if s ∈ degrees ∧ s ≠ 0 then
    ((-1 : ℚ) ^ (s - 1) / s) • MvPolynomial.psum σ ℚ s else 0)

-- Degree zero comes from the empty partition, even when zero belongs to the degree set.
example : PowerSeries.coeff 0 (series Unit) = 1 := by
  unfold series
  rw [exp_signedPowerSumSeries_eq_sum_partitions]
  simp

-- The sole allowed partition of degree four is (2, 2), whose denominator is 2² · 2!.
example : PowerSeries.coeff 4 (series Unit) = (1 / 8 : ℚ) • MvPolynomial.psum Unit ℚ 2 ^ 2 := by
  let twoTwos : (4 : ℕ).Partition :=
    ⟨Multiset.replicate 2 2, by simp, by decide⟩
  have heq (l : (4 : ℕ).Partition) (hl : ∀ a ∈ l.parts, a ∈ degrees) : l = twoTwos := by
    have hparts : l.parts = Multiset.replicate l.parts.card 2 := by
      apply Multiset.eq_replicate_of_mem
      intro a ha
      have hamem := hl a ha
      simp only [degrees, Set.mem_insert_iff, Set.mem_singleton_iff] at hamem
      exact hamem.resolve_left (l.parts_pos ha).ne'
    have hs := l.parts_sum
    rw [hparts, Multiset.sum_replicate, Nat.nsmul_eq_mul] at hs
    have hcard : l.parts.card = 2 := by omega
    exact Nat.Partition.ext (by simpa [hcard, twoTwos] using hparts)
  unfold series
  rw [exp_signedPowerSumSeries_eq_sum_partitions, PowerSeries.coeff_mk,
    Finset.sum_eq_single twoTwos]
  · norm_num [twoTwos, Multiset.count_replicate, pow_two]
  · intro l hl hne
    exact (hne (heq l (Finset.mem_filter.mp hl).2)).elim
  · intro h
    exact (h (by simp [twoTwos, degrees])).elim

end MetaMathlibExt.PowerSumExpTest
