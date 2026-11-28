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

-- Degree zero uses the empty partition even when there are no variables.
example : MvPolynomial.esymm (Fin 0) ℚ 0 = 1 := by
  rw [esymm_eq_sum_partitions]
  simp

-- The two partitions of 2 give (p₁² - p₂) / 2, including the sign of (2).
example (σ : Type*) [Fintype σ] :
    MvPolynomial.esymm σ ℚ 2 =
      (1 / 2 : ℚ) • MvPolynomial.psum σ ℚ 1 ^ 2 - (1 / 2 : ℚ) • MvPolynomial.psum σ ℚ 2 := by
  let ones : (2 : ℕ).Partition := ⟨{1, 1}, by simp, by decide⟩
  let two : (2 : ℕ).Partition := ⟨{2}, by simp, by decide⟩
  have huniv : (Finset.univ : Finset (2 : ℕ).Partition) = {ones, two} := by
    ext l
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases h : 2 ∈ l.parts
    · right
      have hs := l.parts_sum
      rw [← Multiset.cons_erase h, Multiset.sum_cons] at hs
      have he : l.parts.erase 2 = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro a ha
        have hpos := l.parts_pos (Multiset.mem_of_mem_erase ha)
        have hle := Multiset.le_sum_of_mem ha
        omega
      apply Nat.Partition.ext
      rw [← Multiset.cons_erase h, he]
      rfl
    · left
      have hr := Multiset.eq_replicate_of_mem (s := l.parts) (a := 1) fun a ha ↦ by
        have hpos := l.parts_pos ha
        have hle := Nat.Partition.le_of_mem_parts ha
        have hne : a ≠ 2 := fun e ↦ h (e ▸ ha)
        omega
      have hs := l.parts_sum
      rw [hr, Multiset.sum_replicate, Nat.nsmul_eq_mul, mul_one] at hs
      exact Nat.Partition.ext (by simpa [hs, ones] using hr)
  have hne : ones ≠ two := by decide
  rw [esymm_eq_sum_partitions, huniv, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  norm_num [ones, two, Multiset.count_cons, pow_two, sub_eq_add_neg, neg_smul]

section EsymmSeries

open PowerSeries

private noncomputable def signedSeries (σ : Type*) [Fintype σ] :
    PowerSeries (MvPolynomial σ ℚ) :=
  PowerSeries.mk fun n ↦ if n = 0 then 0 else ((-1 : ℚ) ^ (n - 1) / n) • MvPolynomial.psum σ ℚ n

-- Even with no variables, both series have constant term 1.
example : coeff 0 ((exp ℚ).subst (signedSeries (Fin 0))) = 1 := by
  have hz : constantCoeff (signedSeries (Fin 0)) = 0 := by simp [signedSeries]
  rw [coeff_zero_eq_constantCoeff]
  change MvPowerSeries.constantCoeff ((exp ℚ).subst (signedSeries (Fin 0))) = 1
  rw [constantCoeff_subst_of_constantCoeff_zero hz, constantCoeff_exp, map_one]

example : coeff 0 (PowerSeries.mk (MvPolynomial.esymm (Fin 0) ℚ)) = 1 := by
  simp

-- Compute the quadratic coefficient on each side independently, at x₀ = 2 and x₁ = 3.
example : MvPolynomial.aeval (fun i : Fin 2 ↦ (i.val : ℚ) + 2)
    (coeff 2 ((exp ℚ).subst (signedSeries (Fin 2)))) = 6 := by
  let p := signedSeries (Fin 2)
  have hp : constantCoeff p = 0 := by simp [p, signedSeries]
  have hs : (fun d : ℕ ↦ coeff d (exp ℚ) • coeff 2 (p ^ d)).support ⊆
      (Finset.range 3 : Set ℕ) := by
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra! h
    have hdvd : (X : PowerSeries (MvPolynomial (Fin 2) ℚ)) ^ d ∣ p ^ d :=
      pow_dvd_pow_of_dvd (X_dvd_iff.mpr hp) d
    apply hd
    change coeff d (exp ℚ) • coeff 2 (p ^ d) = 0
    rw [X_pow_dvd_iff.mp hdvd 2 (by omega), smul_zero]
  have h₂ : coeff 2 (p ^ 2) = (coeff 1 p) ^ 2 := by
    have hanti : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
    rw [pow_two, coeff_mul, hanti]
    simp [Finset.sum_insert, coeff_zero_eq_constantCoeff, hp, pow_two]
  change MvPolynomial.aeval _ (coeff 2 ((exp ℚ).subst p)) = 6
  rw [coeff_subst' (.of_constantCoeff_zero' hp), finsum_eq_sum_of_support_subset _ hs,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h₂]
  norm_num [p, signedSeries, MvPolynomial.psum, Fin.sum_univ_two, map_smul]

example : MvPolynomial.aeval (fun i : Fin 2 ↦ (i.val : ℚ) + 2)
    (coeff 2 (PowerSeries.mk (MvPolynomial.esymm (Fin 2) ℚ))) = 6 := by
  have hs : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
  norm_num [MvPolynomial.esymm, hs, Fin.prod_univ_two]

-- The public identity applies to the entire two-variable series.
example : (exp ℚ).subst (signedSeries (Fin 2)) =
    PowerSeries.mk (MvPolynomial.esymm (Fin 2) ℚ) :=
  exp_signedPowerSumSeries_eq_esymmSeries (Fin 2)

end EsymmSeries

end MetaMathlibExt.PowerSumExpTest
