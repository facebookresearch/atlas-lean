/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Causality.CausalIdentification

/-!
# The sib transmission/disequilibrium test (S-TDT)

The S-TDT compares affected and unaffected sibs within sibships when parental genotypes are
unknown. We model an affected set of size `a` as uniformly sampled from a sibship of size `t`.
For sib scores `x_j`, this module proves the null mean and variance of the sum of the scores
in the affected set. Both formulas hold for arbitrary real scores, including allele counts
in `{0, 1, 2}`.

Source: R. S. Spielman and W. J. Ewens, "A sibship test for linkage in the presence of
association: the sib transmission/disequilibrium test", Am. J. Hum. Genet. 62 (1998) 450–458.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SibTransmissionDisequilibriumWanted

open MathlibExt.Probability.Causality (randExp)

/-- The number of tested alleles carried by the sibs in `S`, the affected sibs. -/
def affectedAlleleCount {t : ℕ} (x : Fin t → ℝ) (S : Finset (Fin t)) : ℝ :=
  ∑ j ∈ S, x j

/-- **Null mean of the S-TDT count** (Spielman and Ewens 1998). Let a sibship have `t ≥ 1`
sibs, `a ≤ t` of them affected, and let `x_j ∈ ℝ` be the number of tested alleles of sib `j`.
If the set of affected sibs is uniformly distributed over the `a`-element subsets of the
sibship, the expected number of tested alleles among the affected sibs, `randExp a` of the count
(the average over all `a`-element subsets of the `t` sibs), is `a r / t`, where `r = ∑_j x_j`.

Source: Spielman and Ewens (1998). -/
public theorem randExp_affectedAlleleCount {t a : ℕ} (ht : 0 < t) (hat : a ≤ t)
    (x : Fin t → ℝ) :
    randExp a (affectedAlleleCount x) = a * (∑ j, x j) / t := by
  classical
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have hC : (t.choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hat).ne'
  -- Each sib lies in `t.choose a * a / t` of the `a`-subsets.
  have hcount (j : Fin t) :
      ∑ S ∈ Finset.univ.powersetCard a, (if j ∈ S then (1 : ℝ) else 0) = t.choose a * a / t := by
    rw [eq_div_iff ht']
    simpa only [Fintype.card_fin] using
      MathlibExt.Probability.Causality.sum_powersetCard_ite_mem (ι := Fin t) a j
  have hsum : ∑ S ∈ Finset.univ.powersetCard a, affectedAlleleCount x S =
      ∑ j, x j * ∑ S ∈ Finset.univ.powersetCard a, (if j ∈ S then (1 : ℝ) else 0) := by
    calc ∑ S ∈ Finset.univ.powersetCard a, affectedAlleleCount x S
        = ∑ S ∈ Finset.univ.powersetCard a, ∑ j, (if j ∈ S then x j else 0) :=
          Finset.sum_congr rfl fun S _ => by
            rw [affectedAlleleCount, Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ j, ∑ S ∈ Finset.univ.powersetCard a, (if j ∈ S then x j else 0) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun j _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun S _ => by split_ifs <;> simp
  rw [randExp, hsum, Fintype.card_fin]
  simp_rw [hcount]
  rw [← Finset.sum_mul, div_eq_iff hC]
  field_simp

open MathlibExt.Probability.Causality (ate diffInMeans popMean popVar sampleMean)

/-- **Null variance of the S-TDT count** (Spielman and Ewens 1998). Let a sibship have `t ≥ 2`
sibs, `a ≤ t` of them affected and `u = t - a` unaffected, and let `x_j ∈ ℝ` be the number of
tested alleles of sib `j`, with `r = ∑_j x_j` and `s = ∑_j x_j²`. If the set of affected sibs
is uniformly distributed over the `a`-element subsets of the sibship, the variance of the
number of tested alleles among the affected sibs about its mean `a r / t`, that is `randExp a` of
the squared deviation, is
`a u (t s - r²) / (t² (t - 1))`.

Source: Spielman and Ewens (1998). -/
public theorem randExp_sq_sub_mean {t a : ℕ} (ht : 2 ≤ t) (hat : a ≤ t)
    (x : Fin t → ℝ) :
    randExp a (fun S => (affectedAlleleCount x S - a * (∑ j, x j) / t) ^ 2) =
      a * (t - a : ℕ) * (t * ∑ j, x j ^ 2 - (∑ j, x j) ^ 2) / ((t : ℝ) ^ 2 * (t - 1)) := by
  classical
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (t : ℝ) ≠ 0 := by linarith
  by_cases ha : a = 0
  · subst a
    simp [randExp, affectedAlleleCount]
  by_cases hfull : a = t
  · subst a
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, zero_div, randExp]
    suffices hzero : ∑ S ∈ (Finset.univ : Finset (Fin t)).powersetCard t,
        (affectedAlleleCount x S - t * (∑ j, x j) / t) ^ 2 = 0 by
      rw [hzero, zero_div]
    refine Finset.sum_eq_zero fun S hS => ?_
    have hcard := (Finset.mem_powersetCard.mp hS).2
    have hUniv : S = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      simp [hcard])
    rw [hUniv, affectedAlleleCount, mul_comm (t : ℝ), mul_div_cancel_right₀ _ ht0, sub_self]
    norm_num
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht1 : (t : ℝ) - 1 ≠ 0 := by linarith
  let y : Fin t → ℝ := fun j => a * x j
  -- On the support of the randomization, the treated mean of `a * x` is the affected sum.
  have hdiff (S : Finset (Fin t)) (hS : S ∈ Finset.univ.powersetCard a) :
      diffInMeans (fun _ => 0) y S = affectedAlleleCount x S := by
    have hcard := (Finset.mem_powersetCard.mp hS).2
    simp only [diffInMeans, sampleMean, Finset.sum_const_zero, zero_div, sub_zero, y,
      ← Finset.mul_sum, hcard, affectedAlleleCount]
    rw [mul_comm (a : ℝ), mul_div_cancel_right₀ _ ha0]
  have hmean : ate (fun _ => 0) y = a * (∑ j, x j) / t := by
    simp only [ate, popMean, sub_zero, y, ← Finset.mul_sum, Fintype.card_fin]
  have hvar := MathlibExt.Probability.Causality.randExp_sq_diffInMeans_sub_ate
    (fun _ => 0) y (n₁ := a) (by omega) (by simpa only [Fintype.card_fin] using
      (show a + 1 ≤ t by omega))
  simp only [sub_zero, Fintype.card_fin, hmean] at hvar
  calc
    _ = randExp a (fun S => (diffInMeans (fun _ => 0) y S - a * (∑ j, x j) / t) ^ 2) := by
      unfold randExp
      congr 1
      exact Finset.sum_congr rfl fun S hS => by simp only [hdiff S hS]
    _ = _ := by
      rw [hvar]
      have hzero : popVar (fun _ : Fin t => (0 : ℝ)) = 0 := by
        simp [popVar, popMean]
      have hpop : popVar y =
          ((∑ j, y j ^ 2) - (∑ j, y j) ^ 2 / t) / ((t : ℝ) - 1) := by
        simp only [popVar, popMean, Fintype.card_fin]
        congr 1
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum,
          ← Finset.sum_mul]
        field_simp [ht0]
        ring
      rw [hzero, zero_div, add_zero, hpop, Nat.cast_sub hat]
      simp only [y, mul_pow, ← Finset.mul_sum]
      field_simp [ha0, ht0, ht1]

end WantedExt.Biology.StatisticalGenetics.SibTransmissionDisequilibriumWanted
