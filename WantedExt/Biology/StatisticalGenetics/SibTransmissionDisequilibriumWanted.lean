/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The sib transmission/disequilibrium test (S-TDT)

The S-TDT compares affected and unaffected sibs within sibships when parental genotypes are
unknown. Under the null hypothesis of no linkage (or no association), the marker genotypes of
the `t` sibs of a sibship are exchangeable with respect to affection status: given the
multiset of sib genotypes, the set of `a` affected sibs is equally likely to be any `a`-subset
of the sibship. Write `x_j` for the number of copies of the tested allele carried by sib `j`,
`r = ∑ x_j`, `s = ∑ x_j²` and `u = t - a`. The count `Y` of tested alleles among the affected
sibs then has conditional mean `a r / t` and conditional variance
`a u (t s - r²) / (t² (t - 1))`. These moments involve only the sibship itself, so the
standardized statistic `(∑ Y - ∑ E[Y]) / √(∑ Var Y)`, summed over independent sibships, is not
affected by population stratification.

Here the equally-likely-subset null is the model, and the null average over `a`-subsets is
`MathlibExt.Probability.Causality.randExp` (the complete-randomization expectation, with the
affected sibs as the treated set). The null mean is proved here; the null variance, whose proof
uses it, is the wanted statement. Both hold for arbitrary real scores `x_j`, in particular for
allele counts in `{0, 1, 2}`.

Sources: R. S. Spielman and W. J. Ewens, "A sibship test for linkage in the presence of
association: the sib transmission/disequilibrium test", Am. J. Hum. Genet. 62 (1998) 450–458.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Causality.CausalIdentification

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

/-- **Null variance of the S-TDT count** (Spielman and Ewens 1998). Let a sibship have `t ≥ 2`
sibs, `a ≤ t` of them affected and `u = t - a` unaffected, and let `x_j ∈ ℝ` be the number of
tested alleles of sib `j`, with `r = ∑_j x_j` and `s = ∑_j x_j²`. If the set of affected sibs
is uniformly distributed over the `a`-element subsets of the sibship, the variance of the
number of tested alleles among the affected sibs about its mean `a r / t`, that is `randExp a` of
the squared deviation, is
`a u (t s - r²) / (t² (t - 1))`.

Source: Spielman and Ewens (1998). -/
public theorem_wanted randExp_sq_sub_mean {t a : ℕ} (ht : 2 ≤ t) (hat : a ≤ t)
    (x : Fin t → ℝ) :
    randExp a (fun S => (affectedAlleleCount x S - a * (∑ j, x j) / t) ^ 2) =
      a * (t - a : ℕ) * (t * ∑ j, x j ^ 2 - (∑ j, x j) ^ 2) / ((t : ℝ) ^ 2 * (t - 1))

end WantedExt.Biology.StatisticalGenetics.SibTransmissionDisequilibriumWanted
