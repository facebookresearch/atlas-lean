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

Here the equally-likely-subset null is the model; the two moment identities are the wanted
statements. They hold for arbitrary real scores `x_j`, in particular for allele counts in
`{0, 1, 2}`.

Sources: R. S. Spielman and W. J. Ewens, "A sibship test for linkage in the presence of
association: the sib transmission/disequilibrium test", Am. J. Hum. Genet. 62 (1998) 450–458.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SibTransmissionDisequilibriumWanted

/-- The number of tested alleles carried by the sibs in `S`, the affected sibs. -/
def affectedAlleleCount {t : ℕ} (x : Fin t → ℝ) (S : Finset (Fin t)) : ℝ :=
  ∑ j ∈ S, x j

/-- The average of `f` over all `a`-element subsets of the `t` sibs, each subset equally likely
(the S-TDT null distribution of the set of affected sibs). -/
noncomputable def subsetAverage {t : ℕ} (a : ℕ) (f : Finset (Fin t) → ℝ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin t)).powersetCard a, f S) / (t.choose a : ℝ)

/-- **Null mean of the S-TDT count** (Spielman and Ewens 1998). Let a sibship have `t ≥ 1`
sibs, `a ≤ t` of them affected, and let `x_j ∈ ℝ` be the number of tested alleles of sib `j`.
If the set of affected sibs is uniformly distributed over the `a`-element subsets of the
sibship, the expected number of tested alleles among the affected sibs is `a r / t`, where
`r = ∑_j x_j`.

Source: Spielman and Ewens (1998). -/
public theorem_wanted subsetAverage_affectedAlleleCount {t a : ℕ} (ht : 0 < t) (hat : a ≤ t)
    (x : Fin t → ℝ) :
    subsetAverage a (affectedAlleleCount x) = a * (∑ j, x j) / t

/-- **Null variance of the S-TDT count** (Spielman and Ewens 1998). Let a sibship have `t ≥ 2`
sibs, `a ≤ t` of them affected and `u = t - a` unaffected, and let `x_j ∈ ℝ` be the number of
tested alleles of sib `j`, with `r = ∑_j x_j` and `s = ∑_j x_j²`. If the set of affected sibs
is uniformly distributed over the `a`-element subsets of the sibship, the variance of the
number of tested alleles among the affected sibs about its mean `a r / t` is
`a u (t s - r²) / (t² (t - 1))`.

Source: Spielman and Ewens (1998). -/
public theorem_wanted subsetAverage_sq_sub_mean {t a : ℕ} (ht : 2 ≤ t) (hat : a ≤ t)
    (x : Fin t → ℝ) :
    subsetAverage a (fun S => (affectedAlleleCount x S - a * (∑ j, x j) / t) ^ 2) =
      a * (t - a : ℕ) * (t * ∑ j, x j ^ 2 - (∑ j, x j) ^ 2) / ((t : ℝ) ^ 2 * (t - 1))

end WantedExt.Biology.StatisticalGenetics.SibTransmissionDisequilibriumWanted
