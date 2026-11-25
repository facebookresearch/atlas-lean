/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Image
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Founder sampling: allele loss and expected allelic richness

A founder sample of `k` gene copies is drawn independently with replacement from a source
population with allele frequencies `p : A -> R` on a finite allele type `A`. An ordered sample
`s : Fin k -> A` has weight `sampleWeight p s = prod j, p (s j)`, its probability under
admissible frequencies. The alleles it retains are `retainedAlleles s`, the image of the tuple.

## Main results

* `sum_sampleWeight`: the sample weights sum to `1`.
* `probAbsent_eq`: the probability that allele `i` is absent (lost in the founder event) is
  `(1 - p i) ^ k`.
* `expectedRichness_eq`: the expected number of distinct retained alleles is
  `sum i, (1 - (1 - p i) ^ k)`. This is the allelic richness `a_g` of Kalinowski (2004) at
  `g = k`, with the with-replacement absence probability; the without-replacement
  (hypergeometric) rarefaction formula is a different statement and is not proved here.
* `expectedRichness_zero`, `expectedRichness_nonneg`, `expectedRichness_mono`: the `k = 0`
  boundary, nonnegativity, and monotonicity in the founder sample size.

The three identities need only `sum p = 1`; admissibility (`0 <= p i`) is assumed only for the
sign and monotonicity statements.

## References

* S. T. Kalinowski, *Counting alleles with rarefaction: private alleles and hierarchical
  sampling designs*, Conservation Genetics 5 (2004), 539-543.
* S. H. Hurlbert, *The nonconcept of species diversity: a critique and alternative
  parameters*, Ecology 52 (1971), 577-586.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.FounderSampling

/-- Weight of one ordered founder sample `s` of `k` gene copies drawn
independently with replacement from a source population with allele
frequencies `p`: the product of the frequencies of the drawn copies. Under
admissible frequencies (`0 <= p`, `sum p = 1` on a finite allele type) this
is the probability of the sample `s`. -/
def sampleWeight {A : Type*} (p : A → ℝ) {k : ℕ} (s : Fin k → A) : ℝ :=
  ∏ j, p (s j)

/-- The set of alleles retained in a founder sample `s`: the image of the
sample tuple. -/
def retainedAlleles {A : Type*} [DecidableEq A] {k : ℕ} (s : Fin k → A) :
    Finset A :=
  Finset.univ.image s

/-- Total sample weight of samples in which allele `i` is absent from a
founder sample of `k` gene copies drawn independently with replacement
from frequencies `p`. Under admissible frequencies (`0 <= p`, `sum p = 1`)
this weight is the absence probability. -/
def probAbsent {A : Type*} [Fintype A] [DecidableEq A] (p : A → ℝ) (k : ℕ)
    (i : A) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin k → A)).filter
    (fun s => i ∉ retainedAlleles s), sampleWeight p s

/-- Expected number of distinct alleles retained in a founder sample of
`k` gene copies drawn independently with replacement from frequencies
`p`: the sample-weight average of the number of distinct alleles in the
sample. Under admissible frequencies (`0 <= p`, `sum p = 1`) the weights
are probabilities and this is an expectation. This is the allelic richness
`a_g` of Kalinowski (2004) at
`g = k`, for with-replacement (binomial) founder sampling. -/
def expectedRichness {A : Type*} [Fintype A] [DecidableEq A] (p : A → ℝ)
    (k : ℕ) : ℝ :=
  ∑ s : Fin k → A, sampleWeight p s * (retainedAlleles s).card

/-- A sum of product weights over tuples with every coordinate in `s`
factors as a product of coordinate sums. -/
private theorem sum_weight_piFinset {A : Type*} (p : A → ℝ) (k : ℕ) (s : Finset A) :
    (∑ f ∈ Fintype.piFinset (fun _ : Fin k => s), ∏ j, p (f j))
      = ∏ _j : Fin k, ∑ a ∈ s, p a :=
  Finset.sum_prod_piFinset s (fun _ a => p a)

/-- The sample weights of all ordered founder samples of `k` gene copies
sum to `1` when the frequencies sum to `1`. -/
theorem sum_sampleWeight {A : Type*} [Fintype A] (p : A → ℝ)
    (hsum : ∑ a, p a = 1) (k : ℕ) :
    ∑ s : Fin k → A, sampleWeight p s = 1 := by
  unfold sampleWeight
  have huniv : (Finset.univ : Finset (Fin k → A))
      = Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset A)) :=
    Fintype.piFinset_univ.symm
  rw [huniv, sum_weight_piFinset]
  simp [hsum]

/-- **Allele loss under founder sampling.** For frequencies with
`sum p = 1` (of any sign), the absence weight of allele `i` in a founder
sample of `k` gene copies drawn independently with replacement is
`(1 - p i) ^ k`; for admissible frequencies (also `0 <= p`) it is the
probability that `i` is absent. -/
theorem probAbsent_eq {A : Type*} [Fintype A] [DecidableEq A] (p : A → ℝ)
    (hsum : ∑ a, p a = 1) (k : ℕ) (i : A) :
    probAbsent p k i = (1 - p i) ^ k := by
  unfold probAbsent
  unfold sampleWeight
  have hset : (Finset.univ : Finset (Fin k → A)).filter
        (fun s => i ∉ retainedAlleles s)
      = Fintype.piFinset (fun _ : Fin k => (Finset.univ.erase i : Finset A)) := by
    ext s
    simp [retainedAlleles, Fintype.mem_piFinset]
  rw [hset, sum_weight_piFinset]
  have h1 : (∑ a ∈ (Finset.univ.erase i : Finset A), p a) = 1 - p i := by
    have hadd :=
      Finset.add_sum_erase (Finset.univ : Finset A) p (Finset.mem_univ i)
    rw [hsum] at hadd
    linarith
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Expected allelic richness under founder sampling.** For frequencies
with `sum p = 1` (of any sign; an expectation when also `0 <= p`), the
expected number of distinct alleles retained in a founder sample of `k`
gene copies drawn independently with replacement is
`∑ i, (1 - (1 - p i) ^ k)`, the sum over alleles of the retention
probability `1 - Q i` of Kalinowski (2004), with the with-replacement
absence probability `Q i = (1 - p i) ^ k`. -/
theorem expectedRichness_eq {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) (hsum : ∑ a, p a = 1) (k : ℕ) :
    expectedRichness p k = ∑ i, (1 - (1 - p i) ^ k) := by
  have hcard : ∀ s : Fin k → A, ((retainedAlleles s).card : ℝ)
      = ∑ i, (if i ∈ retainedAlleles s then (1 : ℝ) else 0) := by
    intro s
    have h1 : ((Finset.univ : Finset A).filter (fun i => i ∈ retainedAlleles s))
        = retainedAlleles s := by
      ext i
      simp
    have h2 : (∑ i, (if i ∈ retainedAlleles s then (1 : ℝ) else 0))
        = ∑ i ∈ (Finset.univ : Finset A).filter
          (fun i => i ∈ retainedAlleles s), 1 := by
      rw [Finset.sum_filter]
    rw [h2, h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold expectedRichness
  calc (∑ s : Fin k → A, sampleWeight p s * ((retainedAlleles s).card : ℝ))
      = ∑ s : Fin k → A, ∑ i : A,
          sampleWeight p s * (if i ∈ retainedAlleles s then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hcard s, Finset.mul_sum]
    _ = ∑ i : A, ∑ s : Fin k → A,
          sampleWeight p s * (if i ∈ retainedAlleles s then (1 : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ i, (1 - (1 - p i) ^ k) := by
        apply Finset.sum_congr rfl
        intro i _
        have hfilt : (∑ s : Fin k → A,
              sampleWeight p s * (if i ∈ retainedAlleles s then (1 : ℝ) else 0))
            = ∑ s ∈ (Finset.univ : Finset (Fin k → A)).filter
              (fun s => i ∈ retainedAlleles s), sampleWeight p s := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : i ∈ retainedAlleles s <;> simp [h]
        rw [hfilt]
        have htot := sum_sampleWeight p hsum k
        have habs := probAbsent_eq p hsum k i
        have hsplit := Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (Fin k → A))
          (fun s => i ∈ retainedAlleles s) (fun s => sampleWeight p s)
        unfold probAbsent at habs
        have hsplit' : (∑ s ∈ (Finset.univ : Finset (Fin k → A)).filter
              (fun s => i ∈ retainedAlleles s), sampleWeight p s)
            + (∑ s ∈ (Finset.univ : Finset (Fin k → A)).filter
              (fun s => ¬ i ∈ retainedAlleles s), sampleWeight p s)
            = ∑ s : Fin k → A, sampleWeight p s := hsplit
        have habs' : (∑ s ∈ (Finset.univ : Finset (Fin k → A)).filter
              (fun s => ¬ i ∈ retainedAlleles s), sampleWeight p s)
            = (1 - p i) ^ k := habs
        linarith

/-- A founder sample of `0` gene copies retains no allele: the expected
retained richness at `k = 0` is `0`, for arbitrary frequencies. -/
theorem expectedRichness_zero {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) :
    expectedRichness p 0 = 0 := by
  unfold expectedRichness
  apply Finset.sum_eq_zero
  intro s _
  have hcard : (retainedAlleles s).card = 0 := by
    unfold retainedAlleles
    rw [Finset.univ_eq_empty, Finset.image_empty, Finset.card_empty]
  rw [hcard, Nat.cast_zero, mul_zero]

/-- The expected retained richness is nonnegative for admissible
(nonnegative) frequencies. -/
theorem expectedRichness_nonneg {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ) :
    0 ≤ expectedRichness p k := by
  unfold expectedRichness
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg
  · unfold sampleWeight
    apply Finset.prod_nonneg
    intro j _
    exact hp (s j)
  · exact Nat.cast_nonneg _

/-- The expected retained richness is nondecreasing in the founder
sample size `k` for admissible frequencies (`0 <= p`, `sum p = 1`): a
larger founder sample retains at least as many alleles in expectation. -/
theorem expectedRichness_mono {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ a, p a = 1) (k : ℕ) :
    expectedRichness p k ≤ expectedRichness p (k + 1) := by
  rw [expectedRichness_eq p hsum k, expectedRichness_eq p hsum (k + 1)]
  apply Finset.sum_le_sum
  intro i _
  have hpi0 : 0 ≤ p i := hp i
  have hpi1 : p i ≤ 1 := by
    have h := Finset.single_le_sum (fun a _ => hp a) (Finset.mem_univ i)
    rw [hsum] at h
    exact h
  have hpow : (1 - p i) ^ (k + 1) ≤ (1 - p i) ^ k :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_add_right k 1)
  linarith

end MathlibExt.Biology.PopulationGenetics.FounderSampling
