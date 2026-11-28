/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Independence.Basic

import Mathlib.MeasureTheory.Measure.Real
import MathlibExt.Probability.Distributions.BinomialEventCount
import MathlibExt.Probability.Independence.Blocks

/-!
# Binomial discovery probability of rare alleles and genotypes

Wendl and Wilson (2009) compute the probability that a sequencing project discovers a rare
variant. The variant has population frequency `φ`: a minor allele frequency, or the frequency of
a rare homozygous genotype. Each of `σ` independently sampled diploid genomes is sequenced
separately to the same haploid redundancy `ρ`, and `c = c(ρ, τ)` is the probability that the
variant's position on a given chromosome is spanned by at least `τ` reads, the threshold that
controls sequencing error. Coverage is the same for both chromosomes, independent across them and
independent of the variant's presence. The variant is discovered if it is detected in at least
`N` samples.

In sample `i`, the event `A i j` says that chromosome `j` carries the allele and `C i j` that the
variant's position on chromosome `j` is covered at least `τ` times; for a rare genotype, `G i`
says that sample `i` has the genotype. An allele is detected in sample `i` on
`(A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)`, and a genotype on `G i ∩ C i 0 ∩ C i 1`, since it is called
only when both chromosomes are covered. All these events are mutually independent: the samples
are independent, and within a sample the alleles (or the genotype) and the coverage of the two
chromosomes are independent of one another. The detection events of different samples are then
independent (`ProbabilityTheory.iIndepSet.iIndepSet_of_measurableSet_generateFrom`), each of
probability `2 φ c - φ ^ 2 c ^ 2` for a rare allele, by inclusion–exclusion, and `φ c ^ 2` for a
rare genotype. So the number `K` of samples in which the variant is detected is binomial, and the
discovery probability `P(K ≥ N)` is a binomial upper tail
(`ProbabilityTheory.iIndepSet.measureReal_ncard_eq`,
`ProbabilityTheory.iIndepSet.measureReal_le_ncard`).

The coverage model enters only through `c`: the formulas hold for any coverage events `C i j` of
probability `c` that satisfy the independence assumptions.

## Main results

* `binomial_discovery_probability`: Theorems 1 and 2 of Wendl and Wilson (2009), the detection
  probabilities of a rare allele and of a rare genotype in one sample, the binomial law of the
  number of samples in which the variant is detected, and the discovery probability.

## References

* M. C. Wendl, R. K. Wilson, *The theory of discovering rare variants via DNA sequencing*,
  BMC Genomics 10 (2009), 485, Theorems 1 and 2. <https://doi.org/10.1186/1471-2164-10-485>
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace Domains.Biology.StatisticalGenetics.RareVariantDiscovery

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The real probability of a finite intersection of independent events is the product of their
real probabilities. -/
private lemma measureReal_biInter {J : Type*} {P : Measure Ω} {E : J → Set Ω}
    (h : iIndepSet E P) (S : Finset J) :
    P.real (⋂ x ∈ S, E x) = ∏ x ∈ S, P.real (E x) := by
  simp [measureReal_def, h.meas_biInter S, ENNReal.toReal_prod]

/-- Theorem 1 of Wendl and Wilson (2009): rare alleles. -/
private theorem rareAllele {P : Measure Ω} {σ : ℕ} {φ c : ℝ} (A C : Fin σ → Fin 2 → Set Ω)
    (hA : ∀ i j, MeasurableSet (A i j)) (hC : ∀ i j, MeasurableSet (C i j))
    (h : iIndepSet (Sum.elim (Function.uncurry A) (Function.uncurry C)) P)
    (hφ : ∀ i j, P.real (A i j) = φ) (hc : ∀ i j, P.real (C i j) = c) :
    (∀ i, P.real ((A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)) = 2 * φ * c - φ ^ 2 * c ^ 2) ∧
    (∀ k, P.real {ω | {i | ω ∈ (A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)}.ncard = k} =
      σ.choose k * (2 * φ * c - φ ^ 2 * c ^ 2) ^ k *
        (1 - (2 * φ * c - φ ^ 2 * c ^ 2)) ^ (σ - k)) ∧
    ∀ N, P.real {ω | N ≤ {i | ω ∈ (A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)}.ncard} =
      ∑ k ∈ Finset.Icc N σ, (σ.choose k : ℝ) * (2 * φ * c - φ ^ 2 * c ^ 2) ^ k *
        (1 - (2 * φ * c - φ ^ 2 * c ^ 2)) ^ (σ - k) := by
  have := h.isProbabilityMeasure
  set E := Sum.elim (Function.uncurry A) (Function.uncurry C) with hE_def
  have hE : ∀ x, MeasurableSet (E x) := by
    rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact hA i j
    · exact hC i j
  have hD : ∀ i, MeasurableSet ((A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)) := fun i =>
    ((hA i 0).inter (hC i 0)).union ((hA i 1).inter (hC i 1))
  have hprob (i : Fin σ) :
      P.real ((A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)) = 2 * φ * c - φ ^ 2 * c ^ 2 := by
    have h2 (j : Fin 2) : P.real (A i j ∩ C i j) = φ * c := by
      have := measureReal_biInter h {Sum.inl (i, j), Sum.inr (i, j)}
      simpa [E, hφ, hc] using this
    have h4 : P.real ((A i 0 ∩ C i 0) ∩ (A i 1 ∩ C i 1)) = φ ^ 2 * c ^ 2 := by
      have := measureReal_biInter h
        {Sum.inl (i, 0), Sum.inr (i, 0), Sum.inl (i, 1), Sum.inr (i, 1)}
      simp only [Finset.set_biInter_insert, Finset.set_biInter_singleton, hE_def, Sum.elim_inl,
        Sum.elim_inr, Function.uncurry_apply_pair] at this
      rw [Set.inter_assoc, this]
      simp [hφ, hc]
      ring
    have := measureReal_union_add_inter (μ := P) (s := A i 0 ∩ C i 0)
      ((hA i 1).inter (hC i 1))
    linarith [h2 0, h2 1]
  have hind : iIndepSet (fun i => (A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)) P := by
    refine h.iIndepSet_of_measurableSet_generateFrom hE (Sum.elim Prod.fst Prod.fst)
      fun i => ?_
    have hmem (x) (hx : Sum.elim Prod.fst Prod.fst x = i) :
        MeasurableSet[generateFrom (E '' (Sum.elim Prod.fst Prod.fst ⁻¹' {i}))] (E x) :=
      measurableSet_generateFrom ⟨x, hx, rfl⟩
    exact ((hmem (.inl (i, 0)) rfl).inter (hmem (.inr (i, 0)) rfl)).union
      ((hmem (.inl (i, 1)) rfl).inter (hmem (.inr (i, 1)) rfl))
  exact ⟨hprob, hind.measureReal_ncard_eq hD hprob, hind.measureReal_le_ncard hD hprob⟩

/-- Theorem 2 of Wendl and Wilson (2009): rare genotypes. -/
private theorem rareGenotype {P : Measure Ω} {σ : ℕ} {φ c : ℝ} (G : Fin σ → Set Ω)
    (C : Fin σ → Fin 2 → Set Ω) (hG : ∀ i, MeasurableSet (G i))
    (hC : ∀ i j, MeasurableSet (C i j)) (h : iIndepSet (Sum.elim G (Function.uncurry C)) P)
    (hφ : ∀ i, P.real (G i) = φ) (hc : ∀ i j, P.real (C i j) = c) :
    (∀ i, P.real (G i ∩ C i 0 ∩ C i 1) = φ * c ^ 2) ∧
    (∀ k, P.real {ω | {i | ω ∈ G i ∩ C i 0 ∩ C i 1}.ncard = k} =
      σ.choose k * (φ * c ^ 2) ^ k * (1 - φ * c ^ 2) ^ (σ - k)) ∧
    ∀ N, P.real {ω | N ≤ {i | ω ∈ G i ∩ C i 0 ∩ C i 1}.ncard} =
      ∑ k ∈ Finset.Icc N σ, (σ.choose k : ℝ) * (φ * c ^ 2) ^ k * (1 - φ * c ^ 2) ^ (σ - k) := by
  have := h.isProbabilityMeasure
  set E := Sum.elim G (Function.uncurry C) with hE_def
  have hE : ∀ x, MeasurableSet (E x) := by
    rintro (i | ⟨i, j⟩)
    · exact hG i
    · exact hC i j
  have hD : ∀ i, MeasurableSet (G i ∩ C i 0 ∩ C i 1) := fun i =>
    ((hG i).inter (hC i 0)).inter (hC i 1)
  have hprob (i : Fin σ) : P.real (G i ∩ C i 0 ∩ C i 1) = φ * c ^ 2 := by
    have := measureReal_biInter h {Sum.inl i, Sum.inr (i, 0), Sum.inr (i, 1)}
    simp only [Finset.set_biInter_insert, Finset.set_biInter_singleton, hE_def, Sum.elim_inl,
      Sum.elim_inr, Function.uncurry_apply_pair] at this
    rw [Set.inter_assoc, this, Finset.prod_insert (by simp), Finset.prod_pair (by simp)]
    simp only [Sum.elim_inl, Sum.elim_inr, Function.uncurry_apply_pair, hφ, hc]
    ring
  have hind : iIndepSet (fun i => G i ∩ C i 0 ∩ C i 1) P := by
    refine h.iIndepSet_of_measurableSet_generateFrom hE (Sum.elim id Prod.fst) fun i => ?_
    have hmem (x) (hx : Sum.elim id Prod.fst x = i) :
        MeasurableSet[generateFrom (E '' (Sum.elim id Prod.fst ⁻¹' {i}))] (E x) :=
      measurableSet_generateFrom ⟨x, hx, rfl⟩
    exact ((hmem (.inl i) rfl).inter (hmem (.inr (i, 0)) rfl)).inter (hmem (.inr (i, 1)) rfl)
  exact ⟨hprob, hind.measureReal_ncard_eq hD hprob, hind.measureReal_le_ncard hD hprob⟩

/-- **Binomial discovery probability of rare alleles and genotypes** (Wendl and Wilson 2009,
Theorems 1 and 2). Let $P$ be a measure on $\Omega$, let $\sigma$ be the number of sampled
diploid genomes, $\varphi$ the population frequency of a rare variant, and $c$ the probability
that the variant's position on a chromosome is spanned by at least $\tau$ reads.

1. *Rare alleles.* For each sample $i < \sigma$ and chromosome $j \in \{0, 1\}$, let $A_{ij}$ be
   the event that chromosome $j$ of sample $i$ carries the allele and $C_{ij}$ the event that the
   variant's position on it is covered, with $P(A_{ij}) = \varphi$ and $P(C_{ij}) = c$, and
   suppose that these $4\sigma$ events are measurable and mutually independent. Then the allele
   is detected in sample $i$, on $D_i = (A_{i0} \cap C_{i0}) \cup (A_{i1} \cap C_{i1})$, with
   probability $q_A = 2\varphi c - \varphi^2 c^2$. The number
   $K(\omega) = \#\{i : \omega \in D_i\}$ of samples in which it is detected is binomial,
   $P(K = k) = \binom{\sigma}{k} q_A^k (1 - q_A)^{\sigma - k}$ for every $k \in \mathbb{N}$, and
   the discovery probability is
   $$P(K \ge N) = \sum_{k=N}^{\sigma} \binom{\sigma}{k} q_A^k (1 - q_A)^{\sigma - k}$$
   for every $N \in \mathbb{N}$.
2. *Rare genotypes.* Let $G_i$ be the event that sample $i$ has the rare genotype and $C_{ij}$ as
   above, with $P(G_i) = \varphi$ and $P(C_{ij}) = c$, and suppose that these $3\sigma$ events
   are measurable and mutually independent. Then the genotype is detected in sample $i$, on
   $G_i \cap C_{i0} \cap C_{i1}$, with probability $q_G = \varphi c^2$, and the number of samples
   in which it is detected has the same binomial law and upper tail with $q_G$ in place of $q_A$.

Mutual independence of all the events says that the samples are independent and that, within a
sample, the alleles of the two chromosomes (or the genotype) and the coverage of the two
chromosomes are independent of one another; it makes $P$ a probability measure. -/
theorem binomial_discovery_probability (P : Measure Ω) (σ : ℕ) (φ c : ℝ) :
    (∀ A C : Fin σ → Fin 2 → Set Ω, (∀ i j, MeasurableSet (A i j)) →
      (∀ i j, MeasurableSet (C i j)) →
      iIndepSet (Sum.elim (Function.uncurry A) (Function.uncurry C)) P →
      (∀ i j, P.real (A i j) = φ) → (∀ i j, P.real (C i j) = c) →
      (∀ i, P.real ((A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)) = 2 * φ * c - φ ^ 2 * c ^ 2) ∧
      (∀ k, P.real {ω | {i | ω ∈ (A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)}.ncard = k} =
        σ.choose k * (2 * φ * c - φ ^ 2 * c ^ 2) ^ k *
          (1 - (2 * φ * c - φ ^ 2 * c ^ 2)) ^ (σ - k)) ∧
      ∀ N, P.real {ω | N ≤ {i | ω ∈ (A i 0 ∩ C i 0) ∪ (A i 1 ∩ C i 1)}.ncard} =
        ∑ k ∈ Finset.Icc N σ, (σ.choose k : ℝ) * (2 * φ * c - φ ^ 2 * c ^ 2) ^ k *
          (1 - (2 * φ * c - φ ^ 2 * c ^ 2)) ^ (σ - k)) ∧
    (∀ (G : Fin σ → Set Ω) (C : Fin σ → Fin 2 → Set Ω), (∀ i, MeasurableSet (G i)) →
      (∀ i j, MeasurableSet (C i j)) → iIndepSet (Sum.elim G (Function.uncurry C)) P →
      (∀ i, P.real (G i) = φ) → (∀ i j, P.real (C i j) = c) →
      (∀ i, P.real (G i ∩ C i 0 ∩ C i 1) = φ * c ^ 2) ∧
      (∀ k, P.real {ω | {i | ω ∈ G i ∩ C i 0 ∩ C i 1}.ncard = k} =
        σ.choose k * (φ * c ^ 2) ^ k * (1 - φ * c ^ 2) ^ (σ - k)) ∧
      ∀ N, P.real {ω | N ≤ {i | ω ∈ G i ∩ C i 0 ∩ C i 1}.ncard} =
        ∑ k ∈ Finset.Icc N σ, (σ.choose k : ℝ) * (φ * c ^ 2) ^ k * (1 - φ * c ^ 2) ^ (σ - k)) :=
  ⟨fun A C hA hC h hφ hc => rareAllele A C hA hC h hφ hc,
    fun G C hG hC h hφ hc => rareGenotype G C hG hC h hφ hc⟩

end Domains.Biology.StatisticalGenetics.RareVariantDiscovery
