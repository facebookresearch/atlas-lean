/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.AdmixtureEM
public import MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS

/-!
# Global ancestry as frequencies for f-statistics

The global-ancestry model of `AdmixtureEM` assigns to individual `i` at locus
`j` the frequency `qf θ i j = ∑ k, Q i k * F k j`. Viewing loci as the sample
space and individuals and ancestral populations as populations, each
individual is an exact affine mixture of the ancestral populations, with zero
private drift. F4 linearity therefore applies to individuals, and the
individual-level qpWave matrix has rank at most `K - 1` for `K` ancestral
populations.

This bridge sits beside `AdmixtureEM`, above the MathlibExt f-statistics API.
The drift-model frequency form of the same zero-private-drift identity is
`FStatistics.DriftModel.freq_eq_sum_of_weight_eq_sum` in `ADMIXTOOLS`.

## Main results

* `ancestryFreq`: individuals and ancestral populations as one frequency
  family over loci.
* `ancestryFreq_inl_eq_sum`: an individual's frequency is its `Q`-mixture of
  ancestral frequencies.
* `f4_ancestryFreq_individual`: f4 linearity for individuals.
* `rank_f4Matrix_ancestryFreq_le`: the individual-level qpWave rank bound.

## References

* J. K. Pritchard, M. Stephens and P. Donnelly, *Inference of population
  structure using multilocus genotype data*, Genetics 155 (2000), 945–959.
* D. H. Alexander, J. Novembre and K. Lange, *Fast model-based estimation of
  ancestry in unrelated individuals*, Genome Research 19 (2009), 1655–1664.
* N. Patterson et al., *Ancient admixture in human history*, Genetics 192
  (2012), 1065–1093.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.ADMIXTOOLS
open scoped BigOperators

namespace Cslib.Bioinformatics.PopulationStructure.AdmixtureEM

variable {I J K : Type*} [Fintype K]

/-- Frequencies of the global-ancestry (STRUCTURE/ADMIXTURE) model, viewed
for f-statistics over loci: individuals `i` (as `Sum.inl i`) have frequency
`qf θ i j = ∑ k, Q i k * F k j` at locus `j`, and ancestral populations `k`
(as `Sum.inr k`) have frequency `F k j`. -/
noncomputable def ancestryFreq (θ : Params I J K) : I ⊕ K → J → ℝ
  | Sum.inl i => qf θ i
  | Sum.inr k => θ.F k


@[simp] theorem ancestryFreq_inl (θ : Params I J K) (i : I) :
    ancestryFreq θ (Sum.inl i) = qf θ i := rfl

@[simp] theorem ancestryFreq_inr (θ : Params I J K) (k : K) :
    ancestryFreq θ (Sum.inr k) = θ.F k := rfl

/-- Zero private drift: an individual's frequency is exactly the
`Q i`-mixture of the ancestral frequencies, with no additional term. This is
the definition of `qf`, restated for `ancestryFreq`. -/
theorem ancestryFreq_inl_eq_sum (θ : Params I J K) (i : I) (j : J) :
    ancestryFreq θ (Sum.inl i) j = ∑ k, θ.Q i k * ancestryFreq θ (Sum.inr k) j := rfl

variable {mJ : MeasurableSpace J} {μ : Measure J}

/-- f4 linearity for individuals of the global-ancestry model: for any
measure on loci and any populations `X Y Z` (individuals or ancestral),
`f4(i, X; Y, Z) = ∑ k, Q i k * f4(k, X; Y, Z)`. Only `∑ k, Q i k = 1` is
used; the strict positivity in `Params` is not needed. -/
theorem f4_ancestryFreq_individual (θ : Params I J K)
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (i : I) (X Y Z : I ⊕ K) :
    f4 μ (ancestryFreq θ) (Sum.inl i) X Y Z =
      ∑ k, θ.Q i k * f4 μ (ancestryFreq θ) (Sum.inr k) X Y Z :=
  f4_affine_combination hp Sum.inr (θ.Q i) (θ.Q_sum i)
    (fun j => ancestryFreq_inl_eq_sum θ i j)

/-- qpWave bound for the global-ancestry model, `k = K - 1` form: with
individuals `Fin (n+1)` as left populations and `K = Fin (k+1)` ancestral
populations, the individual-level f4 matrix against arbitrary right
populations has rank at most `k`. -/
theorem rank_f4Matrix_ancestryFreq_le {n r k : ℕ} (θ : Params (Fin (n + 1)) J (Fin (k + 1)))
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_le hp Sum.inl R Sum.inr θ.Q (fun i => θ.Q_sum i)
    (fun i j => ancestryFreq_inl_eq_sum θ i j)

/-- The rank bound over finitely many loci with a finite measure (in
particular the counting measure), where square integrability is automatic. -/
theorem rank_f4Matrix_ancestryFreq_le_of_finite {n r k : ℕ} [Finite J]
    [DiscreteMeasurableSpace J] [IsFiniteMeasure μ]
    (θ : Params (Fin (n + 1)) J (Fin (k + 1))) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreq_le θ (fun _ => MemLp.of_discrete) R

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
