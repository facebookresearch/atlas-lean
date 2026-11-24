/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.GlobalAncestryBridge
public import Domains.Biology.PopulationGenetics.ADMIXTOOLS

/-!
# Global ancestry as frequencies for f-statistics

The global-ancestry model assigns to individual `i` at locus `j` the
frequency `∑ k, Q i k * F k j`. Viewing loci as the sample space and
individuals and ancestral populations as populations, each individual is an
exact affine mixture of the ancestral populations, with zero private drift,
whenever each row of `Q` sums to `1`. No positivity assumption on `Q` or `F`
is used for the f-statistic conclusions. F4 linearity therefore applies to
individuals, and the individual-level qpWave matrix has rank at most `K - 1`
for `K` ancestral populations.

The raw `Q`/`F` form is stated first; the `AdmixtureEM.Params` form follows
from its row-sum field. The drift-model frequency form of the same
zero-private-drift identity is
`FStatistics.DriftModel.freq_eq_sum_of_weight_eq_sum` in `ADMIXTOOLS`.

## Main results

* `ancestryFreqOf`: individuals and ancestral populations as one frequency
  family over loci, from raw ancestry proportions `Q` and frequencies `F`.
* `f4_ancestryFreqOf_individual` and `rank_f4Matrix_ancestryFreqOf_le`: f4
  linearity and the qpWave bound under only the row-sum hypothesis.
* `ancestryFreq`, `f4_ancestryFreq_individual` and
  `rank_f4Matrix_ancestryFreq_le`: the corresponding statements for
  `AdmixtureEM.Params`.

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

variable {mJ : MeasurableSpace J} {μ : Measure J}

/-- F4 linearity for individuals from raw global-ancestry data, for
square-integrable frequencies. Besides square integrability, only the
row-sum hypothesis `∑ k, Q i k = 1` is used (no sign condition). -/
theorem f4_ancestryFreqOf_individual (Q : I → K → ℝ) (F : K → J → ℝ)
    (hQ : ∀ i, ∑ k, Q i k = 1)
    (hp : ∀ X, MemLp (ancestryFreqOf Q F X) 2 μ) (i : I) (X Y Z : I ⊕ K) :
    f4 μ (ancestryFreqOf Q F) (Sum.inl i) X Y Z =
      ∑ k, Q i k * f4 μ (ancestryFreqOf Q F) (Sum.inr k) X Y Z :=
  f4_affine_combination hp Sum.inr (Q i) (hQ i)
    (fun j => ancestryFreqOf_inl_eq_sum Q F i j)

/-- QpWave bound for raw global-ancestry data: with individuals
`Fin (n + 1)` as left populations and `Fin (k + 1)` ancestral populations,
the individual-level f4 matrix against arbitrary right populations has rank
at most `k`, assuming only that every `Q` row sums to `1` and that the
frequencies are square integrable. -/
theorem rank_f4Matrix_ancestryFreqOf_le {n r k : ℕ}
    (Q : Fin (n + 1) → Fin (k + 1) → ℝ) (F : Fin (k + 1) → J → ℝ)
    (hQ : ∀ i, ∑ l, Q i l = 1)
    (hp : ∀ X, MemLp (ancestryFreqOf Q F X) 2 μ)
    (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreqOf Q F) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_le hp Sum.inl R Sum.inr Q hQ
    (fun i j => ancestryFreqOf_inl_eq_sum Q F i j)

/-- The raw rank bound (rank at most `k` when every `Q` row sums to `1`) over
finitely many loci, every subset measurable, with a finite measure (in
particular the counting measure), where square integrability is automatic. -/
theorem rank_f4Matrix_ancestryFreqOf_le_of_finite {n r k : ℕ} [Finite J]
    [DiscreteMeasurableSpace J] [IsFiniteMeasure μ]
    (Q : Fin (n + 1) → Fin (k + 1) → ℝ) (F : Fin (k + 1) → J → ℝ)
    (hQ : ∀ i, ∑ l, Q i l = 1) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreqOf Q F) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreqOf_le Q F hQ (fun _ => MemLp.of_discrete) R

/-- F4 linearity for individuals of the `AdmixtureEM` model, for
square-integrable frequencies. The strict positivity fields of `Params` are
not used; only `θ.Q_sum` enters. -/
theorem f4_ancestryFreq_individual (θ : Params I J K)
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (i : I) (X Y Z : I ⊕ K) :
    f4 μ (ancestryFreq θ) (Sum.inl i) X Y Z =
      ∑ k, θ.Q i k * f4 μ (ancestryFreq θ) (Sum.inr k) X Y Z :=
  f4_ancestryFreqOf_individual θ.Q θ.F (fun i => θ.Q_sum i) hp i X Y Z

/-- QpWave bound for the `AdmixtureEM` model, in `k = K - 1` form: for
square-integrable frequencies, the individual-level f4 matrix against
arbitrary right populations has rank at most `k`. -/
theorem rank_f4Matrix_ancestryFreq_le {n r k : ℕ} (θ : Params (Fin (n + 1)) J (Fin (k + 1)))
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreqOf_le θ.Q θ.F (fun i => θ.Q_sum i) hp R

/-- The `Params` rank bound (rank at most `k`) over finitely many loci, every
subset measurable, with a finite measure. -/
theorem rank_f4Matrix_ancestryFreq_le_of_finite {n r k : ℕ} [Finite J]
    [DiscreteMeasurableSpace J] [IsFiniteMeasure μ]
    (θ : Params (Fin (n + 1)) J (Fin (k + 1))) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreq_le θ (fun _ => MemLp.of_discrete) R

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
