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

The global-ancestry model assigns to individual `i` at locus `j` the
frequency `∑ k, Q i k * F k j`. Viewing loci as the sample space and
individuals and ancestral populations as populations, each individual is an
exact affine mixture of the ancestral populations, with zero private drift,
whenever each row of `Q` sums to `1`. No positivity assumption on `Q` or `F`
is used for the f-statistic conclusions. F4 linearity therefore applies to
individuals, and the individual-level qpWave matrix has rank at most `K - 1`
for `K` ancestral populations.

The raw `Q`/`F` form is stated first; the `AdmixtureEM.Params` form follows
from its row-sum field. This bridge sits beside `AdmixtureEM`, above the
MathlibExt f-statistics API. The drift-model frequency form of the same
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

/-- Frequencies of a global-ancestry model from raw ancestry proportions
`Q` and ancestral frequencies `F`, viewed for f-statistics over loci:
individuals `i` (as `Sum.inl i`) have frequency `∑ k, Q i k * F k j` at locus
`j`, and ancestral populations `k` (as `Sum.inr k`) have frequency `F k j`.
No positivity or boundedness assumption is part of the definition. -/
noncomputable def ancestryFreqOf (Q : I → K → ℝ) (F : K → J → ℝ) : I ⊕ K → J → ℝ
  | Sum.inl i => fun j => ∑ k, Q i k * F k j
  | Sum.inr k => F k

@[simp] theorem ancestryFreqOf_inl (Q : I → K → ℝ) (F : K → J → ℝ) (i : I) :
    ancestryFreqOf Q F (Sum.inl i) = fun j => ∑ k, Q i k * F k j := rfl

@[simp] theorem ancestryFreqOf_inr (Q : I → K → ℝ) (F : K → J → ℝ) (k : K) :
    ancestryFreqOf Q F (Sum.inr k) = F k := rfl

/-- Zero private drift for raw global-ancestry data: an individual's
frequency is exactly the `Q i`-mixture of the ancestral frequencies. -/
theorem ancestryFreqOf_inl_eq_sum (Q : I → K → ℝ) (F : K → J → ℝ) (i : I) (j : J) :
    ancestryFreqOf Q F (Sum.inl i) j = ∑ k, Q i k * ancestryFreqOf Q F (Sum.inr k) j := rfl

variable {mJ : MeasurableSpace J} {μ : Measure J}

/-- F4 linearity for individuals from raw global-ancestry data. Only the
row-sum hypothesis `∑ k, Q i k = 1` is used. -/
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
at most `k`, assuming only that every `Q` row sums to `1`. -/
theorem rank_f4Matrix_ancestryFreqOf_le {n r k : ℕ}
    (Q : Fin (n + 1) → Fin (k + 1) → ℝ) (F : Fin (k + 1) → J → ℝ)
    (hQ : ∀ i, ∑ l, Q i l = 1)
    (hp : ∀ X, MemLp (ancestryFreqOf Q F X) 2 μ)
    (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreqOf Q F) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_le hp Sum.inl R Sum.inr Q hQ
    (fun i j => ancestryFreqOf_inl_eq_sum Q F i j)

/-- The raw rank bound over finitely many loci with a finite measure (in
particular the counting measure), where square integrability is automatic. -/
theorem rank_f4Matrix_ancestryFreqOf_le_of_finite {n r k : ℕ} [Finite J]
    [DiscreteMeasurableSpace J] [IsFiniteMeasure μ]
    (Q : Fin (n + 1) → Fin (k + 1) → ℝ) (F : Fin (k + 1) → J → ℝ)
    (hQ : ∀ i, ∑ l, Q i l = 1) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreqOf Q F) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreqOf_le Q F hQ (fun _ => MemLp.of_discrete) R

/-- Frequencies of the `AdmixtureEM` global-ancestry model over loci:
individuals have frequency `qf θ i j = ∑ k, Q i k * F k j`, and ancestral
populations have frequency `F k j`. This is the `Params` specialization of
`ancestryFreqOf`. -/
noncomputable def ancestryFreq (θ : Params I J K) : I ⊕ K → J → ℝ :=
  ancestryFreqOf θ.Q θ.F

@[simp] theorem ancestryFreq_inl (θ : Params I J K) (i : I) :
    ancestryFreq θ (Sum.inl i) = qf θ i := rfl

@[simp] theorem ancestryFreq_inr (θ : Params I J K) (k : K) :
    ancestryFreq θ (Sum.inr k) = θ.F k := rfl

/-- Zero private drift for `Params`: an individual's frequency is exactly the
`Q i`-mixture of the ancestral frequencies. -/
theorem ancestryFreq_inl_eq_sum (θ : Params I J K) (i : I) (j : J) :
    ancestryFreq θ (Sum.inl i) j = ∑ k, θ.Q i k * ancestryFreq θ (Sum.inr k) j :=
  ancestryFreqOf_inl_eq_sum θ.Q θ.F i j

/-- F4 linearity for individuals of the `AdmixtureEM` model. The strict
positivity fields of `Params` are not used; only `θ.Q_sum` enters. -/
theorem f4_ancestryFreq_individual (θ : Params I J K)
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (i : I) (X Y Z : I ⊕ K) :
    f4 μ (ancestryFreq θ) (Sum.inl i) X Y Z =
      ∑ k, θ.Q i k * f4 μ (ancestryFreq θ) (Sum.inr k) X Y Z :=
  f4_ancestryFreqOf_individual θ.Q θ.F (fun i => θ.Q_sum i) hp i X Y Z

/-- QpWave bound for the `AdmixtureEM` model, in `k = K - 1` form. -/
theorem rank_f4Matrix_ancestryFreq_le {n r k : ℕ} (θ : Params (Fin (n + 1)) J (Fin (k + 1)))
    (hp : ∀ X, MemLp (ancestryFreq θ X) 2 μ) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreqOf_le θ.Q θ.F (fun i => θ.Q_sum i) hp R

/-- The `Params` rank bound over finitely many loci with a finite measure. -/
theorem rank_f4Matrix_ancestryFreq_le_of_finite {n r k : ℕ} [Finite J]
    [DiscreteMeasurableSpace J] [IsFiniteMeasure μ]
    (θ : Params (Fin (n + 1)) J (Fin (k + 1))) (R : Fin (r + 1) → Fin (n + 1) ⊕ Fin (k + 1)) :
    (f4Matrix μ (ancestryFreq θ) Sum.inl R).rank ≤ k :=
  rank_f4Matrix_ancestryFreq_le θ (fun _ => MemLp.of_discrete) R

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
