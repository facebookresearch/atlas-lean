/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.AdmixtureEM

/-!
# Frequencies of the global-ancestry model

`ancestryFreqOf` puts individuals and their ancestral populations in one frequency family
indexed by loci. `ancestryFreq` specializes it to the parameters of `AdmixtureEM`.
Linearity of f4 and the rank bound for this family are in
`Domains.Biology.PopulationGenetics.GlobalAncestryBridge`.
-/

@[expose] public section

open scoped BigOperators

namespace Cslib.Bioinformatics.PopulationStructure.AdmixtureEM

variable {I J K : Type*} [Fintype K]

/-- Frequencies of a global-ancestry model from raw ancestry proportions
`Q` and ancestral frequencies `F`, viewed for f-statistics over loci:
individuals `i` (as `Sum.inl i`) have frequency `∑ k, Q i k * F k j` at locus
`j`, and ancestral populations `k` (as `Sum.inr k`) have frequency `F k j`.
No positivity or boundedness assumption is part of the definition; in use, each `Q i` is a vector
of nonnegative ancestry proportions summing to `1` and `0 ≤ F k j ≤ 1`. -/
noncomputable def ancestryFreqOf (Q : I → K → ℝ) (F : K → J → ℝ) : I ⊕ K → J → ℝ
  | Sum.inl i => fun j => ∑ k, Q i k * F k j
  | Sum.inr k => F k

@[simp] theorem ancestryFreqOf_inl (Q : I → K → ℝ) (F : K → J → ℝ) (i : I) :
    ancestryFreqOf Q F (Sum.inl i) = fun j => ∑ k, Q i k * F k j := rfl

@[simp] theorem ancestryFreqOf_inr (Q : I → K → ℝ) (F : K → J → ℝ) (k : K) :
    ancestryFreqOf Q F (Sum.inr k) = F k := rfl

/-- Zero private drift for raw global-ancestry data: an individual's
frequency is exactly the combination of the ancestral frequencies with
coefficients `Q i k` (of any sign and sum; a mixture when they are
nonnegative and sum to `1`). -/
theorem ancestryFreqOf_inl_eq_sum (Q : I → K → ℝ) (F : K → J → ℝ) (i : I) (j : J) :
    ancestryFreqOf Q F (Sum.inl i) j = ∑ k, Q i k * ancestryFreqOf Q F (Sum.inr k) j := rfl

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

end Cslib.Bioinformatics.PopulationStructure.AdmixtureEM
