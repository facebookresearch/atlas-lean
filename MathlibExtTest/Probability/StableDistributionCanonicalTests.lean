/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Probability.StableDistribution
public import MathlibExt.Probability.InfinitelyDivisible

@[expose] public section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
open MathlibExt.Probability.StableDistribution

namespace MathlibExtTest.Probability.StableDistributionCanonicalTests

/-- The indexed predicate must determine the positive-n dilation. -/
theorem fixed_index_dilation {μ : Measure ℝ} {α : ℝ} (h : IsStable μ α)
    (n : ℕ) (hn : 0 < n) :
    ∃ b : ℝ, μ.convPow n = μ.map (fun x => (n : ℝ) ^ (1 / α) * x + b) :=
  h.2.2.2 n hn

/-- The nondegenerate standard Gaussian cannot have stability index one. -/
theorem gaussian_not_index_one : ¬ IsStable (gaussianReal 0 1) 1 :=
  not_isStable_gaussianReal_one one_ne_zero

/-- The actual Gaussian law supplies a nondegenerate indexed self-attraction witness. -/
theorem gaussian_indexed_self_attraction : InDomainOfAttractionIndex (gaussianReal 0 1) 2 :=
  ⟨gaussianReal 0 1, isStable_gaussianReal 0 1,
    isNondegenerate_gaussianReal one_ne_zero,
    (isStable_gaussianReal 0 1).inDomainOfAttraction_self⟩

/-- Every indexed witness must satisfy the missing nondegeneracy clause. -/
theorem indexed_witness_nondegenerate {μ : Measure ℝ} {α : ℝ}
    (h : InDomainOfAttractionIndex μ α) :
    ∃ G : Measure ℝ, IsNondegenerate G ∧ InDomainOfAttraction μ G := by
  obtain ⟨G, _, hG, hDA⟩ := h
  exact ⟨G, hG, hDA⟩

/-- The original chosen Dirac witness is excluded by the new exact contract. -/
theorem dirac_not_indexed_witness (a : ℝ) (μ : Measure ℝ) (α : ℝ) :
    ¬ (IsStable (dirac a) α ∧ IsNondegenerate (dirac a) ∧ InDomainOfAttraction μ (dirac a)) :=
  fun h => not_isNondegenerate_dirac a h.2.1

/-- The real self-attraction witness has a positive order-zero normalizer and the exact limit. -/
theorem gaussian_self_normalizer_zero :
    ∃ a b : ℕ → ℝ, 0 < a 0 ∧ (∀ n, 0 < a n) ∧
      ∀ f : ℝ →ᵇ ℝ, Tendsto
        (fun n => ∫ x, f x ∂(Measure.map (fun y => (y - b n) / a n)
          ((gaussianReal 0 1).convPow n))) atTop (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  have h := (isStable_gaussianReal 0 1).inDomainOfAttraction_self
  obtain ⟨_, _, a, b, ha, hlim⟩ := h
  exact ⟨a, b, ha 0, ha, hlim⟩

/-- Canonical order zero remains the Dirac identity. -/
theorem canonical_convolution_zero : (gaussianReal 0 1).convPow 0 = dirac 0 := rfl

end MathlibExtTest.Probability.StableDistributionCanonicalTests
