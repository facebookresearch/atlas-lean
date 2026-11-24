/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltration

/-!
# Homological first-page data for a first-quadrant filtration

This file defines the page-indexing data appropriate for an increasing
first-quadrant filtration of a chain complex after reindexing it as a
cochain complex.  It starts at page one, has differential bidegree
`(-r, r-1)`, and uses cohomological degree `-(p+q)`.

The construction is deliberately separate from Mathlib's
`coreE₂HomologicalNat`, whose filtration orientation and starting-page
convention are different.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Abelian.SpectralObject

/-- Page data for the homological spectral sequence of an increasing
first-quadrant filtration.  At page one, the interval is
`p-1 ≤ p`, so its objects are the relative homology of consecutive
filtration stages. -/
@[simps!]
def coreE₁FirstQuadrantHomological :
    SpectralSequenceDataCore EInt
      (fun r => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 where
  deg pq := -pq.1 - pq.2
  i₀ r pq hr := @WithBotTop.coe ℤ ((pq.1 : ℤ) - r)
  i₁ pq := @WithBotTop.coe ℤ ((pq.1 : ℤ) - 1)
  i₂ pq := @WithBotTop.coe ℤ (pq.1 : ℤ)
  i₃ r pq hr := @WithBotTop.coe ℤ ((pq.1 : ℤ) + r - 1)
  le₀₁ r pq hr := WithBotTop.coe_monotone (by lia)
  le₁₂ pq := WithBotTop.coe_monotone (by lia)
  le₂₃ r pq hr := WithBotTop.coe_monotone (by lia)
  hc r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact congrArg (@WithBotTop.coe ℤ) (by lia)
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact congrArg (@WithBotTop.coe ℤ) (by lia)
  antitone_i₀ r r' pq hr hrr' := WithBotTop.coe_monotone (by lia)
  monotone_i₃ r r' pq hr hrr' := WithBotTop.coe_monotone (by lia)
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact congrArg (@WithBotTop.coe ℤ) (by lia)
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    exact congrArg (@WithBotTop.coe ℤ) (by lia)

instance : coreE₁FirstQuadrantHomological.HasFirstPageComputation where
  hi₀₁ pq := congrArg (@WithBotTop.coe ℤ) (by lia)
  hi₂₃ pq := congrArg (@WithBotTop.coe ℤ) (by lia)

end CategoryTheory.Abelian.SpectralObject

end
