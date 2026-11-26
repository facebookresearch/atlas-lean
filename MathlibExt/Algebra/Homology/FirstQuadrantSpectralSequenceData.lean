/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltration

/-!
# Page indices for an increasing first-quadrant filtration

For a spectral object indexed by EInt = ℤ ∪ {⊥,⊤}, use page indices r≥1, bidegrees (p,q) ∈
ℕ×ℕ, and differential shape (−r,r−1). The cochain degree of (p,q) is −p−q.

The four filtration indices at page r are p−r ≤ p−1 ≤ p ≤ p+r−1, all computed in ℤ and
embedded as finite EInt indices. At r=1 the outer indices equal their adjacent inner indices,
so the first-page object is the relative homology of the consecutive stages p−1≤p.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Abelian.SpectralObject

/-- Define spectral-sequence data for EInt-indexed spectral objects starting at page r₀=1 and with
bidegree set ℕ×ℕ. At (p,q), the cochain degree is −p−q, the page-r differential shape is
(−r,r−1), and the four filtration indices are i₀=p−r, i₁=p−1, i₂=p, and i₃=p+r−1. Each index
is computed in ℤ and embedded in EInt, with i₀≤i₁≤i₂≤i₃ for r≥1. At page one i₀=i₁ and i₂=i₃,
yielding the consecutive-stage relative homology at p−1≤p. -/
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
