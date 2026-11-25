/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# The core of an increasing homological spectral sequence

The page-one core of a positive increasing filtration uses the interval
p - 1 ⟶ p at bidegree (p, q). Its homological differential has bidegree
(-r, r - 1).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace CategoryTheory.Abelian.SpectralObject

/-- The page-one core for a positive increasing homological filtration.

At page `r`, the object at `(p, q)` uses cohomological degree `-p-q` and
filtration indices
`p-r ≤ p-1 ≤ p ≤ p+r-1`. -/
@[simps!]
def coreE₁IncreasingHomologicalNat :
    SpectralSequenceDataCore EInt
      (fun r ↦ ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1 where
  deg pq := -pq.1 - pq.2
  i₀ r pq hr := (pq.1 - r : ℤ)
  i₁ pq := (pq.1 - 1 : ℤ)
  i₂ pq := (pq.1 : ℤ)
  i₃ r pq hr := (pq.1 + r - 1 : ℤ)
  le₀₁ r pq hr := by simp; lia
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; lia
  hc r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia
  hc₀₂ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia +mbtc
  hc₁₃ r pq pq' hpq hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia +mbtc
  antitone_i₀ r r' pq hr hrr' := by simp; lia
  monotone_i₃ r r' pq hr hrr' := by simp; lia
  i₀_prev r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia +mbtc
  i₃_next r r' pq pq' hpq hrr' hr := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff] at hpq
    lia +mbtc

set_option backward.defeqAttrib.useBackward true in
instance : coreE₁IncreasingHomologicalNat.HasFirstPageComputation where
  hi₀₁ pq := by dsimp
  hi₂₃ pq := by dsimp; lia

end CategoryTheory.Abelian.SpectralObject
