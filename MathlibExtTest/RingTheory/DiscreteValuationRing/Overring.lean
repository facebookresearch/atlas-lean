/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.Overring

@[expose] public section

/-- Consumer with the original binders. -/
example
    (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K]
    (W : Subring K) (hVW : ∀ v : V, algebraMap V K v ∈ W) (hW : W ≠ ⊤)
    (x : K) (hx : x ∈ W) :
    ∃ v : V, algebraMap V K v = x :=
  IsDiscreteValuationRing.exists_algebraMap_eq_of_mem_subring_of_ne_top
    V K W hVW hW x hx

/-- The same consumer in a higher universe. -/
example
    (V : Type 1) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type 1) [Field K] [Algebra V K] [IsFractionRing V K]
    (W : Subring K) (hVW : ∀ v : V, algebraMap V K v ∈ W) (hW : W ≠ ⊤)
    (x : K) (hx : x ∈ W) :
    ∃ v : V, algebraMap V K v = x :=
  IsDiscreteValuationRing.exists_algebraMap_eq_of_mem_subring_of_ne_top
    V K W hVW hW x hx

/-- Boundary: the inverse of a uniformizer is not in the image of the ring.
Hence the hypothesis that the subring is proper cannot be dropped: for
the whole fraction field, that inverse lies in the subring but has no
preimage. -/
example
    (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type*) [Field K] [Algebra V K] [IsFractionRing V K] :
    ∃ x : K, x ∈ (⊤ : Subring K) ∧ ¬ ∃ v : V, algebraMap V K v = x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine ⟨(algebraMap V K ϖ)⁻¹, Subring.mem_top _, ?_⟩
  rintro ⟨v, hv⟩
  have hinj := IsFractionRing.injective V K
  have h1 : algebraMap V K (v * ϖ) = 1 := by
    rw [map_mul, hv]; exact inv_mul_cancel₀
      ((map_ne_zero_iff _ hinj).mpr hϖ.ne_zero)
  have h2 : v * ϖ = 1 := hinj (by rw [h1, map_one])
  exact hϖ.1 ⟨⟨ϖ, v, by rw [mul_comm]; exact h2, h2⟩, rfl⟩
