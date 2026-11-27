/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.LocalVectorDominatedProjection
public import Mathlib.Order.Zorn

/-!
# Maximal orthogonal family of locally dominated projections

For a positive bounded functional `ψ`, call a nonzero star projection `p` eligible when some
`ξ∈H` satisfies `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`.

There is a maximal set `S` of eligible projections with `pq=0` for distinct members. Maximality
is by inclusion among such orthogonal sets. The construction allows an empty family in a zero
algebra and does not assume normality of `ψ`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Maximal set of orthogonal locally vector-dominated projections.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders.
`maximalLocalProjectionFamily M ψ` returns a set `S` of nonzero star projections with
pairwise zero products. Each `p∈S` has a vector `ξ` dominating `Re ψ` on `0≤b≤p`; any
larger orthogonal set with these properties is contained in `S`. -/
def maximalLocalProjectionFamily (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) →
      {S : Set M //
        (∀ p ∈ S, IsStarProjection p ∧ p ≠ 0 ∧ ∃ ξ : H,
          ∀ b : PositiveElement M,
            @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
            (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) ∧
        S.Pairwise (fun p q => p * q = 0) ∧
        ∀ T : Set M,
          (∀ p ∈ T, IsStarProjection p ∧ p ≠ 0 ∧ ∃ ξ : H,
            ∀ b : PositiveElement M,
              @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
              (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
          T.Pairwise (fun p q => p * q = 0) → S ⊆ T → T ⊆ S} := by
  classical
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  let eligible (p : M) : Prop := IsStarProjection p ∧ p ≠ 0 ∧ ∃ ξ : H,
    ∀ b : PositiveElement M,
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
      (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re
  let families : Set (Set M) := {S | (∀ p ∈ S, eligible p) ∧ S.Pairwise (fun p q => p * q = 0)}
  have hchain (C : Set (Set M)) (hC : C ⊆ families) (hc : IsChain (· ⊆ ·) C) :
      ∃ U ∈ families, ∀ S ∈ C, S ⊆ U := by
    refine ⟨⋃₀ C, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro p hp
        obtain ⟨S, hSC, hpS⟩ := Set.mem_sUnion.mp hp
        exact (hC hSC).1 p hpS
      · intro p hp q hq hpq
        obtain ⟨S, hSC, hpS⟩ := Set.mem_sUnion.mp hp
        obtain ⟨T, hTC, hqT⟩ := Set.mem_sUnion.mp hq
        by_cases hST : S = T
        · subst T
          exact (hC hSC).2 hpS hqT hpq
        · rcases hc hSC hTC hST with hsub | hsub
          · exact (hC hTC).2 (hsub hpS) hqT hpq
          · exact (hC hSC).2 hpS (hsub hqT) hpq
    · intro S hSC p hpS
      exact Set.mem_sUnion.mpr ⟨S, hSC, hpS⟩
  have maximalExists : ∃ S, Maximal (· ∈ families) S := zorn_subset families hchain
  let S : Set M := Classical.choose maximalExists
  have hS := Classical.choose_spec maximalExists
  refine ⟨S, hS.1.1, hS.1.2, ?_⟩
  intro T hTel hTpair hST
  exact hS.2 ⟨hTel, hTpair⟩ hST

end

end VonNeumannAlgebra
