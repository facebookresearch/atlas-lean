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

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalFiniteCutoffs
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveSupremum

/-!
# Positive supremum of maximal-family finite cutoffs

For a positive bounded functional `ψ`, the finite projection cutoffs `P_t` of its maximal local
family have a nonempty directed range bounded by the identity and in norm by one.

Their constructed positive least upper bound `s` satisfies `s=sup_t P_t`, `‖s‖≤1` and `s≤I`. Its
projection and identity properties are established in the subsequent cutoff lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive least upper bound of the finite cutoff family.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `S` be the constructed
maximal set of pairwise orthogonal nonzero star projections, each admitting a vector `ξ`
with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`.
`maximalLocalCutoffSupremum M ψ` returns `s∈M₊` that is the least upper bound of `{P_t}`,
with `‖s‖≤1` and `s≤I_M`. -/
def maximalLocalCutoffSupremum (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) →
      let P := maximalLocalPositiveFiniteCutoffs M ψ
      {s : PositiveElement M //
        @IsLUB M (CStarAlgebra.spectralOrder M).toLE
          (Set.range fun t => (P.val t : M)) (s : M) ∧
        ‖(s : M)‖ ≤ 1 ∧ @LE.le M (CStarAlgebra.spectralOrder M).toLE (s : M) 1} := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder M := sourceOrder
  letI : Preorder M := sourceOrder.toPreorder
  letI : LE M := sourceOrder.toLE
  letI : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  let P := maximalLocalPositiveFiniteCutoffs M ψ
  have hnonempty : (Set.range P.val).Nonempty := maximalLocalPositiveFiniteCutoffs_range_nonempty M ψ
  have hdirected : DirectedOn (fun a b : PositiveElement M =>
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) (b : M)) (Set.range P.val) :=
    maximalLocalPositiveFiniteCutoffs_directedOn M ψ
  have hbound (p : PositiveElement M) (hp : p ∈ Set.range P.val) : ‖(p : M)‖ ≤ 1 := by
    obtain ⟨t, rfl⟩ := hp
    exact (maximalLocalPositiveFiniteCutoffs_norm_le_one M ψ) t
  let s := boundedPositiveSupremum M (Set.range P.val) hnonempty hdirected 1 hbound
  have hrange : ((fun p : PositiveElement M => (p : M)) '' Set.range P.val) =
      Set.range (fun t => (P.val t : M)) := by
    ext a
    constructor
    · rintro ⟨p, ⟨t, rfl⟩, rfl⟩
      exact Set.mem_range_self t
    · rintro ⟨t, rfl⟩
      exact ⟨P.val t, Set.mem_range_self t, rfl⟩
  have hLUB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE
      (Set.range fun t => (P.val t : M)) (s.val : M) := by
    rw [← hrange]
    exact s.property.1
  have hunit : @LE.le M (CStarAlgebra.spectralOrder M).toLE (s.val : M) 1 := by
    apply hLUB.2
    intro p hp
    obtain ⟨t, rfl⟩ := hp
    exact (maximalLocalPositiveFiniteCutoffs_le_one M ψ) t
  exact ⟨s.val, hLUB, s.property.2, hunit⟩

/-- **Least-upper-bound property of the maximal-family cutoff supremum.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M →
ℂ` be a positive bounded complex-linear functional for the spectral orders. Let `S` be the
constructed maximal set of pairwise orthogonal nonzero star projections, each admitting a
vector `ξ` with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`.
the element `s=maximalLocalCutoffSupremum M ψ` is the least upper bound of the range of
finite cutoffs `P_t`. -/
theorem maximalLocalCutoffSupremum_isLUB (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      @IsLUB M (CStarAlgebra.spectralOrder M).toLE
        (Set.range fun t => ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M))
        ((maximalLocalCutoffSupremum M ψ).val : M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalCutoffSupremum M ψ).property.1

/-- **Norm bound of the finite-cutoff supremum.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. for
`s=maximalLocalCutoffSupremum M ψ`, `‖s‖≤1`. -/
theorem maximalLocalCutoffSupremum_norm_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      ‖((maximalLocalCutoffSupremum M ψ).val : M)‖ ≤ 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalCutoffSupremum M ψ).property.2.1

/-- **Finite-cutoff supremum lies below the identity.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. for
`s=maximalLocalCutoffSupremum M ψ`, `s≤I_M` in the spectral order. -/
theorem maximalLocalCutoffSupremum_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      @LE.le M (CStarAlgebra.spectralOrder M).toLE ((maximalLocalCutoffSupremum M ψ).val : M) 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalCutoffSupremum M ψ).property.2.2

end

end VonNeumannAlgebra
