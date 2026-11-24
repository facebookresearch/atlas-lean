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
# The actual positive supremum of the maximal family's finite cutoffs

The strict finite-cutoff constructor proves positivity, norm≤1, nonemptiness
and directedness from original ψ. Feeding precisely those actual fields to
the strict bounded-positive-supremum constructor gives an original positive
least upper bound of the literal cutoff range. Its norm≤1 and order≤1 are
proved internally. No LUB, projection limit or normal member is an input.
The supremum's projection law and zero complement remain subsequent steps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct the actual original finite-cutoff positive LUB with original norm and identity bounds. -/
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

/-- The constructed cutoff supremum is the least upper bound of the literal cutoff values. -/
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

/-- The same constructed cutoff supremum has norm at most one. -/
theorem maximalLocalCutoffSupremum_norm_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      ‖((maximalLocalCutoffSupremum M ψ).val : M)‖ ≤ 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalCutoffSupremum M ψ).property.2.1

/-- The same constructed cutoff supremum lies below the identity in the spectral order. -/
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
