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

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalProjectionFamily
public import MathlibExt.Algebra.Star.StarProjection.FiniteSum
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual bounded positive finite cutoffs of the maximal local projection family

Each cutoff is the literal sum of a finite set of members of the original
constructed maximal family. Its star-projection law gives positivity and
bounds it by the original identity. The original C-star norm gives norm≤1.
Finite unions and positivity make the actual range directed; the empty
finite set supplies nonemptiness. No cutoff family, positivity, norm bound,
supremum, projection limit or normal member certificate is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped BigOperators

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Construct the actual positive finite-sum cutoffs and all prerequisites of their bounded supremum. -/
def maximalLocalPositiveFiniteCutoffs (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) →
      let S := maximalLocalProjectionFamily M ψ
      {P : Finset S.val → PositiveElement M //
        (∀ t, (P t : M) = ∑ p ∈ t, (p.val : M)) ∧
        (∀ t, IsStarProjection (P t : M)) ∧
        (∀ t, @LE.le M (CStarAlgebra.spectralOrder M).toLE (P t : M) 1) ∧
        (∀ t, ‖(P t : M)‖ ≤ 1) ∧
        (@Monotone (Finset S.val) M inferInstance (CStarAlgebra.spectralOrder M).toPreorder
          (fun t => (P t : M))) ∧
        (Set.range P).Nonempty ∧
        DirectedOn (fun a b : PositiveElement M =>
          @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) (b : M)) (Set.range P)} := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder M := sourceOrder
  letI : Preorder M := sourceOrder.toPreorder
  letI : LE M := sourceOrder.toLE
  letI : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  letI : IsOrderedAddMonoid M := StarOrderedRing.toIsOrderedAddMonoid
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  let S := maximalLocalProjectionFamily M ψ
  let sum (t : Finset S.val) : M := ∑ p ∈ t, (p.val : M)
  have hsum (t : Finset S.val) : IsStarProjection (sum t) := by
    apply IsStarProjection.finset_sum_of_pairwise_mul_eq_zero
    · intro p _hp
      exact (S.property.1 p.val p.property).1
    · intro p _hp q _hq hpq
      exact S.property.2.1 p.property q.property
        (fun h => hpq (Subtype.ext h))
  let P (t : Finset S.val) : PositiveElement M := ⟨sum t, (hsum t).nonneg⟩
  have hone (t : Finset S.val) : @LE.le M (CStarAlgebra.spectralOrder M).toLE (P t : M) 1 :=
    (hsum t).le_one
  have hnorm (t : Finset S.val) : ‖(P t : M)‖ ≤ 1 := by
    have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg (hone t) (P t).property
    have hunit : ‖(1 : M)‖ ≤ 1 := by
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    exact h.trans hunit
  have hmono : @Monotone (Finset S.val) M inferInstance
      (CStarAlgebra.spectralOrder M).toPreorder (fun t => (P t : M)) := by
    intro t v htv
    change sum t ≤ sum v
    apply Finset.sum_le_sum_of_subset_of_nonneg htv
    intro p _hp _hpt
    exact (S.property.1 p.val p.property).1.nonneg
  refine ⟨P, (fun _ => rfl), hsum, hone, hnorm, hmono, ?_, ?_⟩
  · exact ⟨P ∅, Set.mem_range_self ∅⟩
  · intro a ha b hb
    obtain ⟨t, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    refine ⟨P (t ∪ v), Set.mem_range_self (t ∪ v), ?_, ?_⟩
    · exact hmono Finset.subset_union_left
    · exact hmono Finset.subset_union_right

/-- Every actual cutoff is the literal finite sum of its original family members. -/
theorem maximalLocalPositiveFiniteCutoffs_value (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M) = ∑ p ∈ t, (p.val : M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.1 t

/-- Each constructed finite cutoff is a star projection. -/
theorem maximalLocalPositiveFiniteCutoffs_isStarProjection (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      IsStarProjection ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.1 t

/-- Every actual finite cutoff is bounded above by the identity in the spectral order. -/
theorem maximalLocalPositiveFiniteCutoffs_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      @LE.le M (CStarAlgebra.spectralOrder M).toLE
        ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M) 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.1 t

/-- Every actual finite cutoff has norm at most one. -/
theorem maximalLocalPositiveFiniteCutoffs_norm_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      ‖((maximalLocalPositiveFiniteCutoffs M ψ).val t : M)‖ ≤ 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.1 t

/-- The actual cutoff values are monotone in their finite index sets. -/
theorem maximalLocalPositiveFiniteCutoffs_monotone (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      @Monotone (Finset (maximalLocalProjectionFamily M ψ).val) M inferInstance
        (CStarAlgebra.spectralOrder M).toPreorder
        (fun t => ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M)) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.2.1

/-- The range of actual cutoffs is nonempty, including the empty finite cutoff. -/
theorem maximalLocalPositiveFiniteCutoffs_range_nonempty (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      (Set.range (maximalLocalPositiveFiniteCutoffs M ψ).val).Nonempty := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.2.2.1

/-- The actual positive cutoff range is directed in the original spectral order. -/
theorem maximalLocalPositiveFiniteCutoffs_directedOn (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      DirectedOn (fun a b : PositiveElement M =>
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) (b : M))
        (Set.range (maximalLocalPositiveFiniteCutoffs M ψ).val) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.2.2.2

end

end VonNeumannAlgebra
