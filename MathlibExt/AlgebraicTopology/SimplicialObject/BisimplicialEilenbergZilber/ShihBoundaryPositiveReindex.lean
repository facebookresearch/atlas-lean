/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryPrefixCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryFrontReduction
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositiveReindexSums

/-!
# Positive-face coordinates for the bisimplicial Shih boundary

The positive upper and lower boundary sums are split into prefix and residual
coordinates.  Prefix terms cancel, and the residual sums are reindexed by the
existing transition, active, lower-left, and lower-right equivalences.  No new
shuffle combinatorics or map identities occur here.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- Positive prefix coordinates cancel. -/
theorem shihPositivePrefixCoordinate_sum_eq_zero (n : ℕ) :
    (∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositivePrefixCoordinate n,
        shihUpperBoundaryTerm B (n + 1) z.val.1 z.val.2.succ) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositivePrefixCoordinate n,
        shihLowerBoundaryTerm B n z.val.2.succ z.val.1 = 0 := by
  classical
  rw [← (AlgebraicTopology.EilenbergZilber.shihUpperPositiveCoordinatePrefixEquivLower n).sum_comp
    (fun z => shihLowerBoundaryTerm B n z.val.2.succ z.val.1)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ => by
    have hprefix : z.val.2.succ.val + 1 < z.val.1.gap := by
      have h := z.property
      change z.val.2.val + 2 < z.val.1.gap at h
      simpa only [Fin.val_succ] using h
    have hcancel := shihPrefixBoundaryTerm_add_eq_zero B
      z.val.1 z.val.2.succ hprefix
    have hindex :
        (AlgebraicTopology.EilenbergZilber.shihUpperPositiveCoordinatePrefixEquivLower
          n z).val.1 = z.val.1.lowerPrefix (by omega) := by rfl
    have hface :
        (AlgebraicTopology.EilenbergZilber.shihUpperPositiveCoordinatePrefixEquivLower
          n z).val.2.succ =
          z.val.1.lowerPrefixFace z.val.2.succ hprefix := by
      apply Fin.ext
      rfl
    rw [hindex, hface]
    exact hcancel

/-- Removing prefix coordinates leaves the exact residual sums. -/
theorem shihPositiveBoundary_sum_eq_residual (n : ℕ) :
    (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i =
    (∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveResidualIndex n,
        shihUpperBoundaryTerm B (n + 1) z.val.1 z.val.2.succ) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveResidualIndex n,
        shihLowerBoundaryTerm B n z.val.2.succ z.val.1 := by
  classical
  have hUpper :
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
          ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) =
        (∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositivePrefixCoordinate n,
            shihUpperBoundaryTerm B (n + 1) z.val.1 z.val.2.succ) +
          ∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveResidualIndex n,
            shihUpperBoundaryTerm B (n + 1) z.val.1 z.val.2.succ := by
    calc
      _ = ∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveCoordinate n,
          shihUpperBoundaryTerm B (n + 1) z.1 z.2.succ :=
        (Fintype.sum_prod_type'
          (α₁ := AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1))
          (α₂ := Fin (n + 2))
          (fun i k => shihUpperBoundaryTerm B (n + 1) i k.succ)).symm
      _ = _ := (Fintype.sum_subtype_add_sum_subtype
        AlgebraicTopology.EilenbergZilber.UpperPositiveCoordinate.IsPrefix
        (fun z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveCoordinate n =>
          shihUpperBoundaryTerm B (n + 1) z.1 z.2.succ)).symm
  have hLower :
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
          ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i) =
        (∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositivePrefixCoordinate n,
            shihLowerBoundaryTerm B n z.val.2.succ z.val.1) +
          ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveResidualIndex n,
            shihLowerBoundaryTerm B n z.val.2.succ z.val.1 := by
    calc
      _ = ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveCoordinate n,
          shihLowerBoundaryTerm B n z.2.succ z.1 :=
        (Fintype.sum_prod_type'
          (α₁ := AlgebraicTopology.EilenbergZilber.ShihIndex n)
          (α₂ := Fin (n + 1))
          (fun i k => shihLowerBoundaryTerm B n k.succ i)).symm
      _ = _ := (Fintype.sum_subtype_add_sum_subtype
        AlgebraicTopology.EilenbergZilber.LowerPositiveCoordinate.IsPrefix
        (fun z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveCoordinate n =>
          shihLowerBoundaryTerm B n z.2.succ z.1)).symm
  rw [hUpper, hLower]
  have hprefix := shihPositivePrefixCoordinate_sum_eq_zero B n
  calc
    _ = ((∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositivePrefixCoordinate n,
            shihUpperBoundaryTerm B (n + 1) z.val.1 z.val.2.succ) +
          ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositivePrefixCoordinate n,
            shihLowerBoundaryTerm B n z.val.2.succ z.val.1) +
        ((∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveResidualIndex n,
            shihUpperBoundaryTerm B (n + 1) z.val.1 z.val.2.succ) +
          ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveResidualIndex n,
            shihLowerBoundaryTerm B n z.val.2.succ z.val.1) := by abel
    _ = _ := by rw [hprefix, zero_add]

/-- Partition the residual boundary into four disjoint strata. -/
theorem shihPositiveBoundary_sum_eq_partitioned (n : ℕ) :
    (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i =
    ((∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveTransitionIndex n,
        shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperPositiveActiveIndex n,
        shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ) +
    ((∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveLeftIndex n,
        shihLowerBoundaryTerm B n z.val.val.2.succ z.val.val.1) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerPositiveRightIndex n,
        shihLowerBoundaryTerm B n z.val.val.2.succ z.val.val.1) := by
  rw [shihPositiveBoundary_sum_eq_residual]
  rw [AlgebraicTopology.EilenbergZilber.sum_upperPositiveResidual_eq_transition_add_active,
    AlgebraicTopology.EilenbergZilber.sum_lowerPositiveResidual_eq_left_add_right]

/-- Reindex the four residual strata by their canonical coordinate types. -/
theorem shihPositiveBoundary_sum_eq_reindexed (n : ℕ) :
    (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i =
    ((∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        let z := (AlgebraicTopology.EilenbergZilber.shihUpperPositiveTransitionEquiv n).symm i
        shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperActiveData n,
        let w := (AlgebraicTopology.EilenbergZilber.shihUpperPositiveActiveEquiv n).symm z
        shihUpperBoundaryTerm B (n + 1) w.val.val.1 w.val.val.2.succ) +
    ((∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerLeftData n,
        let w := (AlgebraicTopology.EilenbergZilber.shihLowerPositiveLeftEquiv n).symm z
        shihLowerBoundaryTerm B n w.val.val.2.succ w.val.val.1) +
      ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerRightData n,
        let w := (AlgebraicTopology.EilenbergZilber.shihLowerPositiveRightEquiv n).symm z
        shihLowerBoundaryTerm B n w.val.val.2.succ w.val.val.1) := by
  rw [shihPositiveBoundary_sum_eq_partitioned,
    AlgebraicTopology.EilenbergZilber.sum_upperPositiveTransition_eq_shihIndex,
    AlgebraicTopology.EilenbergZilber.sum_upperPositiveActive_eq_data,
    AlgebraicTopology.EilenbergZilber.sum_lowerPositiveLeft_eq_data,
    AlgebraicTopology.EilenbergZilber.sum_lowerPositiveRight_eq_data]

/-- The remaining all-positive-face identity. -/
def ShihPositiveFaceIdentity (n : ℕ) : Prop :=
  (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
      ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
    ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
      ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i =
    awShuffleZeroComponent B (n + 1) -
      𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1))

/-- The positive-face identity in canonical residual coordinates. -/
def ShihReindexedPositiveFaceIdentity (n : ℕ) : Prop :=
  ((∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
      let z := (AlgebraicTopology.EilenbergZilber.shihUpperPositiveTransitionEquiv n).symm i
      shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ) +
    ∑ z : AlgebraicTopology.EilenbergZilber.ShihUpperActiveData n,
      let w := (AlgebraicTopology.EilenbergZilber.shihUpperPositiveActiveEquiv n).symm z
      shihUpperBoundaryTerm B (n + 1) w.val.val.1 w.val.val.2.succ) +
  ((∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerLeftData n,
      let w := (AlgebraicTopology.EilenbergZilber.shihLowerPositiveLeftEquiv n).symm z
      shihLowerBoundaryTerm B n w.val.val.2.succ w.val.val.1) +
    ∑ z : AlgebraicTopology.EilenbergZilber.ShihLowerRightData n,
      let w := (AlgebraicTopology.EilenbergZilber.shihLowerPositiveRightEquiv n).symm z
      shihLowerBoundaryTerm B n w.val.val.2.succ w.val.val.1) =
    awShuffleZeroComponent B (n + 1) -
      𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1))

/-- The original and fully reindexed positive-face identities are equivalent. -/
theorem shihPositiveFaceIdentity_iff_reindexed (n : ℕ) :
    ShihPositiveFaceIdentity B n ↔ ShihReindexedPositiveFaceIdentity B n := by
  rw [ShihPositiveFaceIdentity, ShihReindexedPositiveFaceIdentity,
    shihPositiveBoundary_sum_eq_reindexed]

end AlgebraicTopology.BisimplicialEilenbergZilber
