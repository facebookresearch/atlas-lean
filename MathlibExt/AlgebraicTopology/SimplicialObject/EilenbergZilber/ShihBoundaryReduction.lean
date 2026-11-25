/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihDerivedBoundary
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneBoundary

/-!
# Reduction of the Shih boundary calculation

This file removes the front-face cancellation between the derived
gap-greater-than-one family and the preceding lower boundary.  The remaining
formula consists of the `AW ≫ shuffle` base summands and positive faces only.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- After splitting front and positive faces, the derived front faces cancel
the preceding lower front faces. -/
theorem shihBoundary_sum_reduction (X Y : SimplicialObject C) (n : ℕ) :
    (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 3), shihUpperBoundaryTerm X Y (n + 1) i k) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 2), shihLowerBoundaryTerm X Y n k i =
    (∑ i : {i : ShihIndex (n + 1) // i.gap = 1},
        gapOneBaseSummand X Y i.1 i.2) +
      (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i := by
  have hUpperFaces :
      (∑ i : ShihIndex (n + 1),
          ∑ k : Fin (n + 3), shihUpperBoundaryTerm X Y (n + 1) i k) =
        (∑ i : ShihIndex (n + 1),
            shihUpperBoundaryTerm X Y (n + 1) i (0 : Fin (n + 3))) +
          ∑ i : ShihIndex (n + 1),
            ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_succ _
  have hLowerFaces :
      (∑ i : ShihIndex n,
          ∑ k : Fin (n + 2), shihLowerBoundaryTerm X Y n k i) =
        (∑ i : ShihIndex n,
            shihLowerBoundaryTerm X Y n (0 : Fin (n + 2)) i) +
          ∑ i : ShihIndex n,
            ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_succ _
  let e : {i : ShihIndex (n + 1) // ¬i.gap = 1} ≃
      {i : ShihIndex (n + 1) // 1 < i.gap} :=
    Equiv.subtypeEquivProp (by
      funext i
      apply propext
      have hi := i.gap_pos
      omega)
  have hUpperZeroSplit :
      (∑ i : ShihIndex (n + 1),
          shihUpperBoundaryTerm X Y (n + 1) i (0 : Fin (n + 3))) =
        (∑ i : {i : ShihIndex (n + 1) // i.gap = 1},
            shihUpperBoundaryTerm X Y (n + 1) i.1 (0 : Fin (n + 3))) +
          ∑ i : {i : ShihIndex (n + 1) // 1 < i.gap},
            shihUpperBoundaryTerm X Y (n + 1) i.1 (0 : Fin (n + 3)) := by
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun i : ShihIndex (n + 1) => i.gap = 1)
      (fun i => shihUpperBoundaryTerm X Y (n + 1) i (0 : Fin (n + 3)))]
    congr 1
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [hUpperFaces, hLowerFaces, hUpperZeroSplit,
    sum_upper_gap_one_zero, add_assoc]
  have hcancel := sum_upper_gap_gt_one_zero_add_sum_lower_zero X Y n
  rw [← zero_add
    ((∑ i : {i : ShihIndex (n + 1) // i.gap = 1},
        gapOneBaseSummand X Y i.1 i.2) +
      (∑ i : ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ) +
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm X Y n k.succ i),
    ← hcancel]
  abel

end AlgebraicTopology.EilenbergZilber
