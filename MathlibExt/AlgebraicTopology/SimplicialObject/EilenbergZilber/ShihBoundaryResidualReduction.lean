/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryTransitionCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryLeftEdgeSum

/-!
# Reduction of the residual Shih identity to active-upper reindexing

All categorical cancellations and endpoint evaluations are discharged here.
The remaining gate is a finite equivalence identifying the nonmixed active
upper coordinates with ordinary left/right insertions and the left edge.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The sole remaining combinatorial reindexing statement for the active
upper stratum. -/
def ShihActiveUpperReindexIdentity
    (X Y : SimplicialObject C) (n : ℕ) : Prop :=
  (∑ z : ShihUpperActiveData n,
      let w := (shihUpperPositiveActiveEquiv n).symm z
      shihUpperBoundaryTerm X Y (n + 1)
        w.val.val.1 w.val.val.2.succ) =
    (∑ q : Fin (n + 1),
      (shihUpperBoundaryTerm X Y (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q 0)
          (ShihIndex.leftEdgeFace (n + 1) q 0) +
        shihUpperBoundaryTerm X Y (n + 1)
          (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
          (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1)))) +
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf 0)
          (i.leftUpperFaceOf 0)) +
      (∑ z : ShihLowerLeftData n,
        shihUpperBoundaryTerm X Y (n + 1) (z.1.leftUpperOf z.2)
          (z.1.leftUpperFaceOf z.2)) +
      (∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1)
          (i.leftUpperOf (Fin.last (i.p + 2)))
          (i.leftUpperFaceOf (Fin.last (i.p + 2))))) +
    ((∑ i : ShihIndex n,
        shihUpperBoundaryTerm X Y (n + 1) (i.rightUpperOf 0)
          (i.rightUpperFaceOf 0)) +
      ∑ z : ShihLowerRightData n,
        shihUpperBoundaryTerm X Y (n + 1) (z.1.rightUpperOf z.2)
          (z.1.rightUpperFaceOf z.2))

/-- Reindexing the positive lower-left faces yields the intrinsic faces used
by the cancellation theorem. -/
theorem reindexedLowerLeft_sum_eq_intrinsic
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihLowerLeftData n,
      let w := (shihLowerPositiveLeftEquiv n).symm z
      shihLowerBoundaryTerm X Y n w.val.val.2.succ w.val.val.1) =
    ∑ z : ShihLowerLeftData n,
      shihLowerBoundaryTerm X Y n
        (z.1.leftLowerFaceOf z.2 z.2.property.1) z.1 := by
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  dsimp only [shihLowerPositiveLeftEquiv]
  congr 1
  apply Fin.ext
  change (i.gap - 1 + a.val - 1) + 1 = i.gap - 1 + a.val
  have hg := i.gap_pos
  have ha := a.property.1
  omega

/-- Reindexing the positive lower-right faces yields the intrinsic faces used
by the cancellation theorem. -/
theorem reindexedLowerRight_sum_eq_intrinsic
    (X Y : SimplicialObject C) (n : ℕ) :
    (∑ z : ShihLowerRightData n,
      let w := (shihLowerPositiveRightEquiv n).symm z
      shihLowerBoundaryTerm X Y n w.val.val.2.succ w.val.val.1) =
    ∑ z : ShihLowerRightData n,
      shihLowerBoundaryTerm X Y n
        (z.1.rightLowerFaceOf z.2 z.2.property) z.1 := by
  apply Finset.sum_congr rfl
  rintro ⟨i, b⟩ _
  dsimp only [shihLowerPositiveRightEquiv]
  congr 1
  apply Fin.ext
  change (i.gap + i.p + b.val - 1) + 1 = i.gap + i.p + b.val
  have hb := b.property
  omega

/-- Once the finite active-upper reindexing is supplied, all remaining
categorical cancellation proves the reindexed positive-face identity. -/
theorem shihReindexedPositiveFaceIdentity_of_activeUpperReindex
    (X Y : SimplicialObject C) (n : ℕ)
    (hactive : ShihActiveUpperReindexIdentity X Y n) :
    ShihReindexedPositiveFaceIdentity X Y n := by
  rw [ShihReindexedPositiveFaceIdentity, hactive,
    reindexedLowerLeft_sum_eq_intrinsic,
    reindexedLowerRight_sum_eq_intrinsic]
  let E := ∑ q : Fin (n + 1),
    (shihUpperBoundaryTerm X Y (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) q 0)
        (ShihIndex.leftEdgeFace (n + 1) q 0) +
      shihUpperBoundaryTerm X Y (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
        (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1)))
  let T := ∑ i : ShihIndex n,
        let z := (shihUpperPositiveTransitionEquiv n).symm i
        shihUpperBoundaryTerm X Y (n + 1)
          z.val.val.1 z.val.val.2.succ
  let L0 := ∑ i : ShihIndex n,
    shihUpperBoundaryTerm X Y (n + 1) (i.leftUpperOf 0)
      (i.leftUpperFaceOf 0)
  let LI := ∑ z : ShihLowerLeftData n,
    shihUpperBoundaryTerm X Y (n + 1) (z.1.leftUpperOf z.2)
      (z.1.leftUpperFaceOf z.2)
  let LL := ∑ z : ShihLowerLeftData n,
    shihLowerBoundaryTerm X Y n
      (z.1.leftLowerFaceOf z.2 z.2.property.1) z.1
  let LE := ∑ i : ShihIndex n,
    shihUpperBoundaryTerm X Y (n + 1)
      (i.leftUpperOf (Fin.last (i.p + 2)))
      (i.leftUpperFaceOf (Fin.last (i.p + 2)))
  let R0 := ∑ i : ShihIndex n,
    shihUpperBoundaryTerm X Y (n + 1) (i.rightUpperOf 0)
      (i.rightUpperFaceOf 0)
  let RP := ∑ z : ShihLowerRightData n,
    shihUpperBoundaryTerm X Y (n + 1) (z.1.rightUpperOf z.2)
      (z.1.rightUpperFaceOf z.2)
  let LR := ∑ z : ShihLowerRightData n,
    shihLowerBoundaryTerm X Y n
      (z.1.rightLowerFaceOf z.2 z.2.property) z.1
  change T + (E + (L0 + LI + LE) + (R0 + RP)) + (LL + LR) = _
  have htransition : T + L0 = 0 := by
    dsimp only [T, L0]
    have h := transitionSum_add_leftZeroSum_eq_zero X Y n
    rw [sum_upperPositiveTransition_eq_shihIndex n
      (fun z => shihUpperBoundaryTerm X Y (n + 1)
        z.val.val.1 z.val.val.2.succ)] at h
    exact h
  have hleft : LI + LL = 0 := by
    simpa only [LI, LL] using ShihIndex.leftInteriorData_sum_eq_zero X Y n
  have hendpoint : LE + R0 = 0 := by
    simpa only [LE, R0] using
      ShihIndex.leftLastSum_add_rightZeroSum_eq_zero X Y n
  have hright : RP + LR = 0 := by
    simpa only [RP, LR] using ShihIndex.rightPositiveData_sum_eq_zero X Y n
  have hedge : E = awShuffleZeroComponent X Y (n + 1) - 𝟙 _ := by
    simpa only [E] using
      shihLeftEdge_sum_eq_awShuffleZeroComponent_sub_id X Y n
  calc
    _ = E + (T + L0) + (LI + LL) + (LE + R0) + (RP + LR) := by abel
    _ = E := by rw [htransition, hleft, hendpoint, hright]; simp
    _ = awShuffleZeroComponent X Y (n + 1) - 𝟙 _ := hedge

/-- The same reduction stated at the original positive-face API boundary. -/
theorem shihPositiveFaceIdentity_of_activeUpperReindex
    (X Y : SimplicialObject C) (n : ℕ)
    (hactive : ShihActiveUpperReindexIdentity X Y n) :
    ShihPositiveFaceIdentity X Y n :=
  (shihPositiveFaceIdentity_iff_reindexed X Y n).mpr
    (shihReindexedPositiveFaceIdentity_of_activeUpperReindex X Y n hactive)

end AlgebraicTopology.EilenbergZilber
