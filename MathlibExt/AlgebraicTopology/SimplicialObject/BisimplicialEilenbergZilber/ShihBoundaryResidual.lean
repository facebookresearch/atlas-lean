/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryActiveReindex
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryNonmixedCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryResidualReduction
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryLeftEdgeSum

/-!
# Residual cancellation in the bisimplicial Shih boundary

This file transports the fixed-bidegree cancellation theorems to intrinsic
Shih coordinates, evaluates the identity and zero-cut endpoint survivors,
and closes the active positive-face residual identity.  Consequently the
all-positive-face identity holds in every degree.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

open AlgebraicTopology.EilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- Intrinsic interior inserted-left cancellation. -/
theorem leftInteriorTerm_add_lower_eq_zero
    {n : ℕ} (i : ShihIndex n) (a : Fin (i.p + 3))
    (ha0 : 0 < a.val) (haLast : a.val < i.p + 2) :
    shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf a)
        (i.leftUpperFaceOf a) +
      shihLowerBoundaryTerm B n (i.leftLowerFaceOf a ha0) i = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihLeftBoundaryTerm_add_lower_eq_zero B
    p q m hm t a ha0 haLast
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1
  simp only [ShihIndex.leftUpperOf, ShihIndex.leftUpperFaceOf,
    ShihIndex.leftLowerFaceOf, ShihIndex.ofGap,
    ShihIndex.leftBoundaryUpperIndex, ShihIndex.leftBoundaryUpperFace,
    ShihIndex.leftBoundaryLowerFace, ShihIndex.gap, hgap]

/-- Intrinsic positive inserted-right cancellation. -/
theorem rightPositiveTerm_add_lower_eq_zero
    {n : ℕ} (i : ShihIndex n) (b : Fin (i.q + 2)) (hb : 0 < b.val) :
    shihUpperBoundaryTerm B (n + 1) (i.rightUpperOf b)
        (i.rightUpperFaceOf b) +
      shihLowerBoundaryTerm B n (i.rightLowerFaceOf b hb) i = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihRightBoundaryTerm_add_lower_eq_zero B p q m hm t b hb
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1
  simp only [ShihIndex.rightUpperOf, ShihIndex.rightUpperFaceOf,
    ShihIndex.rightLowerFaceOf, ShihIndex.ofGap,
    ShihIndex.rightBoundaryUpperIndex, ShihIndex.rightBoundaryUpperFace,
    ShihIndex.rightBoundaryLowerFace, ShihIndex.gap, hgap]

/-- Intrinsic terminal-left/initial-right cancellation. -/
theorem leftLastTerm_add_rightZeroTerm_eq_zero
    {n : ℕ} (i : ShihIndex n) :
    shihUpperBoundaryTerm B (n + 1)
        (i.leftUpperOf (Fin.last (i.p + 2)))
        (i.leftUpperFaceOf (Fin.last (i.p + 2))) +
      shihUpperBoundaryTerm B (n + 1) (i.rightUpperOf 0)
        (i.rightUpperFaceOf 0) = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihLeftLastBoundaryTerm_add_rightZero_eq_zero B p q m hm t
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1
  simp only [ShihIndex.leftUpperOf, ShihIndex.leftUpperFaceOf,
    ShihIndex.rightUpperOf, ShihIndex.rightUpperFaceOf,
    ShihIndex.leftBoundaryUpperIndex, ShihIndex.leftBoundaryUpperFace,
    ShihIndex.rightBoundaryUpperIndex, ShihIndex.rightBoundaryUpperFace,
    ShihIndex.gap, hgap]

/-- The complete intrinsic left-interior data family cancels. -/
theorem leftInteriorData_sum_eq_zero (n : ℕ) :
    (∑ z : ShihLowerLeftData n,
        shihUpperBoundaryTerm B (n + 1) (z.1.leftUpperOf z.2)
          (z.1.leftUpperFaceOf z.2)) +
      ∑ z : ShihLowerLeftData n,
        shihLowerBoundaryTerm B n
          (z.1.leftLowerFaceOf z.2 z.2.property.1) z.1 = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ =>
    leftInteriorTerm_add_lower_eq_zero B z.1 z.2
      z.2.property.1 z.2.property.2

/-- The complete intrinsic positive-right data family cancels. -/
theorem rightPositiveData_sum_eq_zero (n : ℕ) :
    (∑ z : ShihLowerRightData n,
        shihUpperBoundaryTerm B (n + 1) (z.1.rightUpperOf z.2)
          (z.1.rightUpperFaceOf z.2)) +
      ∑ z : ShihLowerRightData n,
        shihLowerBoundaryTerm B n
          (z.1.rightLowerFaceOf z.2 z.2.property) z.1 = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun z _ =>
    rightPositiveTerm_add_lower_eq_zero B z.1 z.2 z.2.property

/-- The endpoint insertion families cancel after summation. -/
theorem leftLastSum_add_rightZeroSum_eq_zero (n : ℕ) :
    (∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1)
          (i.leftUpperOf (Fin.last (i.p + 2)))
          (i.leftUpperFaceOf (Fin.last (i.p + 2)))) +
      ∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1) (i.rightUpperOf 0)
          (i.rightUpperFaceOf 0) = 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ =>
    leftLastTerm_add_rightZeroTerm_eq_zero B i

theorem raisePrefixTerm_add_leftZeroTerm_eq_zero
    {n : ℕ} (i : ShihIndex n) :
    shihUpperBoundaryTerm B (n + 1) i.raisePrefix
        (i.leftUpperFaceOf 0) +
      shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf 0)
        (i.leftUpperFaceOf 0) = 0 := by
  rcases i with ⟨⟨p, hp⟩, ⟨q, hq⟩, t⟩
  generalize hgap : n - p - q = m
  have hm : 0 < m := by
    have hq' : q < n - p := hq
    omega
  have hdegree : p + q + m = n := by omega
  have h := shihTransitionBoundaryTerm_add_leftZero_eq_zero B p q m hm t
  have hn : n = p + q + m := hdegree.symm
  subst n
  convert h using 1
  simp only [ShihIndex.raisePrefix, ShihIndex.leftUpperOf,
    ShihIndex.leftUpperFaceOf, ShihIndex.ofGap,
    ShihIndex.transitionUpperFace, ShihIndex.leftBoundaryUpperIndex,
    ShihIndex.leftBoundaryUpperFace, Shuffle.leftBoundaryIndex_zero,
    ShihIndex.gap, hgap, Fin.val_zero, Nat.add_zero]

theorem transitionCoordinateTerm_add_leftZeroTerm_eq_zero
    {n : ℕ} (i : ShihIndex n) :
    let z := (shihUpperPositiveTransitionEquiv n).symm i
    shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ +
      shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf 0)
        (i.leftUpperFaceOf 0) = 0 := by
  dsimp only
  have hindex :
      ((shihUpperPositiveTransitionEquiv n).symm i).val.val.1 =
        i.raisePrefix := rfl
  have hface :
      ((shihUpperPositiveTransitionEquiv n).symm i).val.val.2.succ =
        i.leftUpperFaceOf 0 := by
    have ht := ((shihUpperPositiveTransitionEquiv n).symm i).property
    change ((shihUpperPositiveTransitionEquiv n).symm i).val.val.2.val + 2 =
      ((shihUpperPositiveTransitionEquiv n).symm i).val.val.1.gap at ht
    rw [hindex, i.gap_raisePrefix] at ht
    apply Fin.ext
    simp only [ShihIndex.leftUpperFaceOf,
      Shuffle.leftBoundaryIndex_zero, Fin.val_succ, Fin.val_zero,
      Nat.add_zero]
    omega
  rw [hindex, hface]
  exact raisePrefixTerm_add_leftZeroTerm_eq_zero B i

/-- The transition family cancels the initial-left insertion family. -/
theorem transitionSum_add_leftZeroSum_eq_zero (n : ℕ) :
    (∑ z : ShihUpperPositiveTransitionIndex n,
        shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ) +
      ∑ i : ShihIndex n,
        shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf 0)
          (i.leftUpperFaceOf 0) = 0 := by
  rw [sum_upperPositiveTransition_eq_shihIndex,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ =>
    transitionCoordinateTerm_add_leftZeroTerm_eq_zero B i

/-- The exceptional identity survivor is the negative identity. -/
theorem shihIdentitySurvivor_eq_neg_id (n : ℕ) :
    shihUpperBoundaryTerm B (n + 1) (ShihIndex.identitySurvivor n)
      (ShihIndex.identitySurvivorFace n) =
        -𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
          (n + 1)) := by
  unfold shihUpperBoundaryTerm shihSummand shihMap
  simp only [Preadditive.zsmul_comp, smul_smul]
  have hd :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (ShihIndex.identitySurvivorFace n) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (ShihIndex.identitySurvivorFace n))
          (SimplexCategory.δ (ShihIndex.identitySurvivorFace n)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hd, AlgebraicTopology.Bisimplicial.map_comp]
  have hmap := congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (ShihIndex.delta_identitySurvivorFace_comp_leftHom n)
    (ShihIndex.delta_identitySurvivorFace_comp_rightHom n)
  rw [hmap, AlgebraicTopology.Bisimplicial.map_id,
    ShihIndex.identitySurvivor_sign]
  have hcoeff :
      ((-1 : ℤ) ^ (ShihIndex.identitySurvivorFace n).val) *
          (-1 : ℤ) ^ n = -1 := by
    calc
      _ = (-1 : ℤ) ^ (n + 1 + n) := by
        simp only [ShihIndex.identitySurvivorFace, pow_add]
      _ = (-1 : ℤ) ^ (2 * n + 1) := by congr 1; omega
      _ = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [hcoeff]
  simp

/-- The exceptional zero-cut bisimplicial AW--shuffle map. -/
noncomputable def zeroCutAlexanderWhitneyShuffleTerm (n : ℕ) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        (n + 1) :=
  AlgebraicTopology.Bisimplicial.map B
    (SimplexCategory.const ⦋n + 1⦌ ⦋n + 1⦌ 0) (𝟙 ⦋n + 1⦌)

theorem shihZeroCutSurvivor_eq (n : ℕ) :
    shihUpperBoundaryTerm B (n + 1) (ShihIndex.zeroCutSurvivor n)
        (ShihIndex.zeroCutSurvivorFace n) =
      zeroCutAlexanderWhitneyShuffleTerm B n := by
  unfold shihUpperBoundaryTerm shihSummand shihMap
    zeroCutAlexanderWhitneyShuffleTerm
  simp only [Preadditive.zsmul_comp, smul_smul]
  have hd :
      ((SimplicialObject.diagonalFunctor A).obj B).δ
          (ShihIndex.zeroCutSurvivorFace n) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (ShihIndex.zeroCutSurvivorFace n))
          (SimplexCategory.δ (ShihIndex.zeroCutSurvivorFace n)) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hd, AlgebraicTopology.Bisimplicial.map_comp]
  have hmap := congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (ShihIndex.delta_zeroCutSurvivorFace_comp_leftHom n)
    (ShihIndex.delta_zeroCutSurvivorFace_comp_rightHom n)
  rw [hmap, ShihIndex.zeroCutSurvivor_sign]
  have hcoeff :
      (-1 : ℤ) ^ (ShihIndex.zeroCutSurvivorFace n).val *
          (-1 : ℤ) ^ n = 1 := by
    rw [← pow_add]
    have heven : (ShihIndex.zeroCutSurvivorFace n).val + n =
        2 * (n + 1) := by
      change n + 2 + n = 2 * (n + 1)
      omega
    rw [heven, pow_mul]
    norm_num
  rw [hcoeff]
  simp

theorem zeroCutAlexanderWhitneyShuffleTerm_eq_awShuffleZeroComponent
    (n : ℕ) :
    zeroCutAlexanderWhitneyShuffleTerm B n =
      awShuffleZeroComponent B (n + 1) := by
  let _ := AlgebraicTopology.EilenbergZilber.Shuffle.leftZeroUnique (n + 1)
  unfold awShuffleZeroComponent
  rw [Fintype.sum_unique]
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle
    (q := n + 1) (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 (n + 1))]
  have hfrontZero :
      (AlgebraicTopology.AlexanderWhitney.frontInclusion 0 (n + 1) (n + 1)
        (by omega)).toOrderHom 0 = 0 := by
    rfl
  unfold zeroCutAlexanderWhitneyShuffleTerm awShuffleDiagonalSummand
    AlgebraicTopology.EilenbergZilber.awShuffleLeftHom
    AlgebraicTopology.EilenbergZilber.awShuffleRightHom
  simp [AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_leftHom,
    hfrontZero,
    AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_rightHom,
    AlgebraicTopology.AlexanderWhitney.backInclusion, SimplexCategory.δ₀Iter_zero,
    AlgebraicTopology.Bisimplicial.map]

/-- The terminal zero-cut survivor is the omitted zero-cut component. -/
theorem shihZeroCutSurvivor_eq_awShuffleZeroComponent (n : ℕ) :
    shihUpperBoundaryTerm B (n + 1) (ShihIndex.zeroCutSurvivor n)
        (ShihIndex.zeroCutSurvivorFace n) =
      awShuffleZeroComponent B (n + 1) := by
  rw [shihZeroCutSurvivor_eq,
    zeroCutAlexanderWhitneyShuffleTerm_eq_awShuffleZeroComponent]

/-- The complete left edge telescopes from minus identity to the zero cut. -/
theorem shihLeftEdge_sum_eq_awShuffleZeroComponent_sub_id (n : ℕ) :
    (∑ q : Fin (n + 1),
        (shihUpperBoundaryTerm B (n + 1)
            (ShihIndex.leftEdgeIndex (n + 1) q 0)
            (ShihIndex.leftEdgeFace (n + 1) q 0) +
          shihUpperBoundaryTerm B (n + 1)
            (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
            (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1)))) =
      awShuffleZeroComponent B (n + 1) -
        𝟙 ((AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
          (n + 1)) := by
  rw [AlgebraicTopology.EilenbergZilber.sum_fin_pairs_eq_endpoints_of_adjacent_cancel]
  · rw [ShihIndex.leftEdgeIndex_zero_eq_identitySurvivor,
      ShihIndex.leftEdgeFace_zero_eq_identitySurvivorFace,
      ShihIndex.leftEdgeIndex_last_eq_zeroCutSurvivor,
      ShihIndex.leftEdgeFace_last_eq_zeroCutSurvivorFace,
      shihIdentitySurvivor_eq_neg_id,
      shihZeroCutSurvivor_eq_awShuffleZeroComponent]
    abel
  · intro q
    exact shihLeftEdge_last_add_zeroSucc_eq_zero B n q

theorem reindexedLowerLeft_sum_eq_intrinsic (n : ℕ) :
    (∑ z : ShihLowerLeftData n,
      let w := (shihLowerPositiveLeftEquiv n).symm z
      shihLowerBoundaryTerm B n w.val.val.2.succ w.val.val.1) =
    ∑ z : ShihLowerLeftData n,
      shihLowerBoundaryTerm B n
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

theorem reindexedLowerRight_sum_eq_intrinsic (n : ℕ) :
    (∑ z : ShihLowerRightData n,
      let w := (shihLowerPositiveRightEquiv n).symm z
      shihLowerBoundaryTerm B n w.val.val.2.succ w.val.val.1) =
    ∑ z : ShihLowerRightData n,
      shihLowerBoundaryTerm B n
        (z.1.rightLowerFaceOf z.2 z.2.property) z.1 := by
  apply Finset.sum_congr rfl
  rintro ⟨i, b⟩ _
  dsimp only [shihLowerPositiveRightEquiv]
  congr 1
  apply Fin.ext
  change (i.gap + i.p + b.val - 1) + 1 = i.gap + i.p + b.val
  have hb := b.property
  omega

/-- Active-upper reindexing implies the reindexed positive-face identity. -/
theorem shihReindexedPositiveFaceIdentity_of_activeUpperReindex
    (n : ℕ) (hactive : ShihActiveUpperReindexIdentity B n) :
    ShihReindexedPositiveFaceIdentity B n := by
  rw [ShihReindexedPositiveFaceIdentity]
  unfold ShihActiveUpperReindexIdentity at hactive
  unfold shihUpperActiveDataTerm at hactive
  rw [hactive,
    reindexedLowerLeft_sum_eq_intrinsic,
    reindexedLowerRight_sum_eq_intrinsic]
  let E := ∑ q : Fin (n + 1),
    (shihUpperBoundaryTerm B (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) q 0)
        (ShihIndex.leftEdgeFace (n + 1) q 0) +
      shihUpperBoundaryTerm B (n + 1)
        (ShihIndex.leftEdgeIndex (n + 1) q (Fin.last 1))
        (ShihIndex.leftEdgeFace (n + 1) q (Fin.last 1)))
  let T := ∑ i : ShihIndex n,
    let z := (shihUpperPositiveTransitionEquiv n).symm i
    shihUpperBoundaryTerm B (n + 1) z.val.val.1 z.val.val.2.succ
  let L0 := ∑ i : ShihIndex n,
    shihUpperBoundaryTerm B (n + 1) (i.leftUpperOf 0)
      (i.leftUpperFaceOf 0)
  let LI := ∑ z : ShihLowerLeftData n,
    shihUpperBoundaryTerm B (n + 1) (z.1.leftUpperOf z.2)
      (z.1.leftUpperFaceOf z.2)
  let LL := ∑ z : ShihLowerLeftData n,
    shihLowerBoundaryTerm B n
      (z.1.leftLowerFaceOf z.2 z.2.property.1) z.1
  let LE := ∑ i : ShihIndex n,
    shihUpperBoundaryTerm B (n + 1)
      (i.leftUpperOf (Fin.last (i.p + 2)))
      (i.leftUpperFaceOf (Fin.last (i.p + 2)))
  let R0 := ∑ i : ShihIndex n,
    shihUpperBoundaryTerm B (n + 1) (i.rightUpperOf 0)
      (i.rightUpperFaceOf 0)
  let RP := ∑ z : ShihLowerRightData n,
    shihUpperBoundaryTerm B (n + 1) (z.1.rightUpperOf z.2)
      (z.1.rightUpperFaceOf z.2)
  let LR := ∑ z : ShihLowerRightData n,
    shihLowerBoundaryTerm B n
      (z.1.rightLowerFaceOf z.2 z.2.property) z.1
  change T + (E + (L0 + LI + LE) + (R0 + RP)) + (LL + LR) = _
  have htransition : T + L0 = 0 := by
    dsimp only [T, L0]
    have h := transitionSum_add_leftZeroSum_eq_zero B n
    rw [sum_upperPositiveTransition_eq_shihIndex n
      (fun z => shihUpperBoundaryTerm B (n + 1)
        z.val.val.1 z.val.val.2.succ)] at h
    exact h
  have hleft : LI + LL = 0 := by
    simpa only [LI, LL] using leftInteriorData_sum_eq_zero B n
  have hendpoint : LE + R0 = 0 := by
    simpa only [LE, R0] using leftLastSum_add_rightZeroSum_eq_zero B n
  have hright : RP + LR = 0 := by
    simpa only [RP, LR] using rightPositiveData_sum_eq_zero B n
  have hedge : E = awShuffleZeroComponent B (n + 1) - 𝟙 _ := by
    simpa only [E] using shihLeftEdge_sum_eq_awShuffleZeroComponent_sub_id B n
  calc
    _ = E + (T + L0) + (LI + LL) + (LE + R0) + (RP + LR) := by abel
    _ = E := by rw [htransition, hleft, hendpoint, hright]; simp
    _ = awShuffleZeroComponent B (n + 1) - 𝟙 _ := hedge

/-- Active-upper reindexing implies the original positive-face identity. -/
theorem shihPositiveFaceIdentity_of_activeUpperReindex
    (n : ℕ) (hactive : ShihActiveUpperReindexIdentity B n) :
    ShihPositiveFaceIdentity B n :=
  (shihPositiveFaceIdentity_iff_reindexed B n).mpr
    (shihReindexedPositiveFaceIdentity_of_activeUpperReindex B n hactive)

/-- The bisimplicial Shih positive-face identity in every degree. -/
theorem shihPositiveFaceIdentity (n : ℕ) :
    ShihPositiveFaceIdentity B n :=
  shihPositiveFaceIdentity_of_activeUpperReindex B n
    (shihActiveUpperReindexIdentity B n)

end AlgebraicTopology.BisimplicialEilenbergZilber
