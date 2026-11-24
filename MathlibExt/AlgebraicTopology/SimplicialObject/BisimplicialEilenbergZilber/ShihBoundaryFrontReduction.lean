/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihDerivedBoundary
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOneSurvivor

/-!
# Front-face reduction for the bisimplicial Shih boundary

The front faces of gap-greater-than-one indices cancel the lower front
faces after the existing successor reindexing.  Gap-one front faces survive
and are identified with the positive-cut Alexander--Whitney--shuffle terms.
This yields the standard reduction from the complete boundary to the
gap-one survivor plus positive faces.
-/

@[expose] public section

open CategoryTheory Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

/-- The bisimplicial Alexander--Whitney--shuffle summand encoded by a gap-one Shih index. -/
noncomputable def gapOneBaseSummand {n : ℕ}
    (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) (hi : i.gap = 1) :
    (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n :=
  AlgebraicTopology.EilenbergZilber.shuffleSignZ i.shuffle •
    AlgebraicTopology.Bisimplicial.map B
      (i.gapOneBaseLeftHom hi) (i.gapOneBaseRightHom hi)

/-- A derived front upper face cancels the corresponding lower front face. -/
theorem shihBoundaryTerm_succ_zero_add_lower_zero
    {n : ℕ} (i : AlgebraicTopology.EilenbergZilber.ShihIndex n) :
    shihUpperBoundaryTerm B (n + 1) i.succ (0 : Fin (n + 3)) +
      shihLowerBoundaryTerm B n (0 : Fin (n + 2)) i = 0 := by
  unfold shihUpperBoundaryTerm shihLowerBoundaryTerm shihSummand shihMap
  simp only [Fin.val_zero, pow_zero,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
    AlgebraicTopology.EilenbergZilber.ShihIndex.succ_sign,
    AlgebraicTopology.EilenbergZilber.ShihIndex.succ_leftHom,
    AlgebraicTopology.EilenbergZilber.ShihIndex.succ_rightHom]
  have hdUpper :
      ((SimplicialObject.diagonalFunctor A).obj B).δ (0 : Fin (n + 3)) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (0 : Fin (n + 3)))
          (SimplexCategory.δ (0 : Fin (n + 3))) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  have hdLower :
      ((SimplicialObject.diagonalFunctor A).obj B).δ (0 : Fin (n + 2)) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (0 : Fin (n + 2)))
          (SimplexCategory.δ (0 : Fin (n + 2))) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hdUpper, AlgebraicTopology.Bisimplicial.map_comp]
  rw [hdLower, AlgebraicTopology.Bisimplicial.map_comp]
  have hmap := congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (AlgebraicTopology.EilenbergZilber.δ_zero_comp_derivedSimplexHom i.leftHom)
    (AlgebraicTopology.EilenbergZilber.δ_zero_comp_derivedSimplexHom i.rightHom)
  rw [hmap]
  simp only [one_mul, neg_smul, neg_add_cancel]

/-- All gap-greater-than-one upper front faces cancel all lower front faces. -/
theorem sum_upper_gap_gt_one_zero_add_sum_lower_zero (n : ℕ) :
    (∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) // 1 < i.gap},
        shihUpperBoundaryTerm B (n + 1) i.1 (0 : Fin (n + 3))) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        shihLowerBoundaryTerm B n (0 : Fin (n + 2)) i = 0 := by
  calc
    _ = ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        (shihUpperBoundaryTerm B (n + 1) i.succ (0 : Fin (n + 3)) +
          shihLowerBoundaryTerm B n (0 : Fin (n + 2)) i) := by
      have hindex :
          (∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
              1 < i.gap},
              shihUpperBoundaryTerm B (n + 1) i.1 (0 : Fin (n + 3))) =
            ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
              shihUpperBoundaryTerm B (n + 1) i.succ (0 : Fin (n + 3)) :=
        AlgebraicTopology.EilenbergZilber.ShihIndex.sum_gap_gt_one fun i =>
          shihUpperBoundaryTerm B (n + 1) i (0 : Fin (n + 3))
      rw [hindex, Finset.sum_add_distrib]
    _ = 0 := Finset.sum_eq_zero fun i _ =>
      shihBoundaryTerm_succ_zero_add_lower_zero B i

/-- The front face of a gap-one Shih summand is its base AW--shuffle summand. -/
theorem shihUpperBoundaryTerm_zero_of_gap_eq_one
    {n : ℕ} (i : AlgebraicTopology.EilenbergZilber.ShihIndex n)
    (hi : i.gap = 1) :
    shihUpperBoundaryTerm B n i (0 : Fin (n + 2)) =
      gapOneBaseSummand B i hi := by
  unfold shihUpperBoundaryTerm shihSummand shihMap gapOneBaseSummand
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  rw [i.sign_of_gap_eq_one hi]
  rw [Preadditive.zsmul_comp]
  have hd :
      ((SimplicialObject.diagonalFunctor A).obj B).δ (0 : Fin (n + 2)) =
        AlgebraicTopology.Bisimplicial.map B
          (SimplexCategory.δ (0 : Fin (n + 2)))
          (SimplexCategory.δ (0 : Fin (n + 2))) := by
    exact (AlgebraicTopology.Bisimplicial.map_diagonal B _).symm
  rw [hd, AlgebraicTopology.Bisimplicial.map_comp]
  have hleft := i.δ_zero_comp_leftHom_of_gap_eq_one hi
  have hright := i.δ_zero_comp_rightHom_of_gap_eq_one hi
  unfold AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneBaseLeftHom
    AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneBaseRightHom
  exact congrArg
    (fun k => AlgebraicTopology.EilenbergZilber.shuffleSignZ i.shuffle • k)
    (congrArg₂ (AlgebraicTopology.Bisimplicial.map B) hleft hright)

/-- The full gap-one front-face sum is the sum of its base survivors. -/
theorem sum_upper_gap_one_zero (n : ℕ) :
    ∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex n // i.gap = 1},
        shihUpperBoundaryTerm B n i.1 (0 : Fin (n + 2)) =
      ∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex n // i.gap = 1},
        gapOneBaseSummand B i.1 i.2 := by
  exact Finset.sum_congr rfl fun i _ =>
    shihUpperBoundaryTerm_zero_of_gap_eq_one B i.1 i.2

/-- A gap-one base summand is the corresponding positive-cut diagonal summand. -/
theorem gapOneBaseSummand_eq_awShuffleDiagonalSummand
    (n : ℕ) (x : AlgebraicTopology.EilenbergZilber.ShihIndex.GapOneShuffleIndex n) :
    gapOneBaseSummand B
        ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).1
        ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).2 =
      awShuffleDiagonalSummand B n x.1.succ x.2 := by
  rcases x with ⟨p, s⟩
  dsimp only [AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv,
    AlgebraicTopology.EilenbergZilber.ShihIndex.ofGapOneShuffleIndex,
    Equiv.symm_apply_apply]
  unfold gapOneBaseSummand
    AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneBaseLeftHom
    AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneBaseRightHom
    awShuffleDiagonalSummand
    AlgebraicTopology.EilenbergZilber.awShuffleLeftHom
    AlgebraicTopology.EilenbergZilber.awShuffleRightHom
  rfl

/-- Reindex the gap-one base family by positive Alexander--Whitney cuts. -/
theorem sum_gapOneBaseSummand (n : ℕ) :
    ∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex n // i.gap = 1},
        gapOneBaseSummand B i.1 i.2 =
      ∑ p : Fin n,
        ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle
            (p.val + 1) (n - (p.val + 1)),
          awShuffleDiagonalSummand B n p.succ s := by
  calc
    _ = ∑ x : AlgebraicTopology.EilenbergZilber.ShihIndex.GapOneShuffleIndex n,
          gapOneBaseSummand B
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).1
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).2 := by
      simpa using
        (AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).sum_comp
          (fun x => gapOneBaseSummand B
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).1
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).2)
    _ = _ := by
      refine (Fintype.sum_sigma
        (fun x : AlgebraicTopology.EilenbergZilber.ShihIndex.GapOneShuffleIndex n =>
          gapOneBaseSummand B
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).1
            ((AlgebraicTopology.EilenbergZilber.ShihIndex.gapOneEquiv n).symm x).2)).trans ?_
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ =>
        gapOneBaseSummand_eq_awShuffleDiagonalSummand B n ⟨p, s⟩

/-- The gap-one base sum is the full AW--shuffle sum minus its zero cut. -/
theorem sum_gapOneBaseSummand_eq_awShuffle_sub_zero (n : ℕ) :
    ∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex n // i.gap = 1},
        gapOneBaseSummand B i.1 i.2 =
      awShuffleDiagonalComponent B n - awShuffleZeroComponent B n := by
  rw [eq_sub_iff_add_eq, add_comm]
  unfold awShuffleDiagonalComponent awShuffleZeroComponent
  rw [Fin.sum_univ_succ, sum_gapOneBaseSummand]
  rfl

/-- Reduce the complete Shih boundary to gap-one survivors and positive faces. -/
theorem shihBoundary_sum_reduction (n : ℕ) :
    (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
        ∑ k : Fin (n + 3), shihUpperBoundaryTerm B (n + 1) i k) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        ∑ k : Fin (n + 2), shihLowerBoundaryTerm B n k i =
    (∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
        i.gap = 1}, gapOneBaseSummand B i.1 i.2) +
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i := by
  have hUpperFaces :
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
          ∑ k : Fin (n + 3), shihUpperBoundaryTerm B (n + 1) i k) =
        (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
            shihUpperBoundaryTerm B (n + 1) i (0 : Fin (n + 3))) +
          ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
            ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_succ _
  have hLowerFaces :
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
          ∑ k : Fin (n + 2), shihLowerBoundaryTerm B n k i) =
        (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
            shihLowerBoundaryTerm B n (0 : Fin (n + 2)) i) +
          ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
            ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_succ _
  let e :
      {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
        ¬i.gap = 1} ≃
      {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
        1 < i.gap} :=
    Equiv.subtypeEquivProp (by
      funext i
      apply propext
      have hi := i.gap_pos
      omega)
  have hUpperZeroSplit :
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
          shihUpperBoundaryTerm B (n + 1) i (0 : Fin (n + 3))) =
        (∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
            i.gap = 1},
            shihUpperBoundaryTerm B (n + 1) i.1 (0 : Fin (n + 3))) +
          ∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
            1 < i.gap},
            shihUpperBoundaryTerm B (n + 1) i.1 (0 : Fin (n + 3)) := by
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) =>
        i.gap = 1)
      (fun i => shihUpperBoundaryTerm B (n + 1) i (0 : Fin (n + 3)))]
    congr 1
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [hUpperFaces, hLowerFaces, hUpperZeroSplit,
    sum_upper_gap_one_zero, add_assoc]
  have hcancel := sum_upper_gap_gt_one_zero_add_sum_lower_zero B n
  rw [← zero_add
    ((∑ i : {i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1) //
        i.gap = 1}, gapOneBaseSummand B i.1 i.2) +
      (∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex (n + 1),
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm B (n + 1) i k.succ) +
      ∑ i : AlgebraicTopology.EilenbergZilber.ShihIndex n,
        ∑ k : Fin (n + 1), shihLowerBoundaryTerm B n k.succ i),
    ← hcancel]
  abel

end AlgebraicTopology.BisimplicialEilenbergZilber
