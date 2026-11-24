/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundary
public import MathlibExt.Data.Set.PowersetCard

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}

def IsRightBoundary (s : Shuffle p (q + 1))
    (i : Fin (p + (q + 1) + 1)) : Prop :=
  (i = 0 ∧ (0 : Fin (p + (q + 1))) ∈ s.rightPositions) ∨
    (i = Fin.last (p + (q + 1)) ∧
      Fin.cast (by omega) (Fin.last (p + q)) ∈ s.rightPositions) ∨
    ∃ lower upper : Fin (p + (q + 1)),
      lower.val + 1 = upper.val ∧ i = upper.castSucc ∧
        lower ∈ s.rightPositions ∧ upper ∈ s.rightPositions

def rightInsertedPosition (t : Shuffle p q) (b : Fin (q + 2)) :
    Fin (p + q + 1) :=
  Fin.cases 0 (fun b' =>
    Fin.lastCases (Fin.last (p + q))
      (fun k => (t.perm (Fin.natAdd p k)).succ) b') b

def rightBoundaryIndex (t : Shuffle p q) (b : Fin (q + 2)) :
    Fin (p + (q + 1) + 1) :=
  Fin.cases 0 (fun b' =>
    Fin.lastCases (Fin.last (p + (q + 1)))
      (fun _ => Fin.cast (by omega) (rightInsertedPosition t b).castSucc) b') b

def rightInsertedPositions (t : Shuffle p q) (b : Fin (q + 2)) :
    Set.powersetCard (Fin (p + (q + 1))) (q + 1) :=
  Set.powersetCard.map (q + 1) (finCongr (by omega)).toEmbedding <|
    Set.powersetCard.insertSuccAbove (rightInsertedPosition t b) t.rightPositions

def rightBoundaryShuffle (t : Shuffle p q) (b : Fin (q + 2)) :
    Shuffle p (q + 1) :=
  ofRightPositions (rightInsertedPositions t b)

def rightBoundaryPair (x : Fin (q + 2) × Shuffle p q) :
    Shuffle p (q + 1) × Fin (p + (q + 1) + 1) :=
  (rightBoundaryShuffle x.2 x.1, rightBoundaryIndex x.2 x.1)

@[simp]
theorem mem_rightInsertedPositions_iff (t : Shuffle p q) (b : Fin (q + 2))
    (x : Fin (p + (q + 1))) :
    x ∈ rightInsertedPositions t b ↔
      Fin.cast (by omega) (rightInsertedPosition t b) = x ∨
        ∃ k ∈ t.rightPositions,
          Fin.cast (by omega) ((rightInsertedPosition t b).succAbove k) = x := by
  simp [rightInsertedPositions, Fin.ext_iff, eq_comm]

theorem rightBoundaryPair_isRightBoundary
    (x : Fin (q + 2) × Shuffle p q) :
    IsRightBoundary (rightBoundaryPair x).1 (rightBoundaryPair x).2 := by
  rcases x with ⟨b, t⟩
  rw [rightBoundaryPair]
  change IsRightBoundary (rightBoundaryShuffle t b) (rightBoundaryIndex t b)
  rw [IsRightBoundary]
  refine Fin.cases ?_ (fun b' => ?_) b
  · left
    constructor
    · rfl
    · rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
        mem_rightInsertedPositions_iff]
      left
      apply Fin.ext
      rfl
  · refine Fin.lastCases ?_ (fun k => ?_) b'
    · right
      left
      constructor
      · simp only [rightBoundaryIndex, Fin.cases_succ, Fin.lastCases_last]
      · rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
          mem_rightInsertedPositions_iff]
        left
        apply Fin.ext
        simp only [rightInsertedPosition, Fin.cases_succ, Fin.lastCases_last]
    · right
      right
      let lower : Fin (p + (q + 1)) :=
        Fin.cast (by omega) (t.perm (Fin.natAdd p k)).castSucc
      let upper : Fin (p + (q + 1)) :=
        Fin.cast (by omega) (t.perm (Fin.natAdd p k)).succ
      refine ⟨lower, upper, ?_, ?_, ?_, ?_⟩
      · rfl
      · apply Fin.ext
        simp only [rightBoundaryIndex, Fin.cases_succ, Fin.lastCases_castSucc,
          rightInsertedPosition, Fin.val_cast, Fin.val_castSucc]
        change (t.perm (Fin.natAdd p k)).val + 1 = upper.val
        rfl
      · rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
          mem_rightInsertedPositions_iff]
        right
        refine ⟨t.perm (Fin.natAdd p k), ?_, ?_⟩
        · rw [mem_rightPositions_iff]
          exact ⟨k, rfl⟩
        · apply Fin.ext
          simp [lower, rightInsertedPosition]
      · rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
          mem_rightInsertedPositions_iff]
        left
        apply Fin.ext
        simp only [rightInsertedPosition, Fin.cases_succ, Fin.lastCases_castSucc,
          upper, Fin.val_cast]

theorem isRightBoundary_not_isMixedBoundary
    {s : Shuffle p (q + 1)} {i : Fin (p + (q + 1) + 1)}
    (h : IsRightBoundary s i) : ¬ IsMixedBoundary s i := by
  rintro ⟨lower, upper, hadj, hi, hmixed⟩
  rcases h with hzero | hlast | hinterior
  · have hu : 0 < upper.val := by omega
    have := congrArg Fin.val (hzero.1.symm.trans hi)
    simp at this
    omega
  · have hval := congrArg Fin.val (hlast.1.symm.trans hi)
    have hu := upper.isLt
    simp at hval
    omega
  · obtain ⟨lower', upper', hadj', hi', hlower', hupper'⟩ := hinterior
    have hupperEq : upper' = upper := by
      apply Fin.ext
      have := congrArg Fin.val (hi'.symm.trans hi)
      simpa using this
    have hlowerEq : lower' = lower := by
      apply Fin.ext
      have hu := congrArg Fin.val hupperEq
      omega
    subst lower'
    subst upper'
    rcases hmixed with hmixed | hmixed
    · exact (mem_rightPositions_iff_not_mem_leftPositions s lower).mp
        hlower' hmixed.1
    · exact (mem_rightPositions_iff_not_mem_leftPositions s upper).mp
        hupper' hmixed.1

@[simp]
theorem rightInsertedPosition_zero (t : Shuffle p q) :
    rightInsertedPosition t (0 : Fin (q + 2)) = 0 := by
  rfl

@[simp]
theorem rightInsertedPosition_last (t : Shuffle p q) :
    rightInsertedPosition t (Fin.last (q + 1)) = Fin.last (p + q) := by
  unfold rightInsertedPosition
  conv_lhs =>
    arg 3
    rw [← Fin.succ_last q]
  rw [Fin.cases_succ, Fin.lastCases_last]

@[simp]
theorem rightInsertedPosition_interior (t : Shuffle p q) (k : Fin q) :
    rightInsertedPosition t (Fin.succ (Fin.castSucc k)) =
      (t.perm (Fin.natAdd p k)).succ := by
  simp [rightInsertedPosition]

@[simp]
theorem rightBoundaryIndex_zero (t : Shuffle p q) :
    rightBoundaryIndex t (0 : Fin (q + 2)) = 0 := by
  rfl

@[simp]
theorem rightBoundaryIndex_last (t : Shuffle p q) :
    rightBoundaryIndex t (Fin.last (q + 1)) = Fin.last (p + (q + 1)) := by
  unfold rightBoundaryIndex
  conv_lhs =>
    arg 3
    rw [← Fin.succ_last q]
  rw [Fin.cases_succ, Fin.lastCases_last]

@[simp]
theorem rightBoundaryIndex_interior (t : Shuffle p q) (k : Fin q) :
    rightBoundaryIndex t (Fin.succ (Fin.castSucc k)) =
      Fin.cast (by omega) ((t.perm (Fin.natAdd p k)).succ.castSucc) := by
  simp [rightBoundaryIndex, rightInsertedPosition]

theorem rightInsertedPosition_eq_of_rightBoundaryIndex_eq
    (t₁ t₂ : Shuffle p q) (b₁ b₂ : Fin (q + 2))
    (h : rightBoundaryIndex t₁ b₁ = rightBoundaryIndex t₂ b₂) :
    rightInsertedPosition t₁ b₁ = rightInsertedPosition t₂ b₂ := by
  cases b₁ using Fin.cases with
  | zero =>
      cases b₂ using Fin.cases with
      | zero => simp
      | succ b₂' =>
          cases b₂' using Fin.lastCases with
          | last =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [Fin.succ_last, rightBoundaryIndex_zero,
                rightBoundaryIndex_last, Fin.val_zero, Fin.val_last] at hval
              omega
          | cast k₂ =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [rightBoundaryIndex_zero, rightBoundaryIndex_interior,
                Fin.val_zero, Fin.val_cast, Fin.val_castSucc, Fin.val_succ] at hval
              omega
  | succ b₁' =>
      cases b₁' using Fin.lastCases with
      | last =>
          cases b₂ using Fin.cases with
          | zero =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [Fin.succ_last, rightBoundaryIndex_last,
                rightBoundaryIndex_zero, Fin.val_last, Fin.val_zero] at hval
              omega
          | succ b₂' =>
              cases b₂' using Fin.lastCases with
              | last => simp
              | cast k₂ =>
                  exfalso
                  have hval := congrArg Fin.val h
                  have hlt := (t₂.perm (Fin.natAdd p k₂)).isLt
                  simp only [Fin.succ_last, rightBoundaryIndex_last,
                    rightBoundaryIndex_interior, Fin.val_last, Fin.val_cast,
                    Fin.val_castSucc, Fin.val_succ] at hval
                  omega
      | cast k₁ =>
          cases b₂ using Fin.cases with
          | zero =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [rightBoundaryIndex_interior, rightBoundaryIndex_zero,
                Fin.val_cast, Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at hval
              omega
          | succ b₂' =>
              cases b₂' using Fin.lastCases with
              | last =>
                  exfalso
                  have hval := congrArg Fin.val h
                  have hlt := (t₁.perm (Fin.natAdd p k₁)).isLt
                  simp only [Fin.succ_last, rightBoundaryIndex_interior,
                    rightBoundaryIndex_last, Fin.val_cast, Fin.val_castSucc,
                    Fin.val_succ, Fin.val_last] at hval
                  omega
              | cast k₂ =>
                  apply Fin.ext
                  have hval := congrArg Fin.val h
                  simpa only [rightInsertedPosition_interior,
                    rightBoundaryIndex_interior, Fin.val_cast,
                    Fin.val_castSucc, Fin.val_succ] using hval

end AlgebraicTopology.EilenbergZilber.Shuffle
