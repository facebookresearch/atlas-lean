/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundary
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCrossing
public import MathlibExt.Data.Set.PowersetCard

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber

namespace Shuffle

variable {p q : ℕ}

def IsLeftBoundary (s : Shuffle (p + 1) q)
    (i : Fin ((p + 1) + q + 1)) : Prop :=
  (i = 0 ∧ (0 : Fin ((p + 1) + q)) ∈ s.leftPositions) ∨
    (i = Fin.last ((p + 1) + q) ∧
      Fin.cast (by omega) (Fin.last (p + q)) ∈ s.leftPositions) ∨
    ∃ lower upper : Fin ((p + 1) + q),
      lower.val + 1 = upper.val ∧ i = upper.castSucc ∧
        lower ∈ s.leftPositions ∧ upper ∈ s.leftPositions

def leftInsertedPosition (t : Shuffle p q) (a : Fin (p + 2)) :
    Fin (p + q + 1) :=
  Fin.cases 0 (fun a' =>
    Fin.lastCases (Fin.last (p + q))
      (fun k => (t.perm (Fin.castAdd q k)).succ) a') a

def leftBoundaryIndex (t : Shuffle p q) (a : Fin (p + 2)) :
    Fin ((p + 1) + q + 1) :=
  Fin.cases 0 (fun a' =>
    Fin.lastCases (Fin.last ((p + 1) + q))
      (fun _ => Fin.cast (by omega) (leftInsertedPosition t a).castSucc) a') a

def leftInsertedPositions (t : Shuffle p q) (a : Fin (p + 2)) :
    Set.powersetCard (Fin ((p + 1) + q)) (p + 1) :=
  Set.powersetCard.map (p + 1) (finCongr (by omega)).toEmbedding <|
    Set.powersetCard.insertSuccAbove (leftInsertedPosition t a) t.leftPositions

def leftBoundaryShuffle (t : Shuffle p q) (a : Fin (p + 2)) :
    Shuffle (p + 1) q :=
  ofLeftPositions (leftInsertedPositions t a)

def leftBoundaryPair (x : Fin (p + 2) × Shuffle p q) :
    Shuffle (p + 1) q × Fin ((p + 1) + q + 1) :=
  (leftBoundaryShuffle x.2 x.1, leftBoundaryIndex x.2 x.1)

@[simp]
theorem mem_leftInsertedPositions_iff (t : Shuffle p q) (a : Fin (p + 2))
    (x : Fin ((p + 1) + q)) :
    x ∈ leftInsertedPositions t a ↔
      Fin.cast (by omega) (leftInsertedPosition t a) = x ∨
        ∃ k ∈ t.leftPositions,
          Fin.cast (by omega) ((leftInsertedPosition t a).succAbove k) = x := by
  simp [leftInsertedPositions, Set.powersetCard.mem_map_iff_mem_range,
    Fin.ext_iff, eq_comm]

theorem leftBoundaryPair_isLeftBoundary
    (x : Fin (p + 2) × Shuffle p q) :
    IsLeftBoundary (leftBoundaryPair x).1 (leftBoundaryPair x).2 := by
  rcases x with ⟨a, t⟩
  rw [leftBoundaryPair]
  change IsLeftBoundary (leftBoundaryShuffle t a) (leftBoundaryIndex t a)
  rw [IsLeftBoundary]
  refine Fin.cases ?_ (fun a' => ?_) a
  · left
    constructor
    · rfl
    · rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
        mem_leftInsertedPositions_iff]
      left
      apply Fin.ext
      rfl
  · refine Fin.lastCases ?_ (fun k => ?_) a'
    · right
      left
      constructor
      · simp only [leftBoundaryIndex, Fin.cases_succ, Fin.lastCases_last]
      · rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
          mem_leftInsertedPositions_iff]
        left
        apply Fin.ext
        simp only [leftInsertedPosition, Fin.cases_succ, Fin.lastCases_last]
    · right
      right
      let lower : Fin ((p + 1) + q) :=
        Fin.cast (by omega) (t.perm (Fin.castAdd q k)).castSucc
      let upper : Fin ((p + 1) + q) :=
        Fin.cast (by omega) (t.perm (Fin.castAdd q k)).succ
      refine ⟨lower, upper, ?_, ?_, ?_, ?_⟩
      · rfl
      · apply Fin.ext
        simp only [leftBoundaryIndex, Fin.cases_succ, Fin.lastCases_castSucc,
          leftInsertedPosition, Fin.val_cast, Fin.val_castSucc]
        change (t.perm (Fin.castAdd q k)).val + 1 = upper.val
        rfl
      · rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
          mem_leftInsertedPositions_iff]
        right
        refine ⟨t.perm (Fin.castAdd q k), ?_, ?_⟩
        · rw [mem_leftPositions_iff]
          exact ⟨k, rfl⟩
        · apply Fin.ext
          simp [lower, leftInsertedPosition]
      · rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
          mem_leftInsertedPositions_iff]
        left
        apply Fin.ext
        simp only [leftInsertedPosition, Fin.cases_succ, Fin.lastCases_castSucc,
          upper, Fin.val_cast]

theorem isLeftBoundary_not_isMixedBoundary
    {s : Shuffle (p + 1) q} {i : Fin ((p + 1) + q + 1)}
    (h : IsLeftBoundary s i) : ¬ IsMixedBoundary s i := by
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
    · exact hmixed.2 hupper'
    · exact hmixed.2 hlower'

@[simp]
theorem leftInsertedPosition_zero (t : Shuffle p q) :
    leftInsertedPosition t (0 : Fin (p + 2)) = 0 := by
  rfl

@[simp]
theorem leftInsertedPosition_last (t : Shuffle p q) :
    leftInsertedPosition t (Fin.last (p + 1)) = Fin.last (p + q) := by
  unfold leftInsertedPosition
  conv_lhs =>
    arg 3
    rw [← Fin.succ_last p]
  rw [Fin.cases_succ, Fin.lastCases_last]

@[simp]
theorem leftInsertedPosition_interior (t : Shuffle p q) (k : Fin p) :
    leftInsertedPosition t (Fin.succ (Fin.castSucc k)) =
      (t.perm (Fin.castAdd q k)).succ := by
  simp [leftInsertedPosition]

@[simp]
theorem leftBoundaryIndex_zero (t : Shuffle p q) :
    leftBoundaryIndex t (0 : Fin (p + 2)) = 0 := by
  rfl

@[simp]
theorem leftBoundaryIndex_last (t : Shuffle p q) :
    leftBoundaryIndex t (Fin.last (p + 1)) = Fin.last ((p + 1) + q) := by
  unfold leftBoundaryIndex
  conv_lhs =>
    arg 3
    rw [← Fin.succ_last p]
  rw [Fin.cases_succ, Fin.lastCases_last]

@[simp]
theorem leftBoundaryIndex_interior (t : Shuffle p q) (k : Fin p) :
    leftBoundaryIndex t (Fin.succ (Fin.castSucc k)) =
      Fin.cast (by omega) ((t.perm (Fin.castAdd q k)).succ.castSucc) := by
  simp [leftBoundaryIndex, leftInsertedPosition]

theorem leftInsertedPosition_eq_of_leftBoundaryIndex_eq
    (t₁ t₂ : Shuffle p q) (a₁ a₂ : Fin (p + 2))
    (h : leftBoundaryIndex t₁ a₁ = leftBoundaryIndex t₂ a₂) :
    leftInsertedPosition t₁ a₁ = leftInsertedPosition t₂ a₂ := by
  cases a₁ using Fin.cases with
  | zero =>
      cases a₂ using Fin.cases with
      | zero => simp
      | succ a₂' =>
          cases a₂' using Fin.lastCases with
          | last =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [Fin.succ_last, leftBoundaryIndex_zero,
                leftBoundaryIndex_last, Fin.val_zero, Fin.val_last] at hval
              omega
          | cast k₂ =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [leftBoundaryIndex_zero, leftBoundaryIndex_interior,
                Fin.val_zero, Fin.val_cast, Fin.val_castSucc, Fin.val_succ] at hval
              omega
  | succ a₁' =>
      cases a₁' using Fin.lastCases with
      | last =>
          cases a₂ using Fin.cases with
          | zero =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [Fin.succ_last, leftBoundaryIndex_last,
                leftBoundaryIndex_zero, Fin.val_last, Fin.val_zero] at hval
              omega
          | succ a₂' =>
              cases a₂' using Fin.lastCases with
              | last => simp
              | cast k₂ =>
                  exfalso
                  have hval := congrArg Fin.val h
                  have hlt := (t₂.perm (Fin.castAdd q k₂)).isLt
                  simp only [Fin.succ_last, leftBoundaryIndex_last, leftBoundaryIndex_interior,
                    Fin.val_last, Fin.val_cast, Fin.val_castSucc, Fin.val_succ] at hval
                  omega
      | cast k₁ =>
          cases a₂ using Fin.cases with
          | zero =>
              exfalso
              have hval := congrArg Fin.val h
              simp only [leftBoundaryIndex_interior, leftBoundaryIndex_zero,
                Fin.val_cast, Fin.val_castSucc, Fin.val_succ, Fin.val_zero] at hval
              omega
          | succ a₂' =>
              cases a₂' using Fin.lastCases with
              | last =>
                  exfalso
                  have hval := congrArg Fin.val h
                  have hlt := (t₁.perm (Fin.castAdd q k₁)).isLt
                  simp only [Fin.succ_last, leftBoundaryIndex_interior, leftBoundaryIndex_last,
                    Fin.val_cast, Fin.val_castSucc, Fin.val_succ, Fin.val_last] at hval
                  omega
              | cast k₂ =>
                  apply Fin.ext
                  have hval := congrArg Fin.val h
                  simpa only [leftInsertedPosition_interior, leftBoundaryIndex_interior,
                    Fin.val_cast, Fin.val_castSucc, Fin.val_succ] using hval

end Shuffle

end AlgebraicTopology.EilenbergZilber
