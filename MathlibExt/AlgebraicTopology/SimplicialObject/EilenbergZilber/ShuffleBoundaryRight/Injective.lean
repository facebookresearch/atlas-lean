/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Basic

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}

theorem rightBoundaryIndex_injective (t : Shuffle p q) :
    Function.Injective (rightBoundaryIndex t) := by
  intro b₁ b₂ h
  cases b₁ using Fin.cases with
  | zero =>
      cases b₂ using Fin.cases with
      | zero => rfl
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
              | last => rfl
              | cast k₂ =>
                  exfalso
                  have hval := congrArg Fin.val h
                  have hlt := (t.perm (Fin.natAdd p k₂)).isLt
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
                  have hlt := (t.perm (Fin.natAdd p k₁)).isLt
                  simp only [Fin.succ_last, rightBoundaryIndex_interior,
                    rightBoundaryIndex_last, Fin.val_cast, Fin.val_castSucc,
                    Fin.val_succ, Fin.val_last] at hval
                  omega
              | cast k₂ =>
                  have hperm :
                      t.perm (Fin.natAdd p k₁) =
                        t.perm (Fin.natAdd p k₂) := by
                    apply Fin.ext
                    have hval := congrArg Fin.val h
                    simp only [rightBoundaryIndex_interior, Fin.val_cast,
                      Fin.val_castSucc, Fin.val_succ] at hval
                    omega
                  have hkNat : Fin.natAdd p k₁ = Fin.natAdd p k₂ :=
                    t.perm.injective hperm
                  have hk : k₁ = k₂ := Fin.natAdd_injective q p hkNat
                  subst k₂
                  rfl

theorem rightBoundaryPair_injective :
    Function.Injective (rightBoundaryPair (p := p) (q := q)) := by
  rintro ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ h
  have hShuffle : rightBoundaryShuffle t₁ b₁ = rightBoundaryShuffle t₂ b₂ :=
    congrArg Prod.fst h
  have hIndex : rightBoundaryIndex t₁ b₁ = rightBoundaryIndex t₂ b₂ :=
    congrArg Prod.snd h
  have hPositions : rightInsertedPositions t₁ b₁ = rightInsertedPositions t₂ b₂ := by
    simpa only [rightBoundaryShuffle, rightPositions_ofRightPositions] using
      congrArg rightPositions hShuffle
  have hInserted : rightInsertedPosition t₁ b₁ = rightInsertedPosition t₂ b₂ :=
    rightInsertedPosition_eq_of_rightBoundaryIndex_eq t₁ t₂ b₁ b₂ hIndex
  let e : Fin (p + q + 1) ≃ Fin (p + (q + 1)) := finCongr (by omega)
  have hMap :
      Set.powersetCard.map (q + 1) e.toEmbedding
          (Set.powersetCard.insertSuccAbove
            (rightInsertedPosition t₂ b₂) t₁.rightPositions) =
        Set.powersetCard.map (q + 1) e.toEmbedding
          (Set.powersetCard.insertSuccAbove
            (rightInsertedPosition t₂ b₂) t₂.rightPositions) := by
    simpa only [rightInsertedPositions, hInserted, e] using hPositions
  have hInsert :
      Set.powersetCard.insertSuccAbove
          (rightInsertedPosition t₂ b₂) t₁.rightPositions =
        Set.powersetCard.insertSuccAbove
          (rightInsertedPosition t₂ b₂) t₂.rightPositions :=
    Set.powersetCard.map_injective (n := q + 1) e.toEmbedding hMap
  have hRight : t₁.rightPositions = t₂.rightPositions :=
    Set.powersetCard.insertSuccAbove_injective
      (rightInsertedPosition t₂ b₂) hInsert
  have ht : t₁ = t₂ := (equivRightPositions (p := p) (q := q)).injective hRight
  subst t₂
  have hb : b₁ = b₂ := rightBoundaryIndex_injective t₁ hIndex
  subst b₂
  rfl

end AlgebraicTopology.EilenbergZilber.Shuffle
