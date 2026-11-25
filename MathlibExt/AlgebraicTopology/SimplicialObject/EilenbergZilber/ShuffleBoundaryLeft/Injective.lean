/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Basic

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}

theorem leftBoundaryIndex_injective (t : Shuffle p q) :
    Function.Injective (leftBoundaryIndex t) := by
  intro a₁ a₂ h
  cases a₁ using Fin.cases with
  | zero =>
      cases a₂ using Fin.cases with
      | zero => rfl
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
              | last => rfl
              | cast k₂ =>
                  exfalso
                  have hval := congrArg Fin.val h
                  have hlt := (t.perm (Fin.castAdd q k₂)).isLt
                  simp only [Fin.succ_last, leftBoundaryIndex_last,
                    leftBoundaryIndex_interior, Fin.val_last, Fin.val_cast,
                    Fin.val_castSucc, Fin.val_succ] at hval
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
                  have hlt := (t.perm (Fin.castAdd q k₁)).isLt
                  simp only [Fin.succ_last, leftBoundaryIndex_interior,
                    leftBoundaryIndex_last, Fin.val_cast, Fin.val_castSucc,
                    Fin.val_succ, Fin.val_last] at hval
                  omega
              | cast k₂ =>
                  have hperm :
                      t.perm (Fin.castAdd q k₁) = t.perm (Fin.castAdd q k₂) := by
                    apply Fin.ext
                    have hval := congrArg Fin.val h
                    simp only [leftBoundaryIndex_interior, Fin.val_cast,
                      Fin.val_castSucc, Fin.val_succ] at hval
                    omega
                  have hkcast : Fin.castAdd q k₁ = Fin.castAdd q k₂ :=
                    t.perm.injective hperm
                  have hk : k₁ = k₂ := Fin.castAdd_injective p q hkcast
                  subst k₂
                  rfl

theorem leftBoundaryPair_injective :
    Function.Injective (leftBoundaryPair (p := p) (q := q)) := by
  rintro ⟨a₁, t₁⟩ ⟨a₂, t₂⟩ h
  have hShuffle : leftBoundaryShuffle t₁ a₁ = leftBoundaryShuffle t₂ a₂ :=
    congrArg Prod.fst h
  have hIndex : leftBoundaryIndex t₁ a₁ = leftBoundaryIndex t₂ a₂ :=
    congrArg Prod.snd h
  have hPositions : leftInsertedPositions t₁ a₁ = leftInsertedPositions t₂ a₂ := by
    simpa only [leftBoundaryShuffle, leftPositions_ofLeftPositions] using
      congrArg leftPositions hShuffle
  have hInserted : leftInsertedPosition t₁ a₁ = leftInsertedPosition t₂ a₂ :=
    leftInsertedPosition_eq_of_leftBoundaryIndex_eq t₁ t₂ a₁ a₂ hIndex
  let e : Fin (p + q + 1) ≃ Fin ((p + 1) + q) := finCongr (by omega)
  have hMap :
      Set.powersetCard.map (p + 1) e.toEmbedding
          (Set.powersetCard.insertSuccAbove (leftInsertedPosition t₂ a₂) t₁.leftPositions) =
        Set.powersetCard.map (p + 1) e.toEmbedding
          (Set.powersetCard.insertSuccAbove (leftInsertedPosition t₂ a₂) t₂.leftPositions) := by
    simpa only [leftInsertedPositions, hInserted, e] using hPositions
  have hInsert :
      Set.powersetCard.insertSuccAbove (leftInsertedPosition t₂ a₂) t₁.leftPositions =
        Set.powersetCard.insertSuccAbove (leftInsertedPosition t₂ a₂) t₂.leftPositions :=
    Set.powersetCard.map_injective (n := p + 1) e.toEmbedding hMap
  have hLeft : t₁.leftPositions = t₂.leftPositions :=
    Set.powersetCard.insertSuccAbove_injective (leftInsertedPosition t₂ a₂) hInsert
  have ht : t₁ = t₂ := (equivLeftPositions (p := p) (q := q)).injective hLeft
  subst t₂
  have ha : a₁ = a₂ := leftBoundaryIndex_injective t₁ hIndex
  subst a₂
  rfl

end AlgebraicTopology.EilenbergZilber.Shuffle
