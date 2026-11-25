/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Positions

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}
private theorem mem_leftPositions_iff_not_mem_rightPositions_right
    (s : Shuffle p q) (k : Fin (p + q)) :
    k ∈ s.leftPositions ↔ k ∉ s.rightPositions := by
  constructor
  · intro hkLeft hkRight
    exact (mem_rightPositions_iff_not_mem_leftPositions s k).mp hkRight hkLeft
  · intro hkNotRight
    by_contra hkNotLeft
    exact hkNotRight
      ((mem_rightPositions_iff_not_mem_leftPositions s k).mpr hkNotLeft)

private theorem right_succAbove_val_lt_succAbove_iff_of_val_eq {n m : ℕ}
    (r : Fin (n + 1)) (d : Fin (m + 1)) (hd : d.val = r.val)
    (x : Fin n) (k : Fin m) :
    (r.succAbove x).val < (d.succAbove k).val ↔ x.val < k.val := by
  by_cases hx : x.castSucc < r
  · rw [Fin.succAbove_of_castSucc_lt _ _ hx]
    change x.val < r.val at hx
    by_cases hk : k.castSucc < d
    · rw [Fin.succAbove_of_castSucc_lt _ _ hk]
      simp only [Fin.val_castSucc]
    · have hle := Fin.not_lt.mp hk
      change d.val ≤ k.val at hle
      rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hk)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  · have hrx := Fin.not_lt.mp hx
    change r.val ≤ x.val at hrx
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hx)]
    by_cases hk : k.castSucc < d
    · change k.val < d.val at hk
      rw [Fin.succAbove_of_castSucc_lt _ _ hk]
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hk)]
      simp only [Fin.val_succ]
      omega

private theorem right_val_lt_succAbove_iff_of_val_eq {n m : ℕ}
    (r : Fin n) (d : Fin (m + 1)) (hd : d.val = r.val) (k : Fin m) :
    r.val < (d.succAbove k).val ↔ r.val ≤ k.val := by
  by_cases hk : k.castSucc < d
  · change k.val < d.val at hk
    rw [Fin.succAbove_of_castSucc_lt _ _ hk]
    simp only [Fin.val_castSucc]
    omega
  · have hle := Fin.not_lt.mp hk
    change d.val ≤ k.val at hle
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp hk)]
    simp only [Fin.val_succ]
    omega

private theorem rightIndex_lt_rightHom_iff (t : Shuffle p q) (b : Fin q)
    (k : Fin (p + q + 1)) :
    b.val < (t.rightHom.toOrderHom k).val ↔
      (t.perm (Fin.natAdd p b)).val < k.val := by
  rw [rightHom_val_eq_card_filter_rightPositions]
  rw [rightPositions, Set.powersetCard.val_ofFinEmb]
  rw [Finset.filter_map, Finset.card_map]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro i j hji hi
  change (t.perm (Fin.natAdd p i)).val < k.val at hi
  change (t.perm (Fin.natAdd p j)).val < k.val
  have hle := Fin.le_iff_val_le_val.mp (t.isShuffle.2.monotone hji)
  omega

theorem leftPositions_rightBoundaryShuffle (t : Shuffle p q)
    (b : Fin (q + 2)) :
    (rightBoundaryShuffle t b).leftPositions.val =
      Finset.map (finCongr (by omega)).toEmbedding
        (Finset.map (rightInsertedPosition t b).succAboveEmb
          t.leftPositions.val) := by
  classical
  let e : Fin (p + q + 1) ≃ Fin (p + (q + 1)) := finCongr (by omega)
  ext x
  change (x ∈ (rightBoundaryShuffle t b).leftPositions) ↔ _
  rw [mem_leftPositions_iff_not_mem_rightPositions_right]
  rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
    mem_rightInsertedPositions_iff]
  change ¬(e (rightInsertedPosition t b) = x ∨
      ∃ k ∈ t.rightPositions,
        e ((rightInsertedPosition t b).succAbove k) = x) ↔ _
  simp only [Finset.mem_map]
  constructor
  · intro hx
    let x' : Fin (p + q + 1) := e.symm x
    have hxne : x' ≠ rightInsertedPosition t b := by
      intro h
      apply hx
      left
      rw [← h]
      exact e.apply_symm_apply x
    have hxrange : x' ∈ Set.range (rightInsertedPosition t b).succAbove := by
      rw [Fin.range_succAbove]
      simpa using hxne
    obtain ⟨y, hy⟩ := hxrange
    have hyNotRight : y ∉ t.rightPositions := by
      intro hyRight
      apply hx
      right
      refine ⟨y, hyRight, ?_⟩
      rw [hy]
      exact e.apply_symm_apply x
    have hyLeft : y ∈ t.leftPositions :=
      (mem_leftPositions_iff_not_mem_rightPositions_right t y).mpr hyNotRight
    refine ⟨(rightInsertedPosition t b).succAbove y, ?_, ?_⟩
    · exact ⟨y, hyLeft, rfl⟩
    · rw [hy]
      exact e.apply_symm_apply x
  · rintro ⟨z, ⟨y, hyLeft, rfl⟩, rfl⟩
    rintro (hInserted | ⟨k, hkRight, hk⟩)
    · exact (rightInsertedPosition t b).succAbove_ne y
        (e.injective hInserted).symm
    · have hsucc : (rightInsertedPosition t b).succAbove k =
          (rightInsertedPosition t b).succAbove y := e.injective hk
      have hky : k = y := Fin.succAbove_right_injective hsucc
      subst k
      exact (mem_leftPositions_iff_not_mem_rightPositions_right t y).mp
        hyLeft hkRight

theorem rightHom_rightBoundaryShuffle_succAbove
    (t : Shuffle p q) (b : Fin (q + 2)) (k : Fin (p + q + 1)) :
    (rightBoundaryShuffle t b).rightHom.toOrderHom
        ((rightBoundaryIndex t b).succAbove (Fin.cast (by omega) k)) =
      b.succAbove (t.rightHom.toOrderHom k) := by
  apply Fin.ext
  rw [rightHom_val_eq_card_filter_rightPositions]
  cases b using Fin.cases with
  | zero =>
      rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
        rightInsertedPositions, Set.powersetCard.val_map]
      unfold Set.powersetCard.insertSuccAbove
      rw [Set.powersetCard.val_ofCard]
      simp only [rightBoundaryIndex_zero, Fin.zero_succAbove, Fin.val_succ,
        Fin.val_cast, Order.lt_add_one_iff, rightInsertedPosition_zero,
        Finset.map_insert, Function.Embedding.coeFn_mk, finCongr_apply,
        Fin.cast_zero]
      rw [Finset.filter_insert]
      simp only [Fin.val_zero, Nat.zero_le, ite_true]
      rw [Finset.card_insert_of_notMem]
      · congr 1
        rw [rightHom_val_eq_card_filter_rightPositions]
        rw [Finset.filter_map, Finset.card_map]
        rw [Finset.filter_map, Finset.card_map]
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro x hx
        change (Fin.succAbove 0 x).val ≤ k.val ↔ x.val < k.val
        rw [Fin.succAbove_zero]
        simp only [Fin.val_succ]
        omega
      · simp
  | succ b' =>
      cases b' using Fin.lastCases with
      | last =>
          rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
            rightInsertedPositions, Set.powersetCard.val_map]
          unfold Set.powersetCard.insertSuccAbove
          rw [Set.powersetCard.val_ofCard]
          simp only [Fin.succ_last, Nat.succ_eq_add_one,
            rightBoundaryIndex_last, Fin.succAbove_last, Fin.val_castSucc,
            Fin.val_cast, rightInsertedPosition_last, Finset.map_insert,
            Function.Embedding.coeFn_mk, finCongr_apply]
          rw [Finset.filter_insert]
          split_ifs with hlast
          · have hk := k.isLt
            simp only [Fin.val_cast, Fin.val_last] at hlast
            omega
          · rw [Finset.filter_map, Finset.card_map]
            rw [Finset.filter_map, Finset.card_map]
            rw [rightHom_val_eq_card_filter_rightPositions]
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro x hx
            change (Fin.succAbove (Fin.last (p + q)) x).val < k.val ↔
              x.val < k.val
            rw [Fin.succAbove_last]
            simp only [Fin.val_castSucc]
      | cast b =>
          rw [rightBoundaryShuffle, rightPositions_ofRightPositions,
            rightInsertedPositions, Set.powersetCard.val_map]
          unfold Set.powersetCard.insertSuccAbove
          rw [Set.powersetCard.val_ofCard]
          simp only [rightBoundaryIndex_interior, Fin.castSucc_succ,
            Fin.cast_succ_eq, rightInsertedPosition_interior,
            Finset.map_insert, Function.Embedding.coeFn_mk, finCongr_apply]
          rw [Finset.filter_insert]
          split_ifs with hIns
          · rw [Finset.card_insert_of_notMem]
            · have hrle :=
                (right_val_lt_succAbove_iff_of_val_eq
                  (Fin.cast (by omega) (t.perm (Fin.natAdd p b)).succ :
                    Fin (p + (q + 1)))
                  ((Fin.cast (by omega)
                    (t.perm (Fin.natAdd p b)).castSucc).succ :
                      Fin (p + (q + 1) + 1))
                  (by rfl) (Fin.cast (by omega) k : Fin (p + (q + 1)))).mp hIns
              have hposlt : (t.perm (Fin.natAdd p b)).val < k.val := by
                simp only [Fin.val_cast, Fin.val_succ] at hrle
                omega
              have hbLt : b.val < (t.rightHom.toOrderHom k).val :=
                (rightIndex_lt_rightHom_iff t b k).mpr hposlt
              have hle : b.castSucc.succ ≤ (t.rightHom.toOrderHom k).castSucc := by
                apply Fin.le_iff_val_le_val.mpr
                simp only [Fin.val_succ, Fin.val_castSucc]
                omega
              rw [Fin.succAbove_of_le_castSucc _ _ hle]
              simp only [Fin.val_succ]
              congr 1
              rw [Finset.filter_map, Finset.card_map]
              rw [Finset.filter_map, Finset.card_map]
              rw [rightHom_val_eq_card_filter_rightPositions]
              apply congrArg Finset.card
              apply Finset.filter_congr
              intro x hx
              change
                ((t.perm (Fin.natAdd p b)).succ.succAbove x).val <
                    ((Fin.cast (by omega)
                      (t.perm (Fin.natAdd p b)).castSucc).succ.succAbove
                        (Fin.cast (by omega) k)).val ↔
                  x.val < k.val
              have hcomparison :=
                right_succAbove_val_lt_succAbove_iff_of_val_eq
                  (t.perm (Fin.natAdd p b)).succ
                  ((Fin.cast (by omega)
                    (t.perm (Fin.natAdd p b)).castSucc).succ :
                      Fin (p + (q + 1) + 1))
                  (by rfl) x (Fin.cast (by omega) k : Fin (p + (q + 1)))
              change
                ((t.perm (Fin.natAdd p b)).succ.succAbove x).val <
                    ((Fin.cast (by omega)
                      (t.perm (Fin.natAdd p b)).castSucc).succ.succAbove
                        (Fin.cast (by omega) k)).val ↔
                  x.val < k.val at hcomparison
              exact hcomparison
            · simp
          · have hself :=
              right_val_lt_succAbove_iff_of_val_eq
                (Fin.cast (by omega) (t.perm (Fin.natAdd p b)).succ :
                  Fin (p + (q + 1)))
                ((Fin.cast (by omega)
                  (t.perm (Fin.natAdd p b)).castSucc).succ :
                    Fin (p + (q + 1) + 1))
                (by rfl) (Fin.cast (by omega) k : Fin (p + (q + 1)))
            have hrnotle :
                ¬ (Fin.cast (by omega) (t.perm (Fin.natAdd p b)).succ :
                    Fin (p + (q + 1))).val ≤
                  (Fin.cast (by omega) k : Fin (p + (q + 1))).val := by
              intro hle
              exact hIns (hself.mpr hle)
            have hklt : k.val < (t.perm (Fin.natAdd p b)).succ.val := by
              simp only [Fin.val_cast] at hrnotle
              omega
            have hposNot : ¬ (t.perm (Fin.natAdd p b)).val < k.val := by
              simp only [Fin.val_succ] at hklt
              omega
            have hbNot :
                ¬ b.val < (t.rightHom.toOrderHom k).val := by
              intro hb
              exact hposNot ((rightIndex_lt_rightHom_iff t b k).mp hb)
            have hlt :
                (t.rightHom.toOrderHom k).castSucc < b.castSucc.succ := by
              change (t.rightHom.toOrderHom k).val < b.val + 1
              omega
            rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
            simp only [Fin.val_castSucc]
            rw [Finset.filter_map, Finset.card_map]
            rw [Finset.filter_map, Finset.card_map]
            rw [rightHom_val_eq_card_filter_rightPositions]
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro x hx
            change
              ((t.perm (Fin.natAdd p b)).succ.succAbove x).val <
                  ((Fin.cast (by omega)
                    (t.perm (Fin.natAdd p b)).castSucc).succ.succAbove
                      (Fin.cast (by omega) k)).val ↔
                x.val < k.val
            have hcomparison :=
              right_succAbove_val_lt_succAbove_iff_of_val_eq
                (t.perm (Fin.natAdd p b)).succ
                ((Fin.cast (by omega)
                  (t.perm (Fin.natAdd p b)).castSucc).succ :
                    Fin (p + (q + 1) + 1))
                (by rfl) x (Fin.cast (by omega) k : Fin (p + (q + 1)))
            change
              ((t.perm (Fin.natAdd p b)).succ.succAbove x).val <
                  ((Fin.cast (by omega)
                    (t.perm (Fin.natAdd p b)).castSucc).succ.succAbove
                      (Fin.cast (by omega) k)).val ↔
                x.val < k.val at hcomparison
            exact hcomparison

theorem leftHom_rightBoundaryShuffle_succAbove
    (t : Shuffle p q) (b : Fin (q + 2)) (k : Fin (p + q + 1)) :
    (rightBoundaryShuffle t b).leftHom.toOrderHom
        ((rightBoundaryIndex t b).succAbove (Fin.cast (by omega) k)) =
      t.leftHom.toOrderHom k := by
  apply Fin.ext
  rw [leftHom_val_eq_card_filter_leftPositions,
    leftHom_val_eq_card_filter_leftPositions,
    leftPositions_rightBoundaryShuffle]
  rw [Finset.filter_map, Finset.card_map]
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x hx
  cases b using Fin.cases with
  | zero =>
      change (Fin.succAbove 0 x).val <
          (Fin.succAbove 0 (Fin.cast (by omega) k)).val ↔ x.val < k.val
      rw [Fin.succAbove_zero, Fin.succAbove_zero]
      simp only [Fin.val_succ, Fin.val_cast]
      omega
  | succ b' =>
      cases b' using Fin.lastCases with
      | last =>
          simp only [Fin.succ_last, rightInsertedPosition_last,
            rightBoundaryIndex_last]
          change (Fin.succAbove (Fin.last (p + q)) x).val <
              (Fin.succAbove (Fin.last (p + (q + 1)))
                (Fin.cast (by omega) k)).val ↔ x.val < k.val
          rw [Fin.succAbove_last, Fin.succAbove_last]
          simp only [Fin.val_castSucc, Fin.val_cast]
      | cast b =>
          simp only [rightInsertedPosition_interior, rightBoundaryIndex_interior]
          change
            ((t.perm (Fin.natAdd p b)).succ.succAbove x).val <
                ((Fin.cast (by omega)
                  (t.perm (Fin.natAdd p b)).castSucc).succ.succAbove
                    (Fin.cast (by omega) k)).val ↔
              x.val < k.val
          have hcomparison :=
            right_succAbove_val_lt_succAbove_iff_of_val_eq
              (t.perm (Fin.natAdd p b)).succ
              ((Fin.cast (by omega)
                (t.perm (Fin.natAdd p b)).castSucc).succ :
                  Fin (p + (q + 1) + 1))
              (by rfl) x (Fin.cast (by omega) k : Fin (p + (q + 1)))
          change
            ((t.perm (Fin.natAdd p b)).succ.succAbove x).val <
                ((Fin.cast (by omega)
                  (t.perm (Fin.natAdd p b)).castSucc).succ.succAbove
                    (Fin.cast (by omega) k)).val ↔
              x.val < k.val at hcomparison
          exact hcomparison

end AlgebraicTopology.EilenbergZilber.Shuffle
