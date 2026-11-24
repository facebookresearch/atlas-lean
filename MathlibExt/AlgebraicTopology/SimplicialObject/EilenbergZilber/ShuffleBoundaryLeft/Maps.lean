/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Positions

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}
private theorem succAbove_val_lt_succAbove_iff_of_val_eq {n m : ℕ}
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

private theorem val_lt_succAbove_iff_of_val_eq {n m : ℕ}
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

private theorem leftIndex_lt_leftHom_iff (t : Shuffle p q) (a : Fin p)
    (k : Fin (p + q + 1)) :
    a.val < (t.leftHom.toOrderHom k).val ↔
      (t.perm (Fin.castAdd q a)).val < k.val := by
  rw [leftHom_val_eq_card_filter_leftPositions]
  rw [leftPositions, Set.powersetCard.val_ofFinEmb]
  rw [Finset.filter_map, Finset.card_map]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro i j hji hi
  change (t.perm (Fin.castAdd q i)).val < k.val at hi
  change (t.perm (Fin.castAdd q j)).val < k.val
  have hle := Fin.le_iff_val_le_val.mp (t.isShuffle.1.monotone hji)
  omega

theorem rightPositions_leftBoundaryShuffle (t : Shuffle p q)
    (a : Fin (p + 2)) :
    (leftBoundaryShuffle t a).rightPositions.val =
      Finset.map (finCongr (by omega)).toEmbedding
        (Finset.map (leftInsertedPosition t a).succAboveEmb
          t.rightPositions.val) := by
  classical
  let e : Fin (p + q + 1) ≃ Fin ((p + 1) + q) := finCongr (by omega)
  ext x
  change (x ∈ (leftBoundaryShuffle t a).rightPositions) ↔ _
  rw [mem_rightPositions_iff_not_mem_leftPositions]
  rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
    mem_leftInsertedPositions_iff]
  change ¬(e (leftInsertedPosition t a) = x ∨
      ∃ k ∈ t.leftPositions,
        e ((leftInsertedPosition t a).succAbove k) = x) ↔ _
  simp only [Finset.mem_map]
  constructor
  · intro hx
    let x' : Fin (p + q + 1) := e.symm x
    have hxne : x' ≠ leftInsertedPosition t a := by
      intro h
      apply hx
      left
      rw [← h]
      exact e.apply_symm_apply x
    have hxrange : x' ∈ Set.range (leftInsertedPosition t a).succAbove := by
      rw [Fin.range_succAbove]
      simpa using hxne
    obtain ⟨y, hy⟩ := hxrange
    have hyNotLeft : y ∉ t.leftPositions := by
      intro hyLeft
      apply hx
      right
      refine ⟨y, hyLeft, ?_⟩
      rw [hy]
      exact e.apply_symm_apply x
    have hyRight : y ∈ t.rightPositions :=
      (mem_rightPositions_iff_not_mem_leftPositions t y).mpr hyNotLeft
    refine ⟨(leftInsertedPosition t a).succAbove y, ?_, ?_⟩
    · exact ⟨y, hyRight, rfl⟩
    · rw [hy]
      exact e.apply_symm_apply x
  · rintro ⟨z, ⟨y, hyRight, rfl⟩, rfl⟩
    rintro (hInserted | ⟨k, hkLeft, hk⟩)
    · exact (leftInsertedPosition t a).succAbove_ne y
        (e.injective hInserted).symm
    · have hsucc : (leftInsertedPosition t a).succAbove k =
          (leftInsertedPosition t a).succAbove y := e.injective hk
      have hky : k = y := Fin.succAbove_right_injective hsucc
      subst k
      exact (mem_rightPositions_iff_not_mem_leftPositions t y).mp hyRight hkLeft

theorem leftHom_leftBoundaryShuffle_succAbove
    (t : Shuffle p q) (a : Fin (p + 2)) (k : Fin (p + q + 1)) :
    (leftBoundaryShuffle t a).leftHom.toOrderHom
        ((leftBoundaryIndex t a).succAbove (Fin.cast (by omega) k)) =
      a.succAbove (t.leftHom.toOrderHom k) := by
  apply Fin.ext
  rw [leftHom_val_eq_card_filter_leftPositions]
  cases a using Fin.cases with
  | zero =>
      rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
        leftInsertedPositions, Set.powersetCard.val_map]
      unfold Set.powersetCard.insertSuccAbove
      rw [Set.powersetCard.val_ofCard]
      simp only [leftBoundaryIndex_zero, Fin.zero_succAbove, Fin.val_succ,
        Fin.val_cast, Order.lt_add_one_iff, leftInsertedPosition_zero,
        Finset.map_insert, Function.Embedding.coeFn_mk, finCongr_apply,
        Fin.cast_zero]
      rw [Finset.filter_insert]
      simp only [Fin.val_zero, Nat.zero_le, ite_true]
      rw [Finset.card_insert_of_notMem]
      · congr 1
        rw [leftHom_val_eq_card_filter_leftPositions]
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
  | succ a' =>
      cases a' using Fin.lastCases with
      | last =>
          rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
            leftInsertedPositions, Set.powersetCard.val_map]
          unfold Set.powersetCard.insertSuccAbove
          rw [Set.powersetCard.val_ofCard]
          simp only [Fin.succ_last, Nat.succ_eq_add_one,
            leftBoundaryIndex_last, Fin.succAbove_last, Fin.val_castSucc,
            Fin.val_cast, leftInsertedPosition_last, Finset.map_insert,
            Function.Embedding.coeFn_mk, finCongr_apply]
          rw [Finset.filter_insert]
          split_ifs with hlast
          · have hk := k.isLt
            simp only [Fin.val_cast, Fin.val_last] at hlast
            omega
          · rw [Finset.filter_map, Finset.card_map]
            rw [Finset.filter_map, Finset.card_map]
            rw [leftHom_val_eq_card_filter_leftPositions]
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro x hx
            change (Fin.succAbove (Fin.last (p + q)) x).val < k.val ↔
              x.val < k.val
            rw [Fin.succAbove_last]
            simp only [Fin.val_castSucc]
      | cast a =>
          rw [leftBoundaryShuffle, leftPositions_ofLeftPositions,
            leftInsertedPositions, Set.powersetCard.val_map]
          unfold Set.powersetCard.insertSuccAbove
          rw [Set.powersetCard.val_ofCard]
          simp only [leftBoundaryIndex_interior, Fin.castSucc_succ,
            Fin.cast_succ_eq, leftInsertedPosition_interior,
            Finset.map_insert, Function.Embedding.coeFn_mk, finCongr_apply]
          rw [Finset.filter_insert]
          split_ifs with hIns
          · rw [Finset.card_insert_of_notMem]
            · have hrle :=
                (val_lt_succAbove_iff_of_val_eq
                  (Fin.cast (by omega) (t.perm (Fin.castAdd q a)).succ :
                    Fin ((p + 1) + q))
                  ((Fin.cast (by omega)
                    (t.perm (Fin.castAdd q a)).castSucc).succ :
                      Fin ((p + 1) + q + 1))
                  (by rfl) (Fin.cast (by omega) k : Fin ((p + 1) + q))).mp hIns
              have hposlt : (t.perm (Fin.castAdd q a)).val < k.val := by
                simp only [Fin.val_cast, Fin.val_succ] at hrle
                omega
              have haLt : a.val < (t.leftHom.toOrderHom k).val :=
                (leftIndex_lt_leftHom_iff t a k).mpr hposlt
              have hle : a.castSucc.succ ≤ (t.leftHom.toOrderHom k).castSucc := by
                apply Fin.le_iff_val_le_val.mpr
                simp only [Fin.val_succ, Fin.val_castSucc]
                omega
              rw [Fin.succAbove_of_le_castSucc _ _ hle]
              simp only [Fin.val_succ]
              congr 1
              rw [Finset.filter_map, Finset.card_map]
              rw [Finset.filter_map, Finset.card_map]
              rw [leftHom_val_eq_card_filter_leftPositions]
              apply congrArg Finset.card
              apply Finset.filter_congr
              intro x hx
              change
                ((t.perm (Fin.castAdd q a)).succ.succAbove x).val <
                    ((Fin.cast (by omega)
                      (t.perm (Fin.castAdd q a)).succ.castSucc).succAbove
                        (Fin.cast (by omega) k)).val ↔
                  x.val < k.val
              have hcomparison :=
                succAbove_val_lt_succAbove_iff_of_val_eq
                  (t.perm (Fin.castAdd q a)).succ
                  ((Fin.cast (by omega)
                    (t.perm (Fin.castAdd q a)).castSucc).succ :
                      Fin ((p + 1) + q + 1))
                  (by rfl) x (Fin.cast (by omega) k : Fin ((p + 1) + q))
              change
                ((t.perm (Fin.castAdd q a)).succ.succAbove x).val <
                    ((Fin.cast (by omega)
                      (t.perm (Fin.castAdd q a)).castSucc).succ.succAbove
                        (Fin.cast (by omega) k)).val ↔
                  x.val < k.val at hcomparison
              exact hcomparison
            · simp
          · have hself :=
              val_lt_succAbove_iff_of_val_eq
                (Fin.cast (by omega) (t.perm (Fin.castAdd q a)).succ :
                  Fin ((p + 1) + q))
                ((Fin.cast (by omega)
                  (t.perm (Fin.castAdd q a)).castSucc).succ :
                    Fin ((p + 1) + q + 1))
                (by rfl) (Fin.cast (by omega) k : Fin ((p + 1) + q))
            have hrnotle :
                ¬ (Fin.cast (by omega) (t.perm (Fin.castAdd q a)).succ :
                    Fin ((p + 1) + q)).val ≤
                  (Fin.cast (by omega) k : Fin ((p + 1) + q)).val := by
              intro hle
              exact hIns (hself.mpr hle)
            have hklt : k.val < (t.perm (Fin.castAdd q a)).succ.val := by
              simp only [Fin.val_cast] at hrnotle
              omega
            have hposNot : ¬ (t.perm (Fin.castAdd q a)).val < k.val := by
              simp only [Fin.val_succ] at hklt
              omega
            have haNot :
                ¬ a.val < (t.leftHom.toOrderHom k).val := by
              intro ha
              exact hposNot ((leftIndex_lt_leftHom_iff t a k).mp ha)
            have hlt :
                (t.leftHom.toOrderHom k).castSucc < a.castSucc.succ := by
              change (t.leftHom.toOrderHom k).val < a.val + 1
              omega
            rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
            simp only [Fin.val_castSucc]
            rw [Finset.filter_map, Finset.card_map]
            rw [Finset.filter_map, Finset.card_map]
            rw [leftHom_val_eq_card_filter_leftPositions]
            apply congrArg Finset.card
            apply Finset.filter_congr
            intro x hx
            change
              ((t.perm (Fin.castAdd q a)).succ.succAbove x).val <
                  ((Fin.cast (by omega)
                    (t.perm (Fin.castAdd q a)).castSucc).succ.succAbove
                      (Fin.cast (by omega) k)).val ↔
                x.val < k.val
            have hcomparison :=
              succAbove_val_lt_succAbove_iff_of_val_eq
                (t.perm (Fin.castAdd q a)).succ
                ((Fin.cast (by omega)
                  (t.perm (Fin.castAdd q a)).castSucc).succ :
                    Fin ((p + 1) + q + 1))
                (by rfl) x (Fin.cast (by omega) k : Fin ((p + 1) + q))
            change
              ((t.perm (Fin.castAdd q a)).succ.succAbove x).val <
                  ((Fin.cast (by omega)
                    (t.perm (Fin.castAdd q a)).castSucc).succ.succAbove
                      (Fin.cast (by omega) k)).val ↔
                x.val < k.val at hcomparison
            exact hcomparison

theorem rightHom_leftBoundaryShuffle_succAbove
    (t : Shuffle p q) (a : Fin (p + 2)) (k : Fin (p + q + 1)) :
    (leftBoundaryShuffle t a).rightHom.toOrderHom
        ((leftBoundaryIndex t a).succAbove (Fin.cast (by omega) k)) =
      t.rightHom.toOrderHom k := by
  apply Fin.ext
  rw [rightHom_val_eq_card_filter_rightPositions,
    rightHom_val_eq_card_filter_rightPositions,
    rightPositions_leftBoundaryShuffle]
  rw [Finset.filter_map, Finset.card_map]
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x hx
  cases a using Fin.cases with
  | zero =>
      change (Fin.succAbove 0 x).val <
          (Fin.succAbove 0 (Fin.cast (by omega) k)).val ↔ x.val < k.val
      rw [Fin.succAbove_zero, Fin.succAbove_zero]
      simp only [Fin.val_succ, Fin.val_cast]
      omega
  | succ a' =>
      cases a' using Fin.lastCases with
      | last =>
          simp only [Fin.succ_last, leftInsertedPosition_last,
            leftBoundaryIndex_last]
          change (Fin.succAbove (Fin.last (p + q)) x).val <
              (Fin.succAbove (Fin.last ((p + 1) + q))
                (Fin.cast (by omega) k)).val ↔ x.val < k.val
          rw [Fin.succAbove_last, Fin.succAbove_last]
          simp only [Fin.val_castSucc, Fin.val_cast]
      | cast a =>
          simp only [leftInsertedPosition_interior, leftBoundaryIndex_interior]
          change
            ((t.perm (Fin.castAdd q a)).succ.succAbove x).val <
                ((Fin.cast (by omega)
                  (t.perm (Fin.castAdd q a)).castSucc).succ.succAbove
                    (Fin.cast (by omega) k)).val ↔
              x.val < k.val
          have hcomparison :=
            succAbove_val_lt_succAbove_iff_of_val_eq
              (t.perm (Fin.castAdd q a)).succ
              ((Fin.cast (by omega)
                (t.perm (Fin.castAdd q a)).castSucc).succ :
                  Fin ((p + 1) + q + 1))
              (by rfl) x (Fin.cast (by omega) k : Fin ((p + 1) + q))
          change
            ((t.perm (Fin.castAdd q a)).succ.succAbove x).val <
                ((Fin.cast (by omega)
                  (t.perm (Fin.castAdd q a)).castSucc).succ.succAbove
                    (Fin.cast (by omega) k)).val ↔
              x.val < k.val at hcomparison
          exact hcomparison

end AlgebraicTopology.EilenbergZilber.Shuffle
