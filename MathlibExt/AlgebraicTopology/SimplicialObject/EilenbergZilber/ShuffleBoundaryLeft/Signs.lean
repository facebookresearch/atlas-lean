/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Maps

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}
private theorem card_crossings_map_succAbove {n : ℕ} (r : Fin (n + 1))
    (l rset : Finset (Fin n)) :
    (((Finset.map r.succAboveEmb l) ×ˢ
        (Finset.map r.succAboveEmb rset)).filter fun ij => ij.2 < ij.1).card =
      ((l ×ˢ rset).filter fun ij => ij.2 < ij.1).card := by
  have hprod :
      (Finset.map r.succAboveEmb l) ×ˢ (Finset.map r.succAboveEmb rset) =
        Finset.map (r.succAboveEmb.prodMap r.succAboveEmb) (l ×ˢ rset) := by
    exact (Finset.prodMap_map_product r.succAboveEmb r.succAboveEmb l rset).symm
  rw [hprod]
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ij hij
  change r.succAbove ij.2 < r.succAbove ij.1 ↔ ij.2 < ij.1
  exact r.succAboveOrderEmb.lt_iff_lt

private theorem card_crossings_map_finCongr {m n : ℕ} (h : m = n)
    (l rset : Finset (Fin m)) :
    (((Finset.map (finCongr h).toEmbedding l) ×ˢ
        (Finset.map (finCongr h).toEmbedding rset)).filter fun ij =>
          ij.2 < ij.1).card =
      ((l ×ˢ rset).filter fun ij => ij.2 < ij.1).card := by
  have hprod :
      (Finset.map (finCongr h).toEmbedding l) ×ˢ
          (Finset.map (finCongr h).toEmbedding rset) =
        Finset.map ((finCongr h).toEmbedding.prodMap
          (finCongr h).toEmbedding) (l ×ˢ rset) := by
    exact (Finset.prodMap_map_product _ _ _ _).symm
  rw [hprod, Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ij hij
  change (finCongr h ij.2).val < (finCongr h ij.1).val ↔ ij.2 < ij.1
  change ij.2.val < ij.1.val ↔ ij.2.val < ij.1.val
  rfl

private theorem card_inserted_crossings {n : ℕ} (r : Fin (n + 1))
    (s : Finset (Fin n)) :
    ((({r} : Finset (Fin (n + 1))) ×ˢ
        (Finset.map r.succAboveEmb s)).filter fun ij =>
        ij.2 < ij.1).card =
      (s.filter fun j => j.castSucc < r).card := by
  let e : Fin n ↪ Fin (n + 1) × Fin (n + 1) :=
    { toFun := fun j => (r, r.succAbove j)
      inj' := by
        intro x y h
        exact (Fin.succAbove_right_injective (p := r)) (congrArg Prod.snd h) }
  have hprod :
      ({r} : Finset (Fin (n + 1))) ×ˢ (Finset.map r.succAboveEmb s) =
        Finset.map e s := by
    ext ij
    rcases ij with ⟨i, j⟩
    rw [Finset.mem_product]
    simp only [Finset.mem_singleton, Finset.mem_map, e]
    constructor
    · rintro ⟨rfl, x, hx, hxj⟩
      exact ⟨x, hx, Prod.ext rfl hxj⟩
    · rintro ⟨x, hx, hpair⟩
      exact ⟨(congrArg Prod.fst hpair).symm,
        ⟨x, hx, congrArg Prod.snd hpair⟩⟩
  rw [hprod]
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  exact Fin.succAbove_lt_iff_castSucc_lt r j

private theorem card_crossings_insert_succAbove {n : ℕ} (r : Fin (n + 1))
    (l rset : Finset (Fin n)) :
    (((insert r (Finset.map r.succAboveEmb l)) ×ˢ
        (Finset.map r.succAboveEmb rset)).filter fun ij =>
        ij.2 < ij.1).card =
      ((l ×ˢ rset).filter fun ij => ij.2 < ij.1).card +
        (rset.filter fun j => j.castSucc < r).card := by
  have hins :
      insert r (Finset.map r.succAboveEmb l) =
        ({r} : Finset (Fin (n + 1))) ∪ Finset.map r.succAboveEmb l := by
    simp
  rw [hins, Finset.union_product, Finset.filter_union]
  have hdisj :
      Disjoint
        ((({r} : Finset (Fin (n + 1))) ×ˢ
          Finset.map r.succAboveEmb rset).filter fun ij => ij.2 < ij.1)
        (((Finset.map r.succAboveEmb l) ×ˢ
          Finset.map r.succAboveEmb rset).filter fun ij => ij.2 < ij.1) := by
    rw [Finset.disjoint_left]
    intro ij hijInserted hijShifted
    have hiInserted := (Finset.mem_product.mp (Finset.mem_filter.mp hijInserted).1).1
    have hiShifted := (Finset.mem_product.mp (Finset.mem_filter.mp hijShifted).1).1
    simp only [Finset.mem_singleton] at hiInserted
    rw [Finset.mem_map] at hiShifted
    obtain ⟨i, hi, hii⟩ := hiShifted
    exact r.succAbove_ne i (hii.trans hiInserted)
  rw [Finset.card_union_of_disjoint hdisj]
  rw [card_inserted_crossings, card_crossings_map_succAbove]
  omega

private theorem card_left_filter_add_card_right_filter (t : Shuffle p q)
    (k : Fin (p + q + 1)) :
    (t.leftPositions.val.filter fun i => i.val < k.val).card +
        (t.rightPositions.val.filter fun i => i.val < k.val).card = k.val := by
  have hdisj : Disjoint t.leftPositions.val t.rightPositions.val := by
    rw [Finset.disjoint_left]
    intro i hiLeft hiRight
    exact (mem_rightPositions_iff_not_mem_leftPositions t i).mp hiRight hiLeft
  have hunion : t.leftPositions.val ∪ t.rightPositions.val = Finset.univ := by
    ext i
    by_cases hi : i ∈ t.leftPositions
    · constructor
      · intro h
        exact Finset.mem_univ i
      · intro h
        exact Finset.mem_union.mpr (Or.inl hi)
    · have hiRight := (mem_rightPositions_iff_not_mem_leftPositions t i).mpr hi
      constructor
      · intro h
        exact Finset.mem_univ i
      · intro h
        exact Finset.mem_union.mpr (Or.inr hiRight)
  have hdisjFilter :
      Disjoint
        (t.leftPositions.val.filter fun i => i.val < k.val)
        (t.rightPositions.val.filter fun i => i.val < k.val) :=
    hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← Finset.card_union_of_disjoint hdisjFilter]
  rw [← Finset.filter_union, hunion]
  rw [Fin.card_filter_val_lt]
  omega

private theorem card_leftPositions_lt_leftPosition (t : Shuffle p q)
    (a : Fin p) :
    (t.leftPositions.val.filter fun i =>
      i.val < (t.perm (Fin.castAdd q a)).val).card = a.val := by
  rw [leftPositions, Set.powersetCard.val_ofFinEmb]
  rw [Finset.filter_map, Finset.card_map]
  change
    (Finset.univ.filter fun i : Fin p =>
      (t.perm (Fin.castAdd q i)).val <
        (t.perm (Fin.castAdd q a)).val).card = a.val
  have hfilter :
      (Finset.univ.filter fun i : Fin p =>
        (t.perm (Fin.castAdd q i)).val <
          (t.perm (Fin.castAdd q a)).val) =
        Finset.univ.filter fun i : Fin p => i.val < a.val := by
    apply Finset.filter_congr
    intro i hi
    change t.perm (Fin.castAdd q i) < t.perm (Fin.castAdd q a) ↔ i < a
    exact t.isShuffle.1.lt_iff_lt
  rw [hfilter, Fin.card_filter_val_lt]
  omega

private theorem card_right_filter_leftInsertedPosition_add_val
    (t : Shuffle p q) (a : Fin (p + 2)) :
    (t.rightPositions.val.filter fun j =>
        j.castSucc < leftInsertedPosition t a).card + a.val =
      (leftBoundaryIndex t a).val := by
  cases a using Fin.cases with
  | zero =>
      simp
  | succ a' =>
      cases a' using Fin.lastCases with
      | last =>
          simp [Set.powersetCard.card_eq]
          omega
      | cast k =>
          simp only [leftInsertedPosition_interior, leftBoundaryIndex_interior,
            Fin.val_succ, Fin.val_cast, Fin.val_castSucc]
          let r : Fin (p + q) := t.perm (Fin.castAdd q k)
          have hrLeft : r ∈ t.leftPositions := by
            rw [mem_leftPositions_iff]
            exact ⟨k, rfl⟩
          have hfilter :
              (t.rightPositions.val.filter fun j => j.castSucc < r.succ) =
                t.rightPositions.val.filter fun j => j.val < r.val := by
            apply Finset.filter_congr
            intro j hj
            have hjNotLeft :=
              (mem_rightPositions_iff_not_mem_leftPositions t j).mp hj
            have hjne : j.val ≠ r.val := by
              intro hval
              apply hjNotLeft
              have hjr : j = r := Fin.ext hval
              rwa [hjr]
            change j.val < r.val + 1 ↔ j.val < r.val
            omega
          rw [hfilter]
          have htotal := card_left_filter_add_card_right_filter t r.castSucc
          simp only [Fin.val_castSucc] at htotal
          rw [card_leftPositions_lt_leftPosition t k] at htotal
          change
            (t.rightPositions.val.filter fun j => j.val < r.val).card +
                (k.val + 1) = r.val + 1
          omega

theorem crossingNumber_leftBoundaryShuffle
    (t : Shuffle p q) (a : Fin (p + 2)) :
    (leftBoundaryShuffle t a).crossingNumber + a.val =
      t.crossingNumber + (leftBoundaryIndex t a).val := by
  classical
  rw [crossingNumber, crossingNumber, rightPositions_leftBoundaryShuffle]
  rw [leftBoundaryShuffle, leftPositions_ofLeftPositions]
  simp only [leftInsertedPositions, Set.powersetCard.val_map]
  change
    (((Finset.map (finCongr (by omega)).toEmbedding
        (Set.powersetCard.insertSuccAbove
          (leftInsertedPosition t a) t.leftPositions).val) ×ˢ
      (Finset.map (finCongr (by omega)).toEmbedding
        (Finset.map (leftInsertedPosition t a).succAboveEmb
          t.rightPositions.val))).filter fun ij => ij.2 < ij.1).card + a.val =
      ((t.leftPositions.val ×ˢ t.rightPositions.val).filter fun ij =>
        ij.2 < ij.1).card + (leftBoundaryIndex t a).val
  have hcast := card_crossings_map_finCongr
    (m := p + q + 1) (n := (p + 1) + q) (by omega)
    (Set.powersetCard.insertSuccAbove (leftInsertedPosition t a) t.leftPositions).val
    (Finset.map (leftInsertedPosition t a).succAboveEmb t.rightPositions.val)
  rw [hcast]
  unfold Set.powersetCard.insertSuccAbove
  rw [Set.powersetCard.val_ofCard]
  rw [card_crossings_insert_succAbove]
  have hright := card_right_filter_leftInsertedPosition_add_val t a
  omega

theorem shuffleSignZ_leftBoundaryShuffle (t : Shuffle p q)
    (a : Fin (p + 2)) :
    (-1 : ℤ) ^ (leftBoundaryIndex t a).val *
        shuffleSignZ (leftBoundaryShuffle t a) =
      (-1 : ℤ) ^ a.val * shuffleSignZ t := by
  rw [shuffleSignZ_eq_neg_one_pow_crossingNumber,
    shuffleSignZ_eq_neg_one_pow_crossingNumber]
  have hcross := crossingNumber_leftBoundaryShuffle t a
  have hsign :
      (-1 : ℤ) ^ (leftBoundaryShuffle t a).crossingNumber *
          (-1 : ℤ) ^ a.val =
        (-1 : ℤ) ^ t.crossingNumber *
          (-1 : ℤ) ^ (leftBoundaryIndex t a).val := by
    rw [← pow_add, ← pow_add, hcross]
  have hsquare (n : ℕ) :
      (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
    rw [← pow_add]
    have hdouble : n + n = 2 * n := by omega
    rw [hdouble, pow_mul]
    norm_num
  calc
    (-1 : ℤ) ^ (leftBoundaryIndex t a).val *
          (-1 : ℤ) ^ (leftBoundaryShuffle t a).crossingNumber =
        ((-1 : ℤ) ^ (leftBoundaryIndex t a).val *
          (-1 : ℤ) ^ (leftBoundaryShuffle t a).crossingNumber) *
            ((-1 : ℤ) ^ a.val * (-1 : ℤ) ^ a.val) := by
              rw [hsquare, mul_one]
    _ = ((-1 : ℤ) ^ (leftBoundaryShuffle t a).crossingNumber *
          (-1 : ℤ) ^ a.val) *
            ((-1 : ℤ) ^ (leftBoundaryIndex t a).val *
              (-1 : ℤ) ^ a.val) := by ring
    _ = ((-1 : ℤ) ^ t.crossingNumber *
          (-1 : ℤ) ^ (leftBoundaryIndex t a).val) *
            ((-1 : ℤ) ^ (leftBoundaryIndex t a).val *
              (-1 : ℤ) ^ a.val) := by rw [hsign]
    _ = (-1 : ℤ) ^ t.crossingNumber *
          ((-1 : ℤ) ^ (leftBoundaryIndex t a).val *
            (-1 : ℤ) ^ (leftBoundaryIndex t a).val) *
          (-1 : ℤ) ^ a.val := by ring
    _ = (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ t.crossingNumber := by
      rw [hsquare]
      ring

end AlgebraicTopology.EilenbergZilber.Shuffle
