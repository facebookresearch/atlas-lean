/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Maps

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber.Shuffle

variable {p q : ℕ}
private theorem right_card_crossings_map_succAbove {n : ℕ}
    (r : Fin (n + 1)) (l rset : Finset (Fin n)) :
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

private theorem right_card_crossings_map_finCongr {m n : ℕ} (h : m = n)
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

private theorem card_inserted_right_crossings {n : ℕ} (r : Fin (n + 1))
    (s : Finset (Fin n)) :
    (((Finset.map r.succAboveEmb s) ×ˢ
        ({r} : Finset (Fin (n + 1)))).filter fun ij =>
        ij.2 < ij.1).card =
      (s.filter fun i => r ≤ i.castSucc).card := by
  let e : Fin n ↪ Fin (n + 1) × Fin (n + 1) :=
    { toFun := fun i => (r.succAbove i, r)
      inj' := by
        intro x y h
        exact (Fin.succAbove_right_injective (p := r)) (congrArg Prod.fst h) }
  have hprod :
      (Finset.map r.succAboveEmb s) ×ˢ ({r} : Finset (Fin (n + 1))) =
        Finset.map e s := by
    ext ij
    rcases ij with ⟨i, j⟩
    rw [Finset.mem_product]
    simp only [Finset.mem_singleton, Finset.mem_map, e]
    constructor
    · rintro ⟨⟨x, hx, hxi⟩, rfl⟩
      exact ⟨x, hx, Prod.ext hxi rfl⟩
    · rintro ⟨x, hx, hpair⟩
      exact ⟨⟨x, hx, congrArg Prod.fst hpair⟩,
        (congrArg Prod.snd hpair).symm⟩
  rw [hprod]
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  exact Fin.lt_succAbove_iff_le_castSucc r i

private theorem card_crossings_succAbove_insert {n : ℕ} (r : Fin (n + 1))
    (l rset : Finset (Fin n)) :
    (((Finset.map r.succAboveEmb l) ×ˢ
        (insert r (Finset.map r.succAboveEmb rset))).filter fun ij =>
        ij.2 < ij.1).card =
      ((l ×ˢ rset).filter fun ij => ij.2 < ij.1).card +
        (l.filter fun i => r ≤ i.castSucc).card := by
  have hins :
      insert r (Finset.map r.succAboveEmb rset) =
        ({r} : Finset (Fin (n + 1))) ∪ Finset.map r.succAboveEmb rset := by
    simp
  rw [hins, Finset.product_union, Finset.filter_union]
  have hdisj :
      Disjoint
        (((Finset.map r.succAboveEmb l) ×ˢ
          ({r} : Finset (Fin (n + 1)))).filter fun ij => ij.2 < ij.1)
        (((Finset.map r.succAboveEmb l) ×ˢ
          Finset.map r.succAboveEmb rset).filter fun ij => ij.2 < ij.1) := by
    rw [Finset.disjoint_left]
    intro ij hijInserted hijShifted
    have hjInserted := (Finset.mem_product.mp (Finset.mem_filter.mp hijInserted).1).2
    have hjShifted := (Finset.mem_product.mp (Finset.mem_filter.mp hijShifted).1).2
    simp only [Finset.mem_singleton] at hjInserted
    rw [Finset.mem_map] at hjShifted
    obtain ⟨j, hj, hjj⟩ := hjShifted
    exact r.succAbove_ne j (hjj.trans hjInserted)
  rw [Finset.card_union_of_disjoint hdisj]
  rw [card_inserted_right_crossings, right_card_crossings_map_succAbove]
  omega

private theorem card_left_filter_add_card_right_filter_right
    (t : Shuffle p q) (k : Fin (p + q + 1)) :
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
    · have hiRight :=
        (mem_rightPositions_iff_not_mem_leftPositions t i).mpr hi
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

private theorem card_rightPositions_lt_rightPosition (t : Shuffle p q)
    (b : Fin q) :
    (t.rightPositions.val.filter fun j =>
      j.val < (t.perm (Fin.natAdd p b)).val).card = b.val := by
  rw [rightPositions, Set.powersetCard.val_ofFinEmb]
  rw [Finset.filter_map, Finset.card_map]
  change
    (Finset.univ.filter fun j : Fin q =>
      (t.perm (Fin.natAdd p j)).val <
        (t.perm (Fin.natAdd p b)).val).card = b.val
  have hfilter :
      (Finset.univ.filter fun j : Fin q =>
        (t.perm (Fin.natAdd p j)).val <
          (t.perm (Fin.natAdd p b)).val) =
        Finset.univ.filter fun j : Fin q => j.val < b.val := by
    apply Finset.filter_congr
    intro j hj
    change t.perm (Fin.natAdd p j) < t.perm (Fin.natAdd p b) ↔ j < b
    exact t.isShuffle.2.lt_iff_lt
  rw [hfilter, Fin.card_filter_val_lt]
  omega

private theorem card_left_filter_rightInsertedPosition_add_index
    (t : Shuffle p q) (b : Fin (q + 2)) :
    (t.leftPositions.val.filter fun i =>
        rightInsertedPosition t b ≤ i.castSucc).card +
        (rightBoundaryIndex t b).val = p + b.val := by
  cases b using Fin.cases with
  | zero =>
      simp [Set.powersetCard.card_eq]
  | succ b' =>
      cases b' using Fin.lastCases with
      | last =>
          simp
      | cast k =>
          simp only [rightInsertedPosition_interior, rightBoundaryIndex_interior,
            Fin.val_succ, Fin.val_cast, Fin.val_castSucc]
          let r : Fin (p + q) := t.perm (Fin.natAdd p k)
          have hrRight : r ∈ t.rightPositions := by
            rw [mem_rightPositions_iff]
            exact ⟨k, rfl⟩
          have hrNotLeft : r ∉ t.leftPositions :=
            (mem_rightPositions_iff_not_mem_leftPositions t r).mp hrRight
          have hfilter :
              (t.leftPositions.val.filter fun i => r.succ ≤ i.castSucc) =
                t.leftPositions.val.filter fun i => r.val < i.val := by
            apply Finset.filter_congr
            intro i hi
            change r.val + 1 ≤ i.val ↔ r.val < i.val
            omega
          rw [hfilter]
          have hnotFilter :
              (t.leftPositions.val.filter fun i => ¬ i.val < r.val) =
                t.leftPositions.val.filter fun i => r.val < i.val := by
            apply Finset.filter_congr
            intro i hi
            have hir : i ≠ r := by
              intro hir
              subst i
              exact hrNotLeft hi
            have hval : i.val ≠ r.val := by
              intro hval
              exact hir (Fin.ext hval)
            omega
          have hsplit := Finset.card_filter_add_card_filter_not
            (s := t.leftPositions.val) (fun i => i.val < r.val)
          rw [hnotFilter, Set.powersetCard.card_eq] at hsplit
          have htotal :=
            card_left_filter_add_card_right_filter_right t r.castSucc
          simp only [Fin.val_castSucc] at htotal
          rw [card_rightPositions_lt_rightPosition t k] at htotal
          change
            (t.leftPositions.val.filter fun i => r.val < i.val).card +
                (r.val + 1) = p + (k.val + 1)
          omega

theorem crossingNumber_rightBoundaryShuffle
    (t : Shuffle p q) (b : Fin (q + 2)) :
    (rightBoundaryShuffle t b).crossingNumber +
        (rightBoundaryIndex t b).val =
      t.crossingNumber + p + b.val := by
  classical
  rw [crossingNumber, crossingNumber, leftPositions_rightBoundaryShuffle]
  rw [rightBoundaryShuffle, rightPositions_ofRightPositions]
  simp only [rightInsertedPositions, Set.powersetCard.val_map]
  change
    (((Finset.map (finCongr (by omega)).toEmbedding
        (Finset.map (rightInsertedPosition t b).succAboveEmb
          t.leftPositions.val)) ×ˢ
      (Finset.map (finCongr (by omega)).toEmbedding
        (Set.powersetCard.insertSuccAbove
          (rightInsertedPosition t b) t.rightPositions).val)).filter fun ij =>
            ij.2 < ij.1).card + (rightBoundaryIndex t b).val =
      ((t.leftPositions.val ×ˢ t.rightPositions.val).filter fun ij =>
        ij.2 < ij.1).card + p + b.val
  have hcast := right_card_crossings_map_finCongr
    (m := p + q + 1) (n := p + (q + 1)) (by omega)
    (Finset.map (rightInsertedPosition t b).succAboveEmb t.leftPositions.val)
    (Set.powersetCard.insertSuccAbove
      (rightInsertedPosition t b) t.rightPositions).val
  rw [hcast]
  unfold Set.powersetCard.insertSuccAbove
  rw [Set.powersetCard.val_ofCard]
  rw [card_crossings_succAbove_insert]
  have hleft := card_left_filter_rightInsertedPosition_add_index t b
  omega

theorem shuffleSignZ_rightBoundaryShuffle (t : Shuffle p q)
    (b : Fin (q + 2)) :
    (-1 : ℤ) ^ (rightBoundaryIndex t b).val *
        shuffleSignZ (rightBoundaryShuffle t b) =
      (-1 : ℤ) ^ (p + b.val) * shuffleSignZ t := by
  rw [shuffleSignZ_eq_neg_one_pow_crossingNumber,
    shuffleSignZ_eq_neg_one_pow_crossingNumber]
  have hcross := crossingNumber_rightBoundaryShuffle t b
  calc
    (-1 : ℤ) ^ (rightBoundaryIndex t b).val *
          (-1 : ℤ) ^ (rightBoundaryShuffle t b).crossingNumber =
        (-1 : ℤ) ^ ((rightBoundaryIndex t b).val +
          (rightBoundaryShuffle t b).crossingNumber) := by rw [pow_add]
    _ = (-1 : ℤ) ^ (t.crossingNumber + (p + b.val)) := by
      congr 1
      omega
    _ = (-1 : ℤ) ^ t.crossingNumber * (-1 : ℤ) ^ (p + b.val) := by
      rw [pow_add]
    _ = (-1 : ℤ) ^ (p + b.val) * (-1 : ℤ) ^ t.crossingNumber := by ring

end AlgebraicTopology.EilenbergZilber.Shuffle
