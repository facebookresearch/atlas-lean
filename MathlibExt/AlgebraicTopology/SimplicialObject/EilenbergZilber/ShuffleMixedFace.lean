/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCrossing

@[expose] public section

namespace AlgebraicTopology.EilenbergZilber

namespace Shuffle

@[ext]
structure MixedFace (p q : ℕ) where
  shuffle : Shuffle p q
  lowerPosition : Fin (p + q)
  upperPosition : Fin (p + q)
  adjacent : lowerPosition.val + 1 = upperPosition.val
  mixed : Xor
    (lowerPosition ∈ shuffle.leftPositions)
    (upperPosition ∈ shuffle.leftPositions)

namespace MixedFace

variable {p q : ℕ}

noncomputable instance : DecidableEq (MixedFace p q) := Classical.decEq _

noncomputable instance : Fintype (MixedFace p q) :=
  Fintype.ofInjective
    (fun x => (x.shuffle, x.lowerPosition, x.upperPosition)) (by
      intro x y h
      apply MixedFace.ext
      · exact congrArg Prod.fst h
      · exact congrArg (fun z => z.2.1) h
      · exact congrArg (fun z => z.2.2) h)

def faceIndex (x : MixedFace p q) : Fin (p + q + 1) :=
  x.upperPosition.castSucc

theorem lowerPosition_lt (x : MixedFace p q) : x.lowerPosition < x.upperPosition := by
  change x.lowerPosition.val < x.upperPosition.val
  have h := x.adjacent
  omega

private theorem lower_lt_deletedVertex_iff_upper_lt (x : MixedFace p q)
    (k : Fin (p + q)) :
    x.lowerPosition.val < (x.faceIndex.succAbove k).val ↔
      x.upperPosition.val < (x.faceIndex.succAbove k).val := by
  dsimp [faceIndex, Fin.succAbove]
  simp only [Fin.castSucc_lt_castSucc_iff, apply_ite Fin.val,
    Fin.val_castSucc, Fin.val_succ]
  have h := x.adjacent
  split_ifs <;> omega

private theorem swap_lt_deletedVertex_iff (x : MixedFace p q)
    (i k : Fin (p + q)) :
    (Equiv.swap x.lowerPosition x.upperPosition i).val <
        (x.faceIndex.succAbove k).val ↔
      i.val < (x.faceIndex.succAbove k).val := by
  rcases eq_or_ne i x.lowerPosition with rfl | hil
  · simpa using x.lower_lt_deletedVertex_iff_upper_lt k |>.symm
  rcases eq_or_ne i x.upperPosition with rfl | hiu
  · simpa using x.lower_lt_deletedVertex_iff_upper_lt k
  simp [Equiv.swap_apply_of_ne_of_ne hil hiu]

private theorem swap_lt_of_lt_of_not_endpoint_pair (x : MixedFace p q)
    {a b : Fin (p + q)} (hab : a < b)
    (hpair : ¬ (a = x.lowerPosition ∧ b = x.upperPosition)) :
    Equiv.swap x.lowerPosition x.upperPosition a <
      Equiv.swap x.lowerPosition x.upperPosition b := by
  rcases eq_or_ne a x.lowerPosition with rfl | hal
  · have hbu : b ≠ x.upperPosition := by
      intro hbu
      exact hpair ⟨rfl, hbu⟩
    have hbl : b ≠ x.lowerPosition := ne_of_gt hab
    simp only [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hbl hbu]
    change x.upperPosition.val < b.val
    have hadj := x.adjacent
    change x.lowerPosition.val < b.val at hab
    omega
  rcases eq_or_ne a x.upperPosition with rfl | hau
  · have hbl : b ≠ x.lowerPosition := by
      exact ne_of_gt (lt_trans x.lowerPosition_lt hab)
    have hbu : b ≠ x.upperPosition := ne_of_gt hab
    simp only [Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hbl hbu]
    exact lt_trans x.lowerPosition_lt hab
  rcases eq_or_ne b x.lowerPosition with rfl | hbl
  · have hau' : a ≠ x.upperPosition := by
      exact ne_of_lt (lt_trans hab x.lowerPosition_lt)
    simp only [Equiv.swap_apply_of_ne_of_ne hal hau', Equiv.swap_apply_left]
    exact lt_trans hab x.lowerPosition_lt
  rcases eq_or_ne b x.upperPosition with rfl | hbu
  · simp only [Equiv.swap_apply_of_ne_of_ne hal hau, Equiv.swap_apply_right]
    change a.val < x.lowerPosition.val
    change a.val < x.upperPosition.val at hab
    have hadj := x.adjacent
    omega
  simp only [Equiv.swap_apply_of_ne_of_ne hal hau,
    Equiv.swap_apply_of_ne_of_ne hbl hbu]
  exact hab

private def swappedLeftPositions (x : MixedFace p q) :
    Set.powersetCard (Fin (p + q)) p :=
  Set.powersetCard.map p
    (Equiv.swap x.lowerPosition x.upperPosition).toEmbedding x.shuffle.leftPositions

private theorem mem_swappedLeftPositions_iff (x : MixedFace p q) (k : Fin (p + q)) :
    k ∈ x.swappedLeftPositions ↔
      Equiv.swap x.lowerPosition x.upperPosition k ∈ x.shuffle.leftPositions := by
  change k ∈ Set.powersetCard.map p
      (Equiv.swap x.lowerPosition x.upperPosition).toEmbedding x.shuffle.leftPositions ↔ _
  rw [Set.powersetCard.mem_map_iff_mem_range]
  constructor
  · rintro ⟨a, ha, hka⟩
    rw [← hka]
    simpa using ha
  · intro hk
    refine ⟨Equiv.swap x.lowerPosition x.upperPosition k, hk, ?_⟩
    simp

def partner (x : MixedFace p q) : MixedFace p q where
  shuffle := ofLeftPositions <|
    Set.powersetCard.map p
      (Equiv.swap x.lowerPosition x.upperPosition).toEmbedding x.shuffle.leftPositions
  lowerPosition := x.lowerPosition
  upperPosition := x.upperPosition
  adjacent := x.adjacent
  mixed := by
    rw [leftPositions_ofLeftPositions]
    change Xor
      (x.lowerPosition ∈ x.swappedLeftPositions)
      (x.upperPosition ∈ x.swappedLeftPositions)
    rcases x.mixed with h | h
    · apply Or.inr
      constructor
      · rw [x.mem_swappedLeftPositions_iff]
        simpa [(x.lowerPosition_lt).ne]
          using h.1
      · rw [x.mem_swappedLeftPositions_iff]
        simpa [(x.lowerPosition_lt).ne]
          using h.2
    · apply Or.inl
      constructor
      · rw [x.mem_swappedLeftPositions_iff]
        simpa [(x.lowerPosition_lt).ne]
          using h.1
      · rw [x.mem_swappedLeftPositions_iff]
        simpa [(x.lowerPosition_lt).ne]
          using h.2

private theorem swappedPerm_isShuffle (x : MixedFace p q) :
    IsShuffle
      ((Equiv.swap x.lowerPosition x.upperPosition) * x.shuffle.perm) := by
  constructor
  · intro i j hij
    change Equiv.swap x.lowerPosition x.upperPosition
        (x.shuffle.perm (Fin.castAdd q i)) <
      Equiv.swap x.lowerPosition x.upperPosition
        (x.shuffle.perm (Fin.castAdd q j))
    apply x.swap_lt_of_lt_of_not_endpoint_pair (x.shuffle.isShuffle.1 hij)
    rintro ⟨hi, hj⟩
    have hlower : x.lowerPosition ∈ x.shuffle.leftPositions := by
      rw [mem_leftPositions_iff]
      exact ⟨i, hi⟩
    have hupper : x.upperPosition ∈ x.shuffle.leftPositions := by
      rw [mem_leftPositions_iff]
      exact ⟨j, hj⟩
    rcases x.mixed with hmixed | hmixed
    · exact hmixed.2 hupper
    · exact hmixed.2 hlower
  · intro i j hij
    change Equiv.swap x.lowerPosition x.upperPosition
        (x.shuffle.perm (Fin.natAdd p i)) <
      Equiv.swap x.lowerPosition x.upperPosition
        (x.shuffle.perm (Fin.natAdd p j))
    apply x.swap_lt_of_lt_of_not_endpoint_pair (x.shuffle.isShuffle.2 hij)
    rintro ⟨hi, hj⟩
    have hlowerRight : x.lowerPosition ∈ x.shuffle.rightPositions := by
      rw [mem_rightPositions_iff]
      exact ⟨i, hi⟩
    have hupperRight : x.upperPosition ∈ x.shuffle.rightPositions := by
      rw [mem_rightPositions_iff]
      exact ⟨j, hj⟩
    have hlower : x.lowerPosition ∉ x.shuffle.leftPositions :=
      (mem_rightPositions_iff_not_mem_leftPositions x.shuffle x.lowerPosition).mp
        hlowerRight
    have hupper : x.upperPosition ∉ x.shuffle.leftPositions :=
      (mem_rightPositions_iff_not_mem_leftPositions x.shuffle x.upperPosition).mp
        hupperRight
    rcases x.mixed with hmixed | hmixed
    · exact hlower hmixed.1
    · exact hupper hmixed.1

private def swappedShuffle (x : MixedFace p q) : Shuffle p q where
  perm := (Equiv.swap x.lowerPosition x.upperPosition) * x.shuffle.perm
  isShuffle := x.swappedPerm_isShuffle

private theorem leftPositions_swappedShuffle (x : MixedFace p q) :
    x.swappedShuffle.leftPositions = x.swappedLeftPositions := by
  apply SetLike.ext
  intro k
  constructor
  · intro hk
    obtain ⟨i, hi⟩ :=
      (mem_leftPositions_iff x.swappedShuffle k).mp hk
    apply (x.mem_swappedLeftPositions_iff k).mpr
    apply (mem_leftPositions_iff x.shuffle _).mpr
    refine ⟨i, ?_⟩
    have hi' := congrArg (Equiv.swap x.lowerPosition x.upperPosition) hi
    simpa [swappedShuffle] using hi'
  · intro hk
    have hk' := (x.mem_swappedLeftPositions_iff k).mp hk
    obtain ⟨i, hi⟩ := (mem_leftPositions_iff x.shuffle _).mp hk'
    apply (mem_leftPositions_iff x.swappedShuffle k).mpr
    refine ⟨i, ?_⟩
    change Equiv.swap x.lowerPosition x.upperPosition
        (x.shuffle.perm (Fin.castAdd q i)) = k
    have hi' := congrArg (Equiv.swap x.lowerPosition x.upperPosition) hi
    simpa using hi'

private theorem partner_shuffle_eq_swappedShuffle (x : MixedFace p q) :
    x.partner.shuffle = x.swappedShuffle := by
  apply equivLeftPositions.injective
  change leftPositions (ofLeftPositions x.swappedLeftPositions) =
    leftPositions x.swappedShuffle
  rw [leftPositions_ofLeftPositions, x.leftPositions_swappedShuffle]

private theorem partner_perm (x : MixedFace p q) :
    x.partner.shuffle.perm =
      (Equiv.swap x.lowerPosition x.upperPosition) * x.shuffle.perm := by
  rw [x.partner_shuffle_eq_swappedShuffle]
  rfl

@[simp]
theorem partner_lowerPosition (x : MixedFace p q) :
    x.partner.lowerPosition = x.lowerPosition := rfl

@[simp]
theorem partner_upperPosition (x : MixedFace p q) :
    x.partner.upperPosition = x.upperPosition := rfl

@[simp]
theorem partner_faceIndex (x : MixedFace p q) : x.partner.faceIndex = x.faceIndex := rfl

@[simp]
theorem partner_partner (x : MixedFace p q) : x.partner.partner = x := by
  apply MixedFace.ext
  · apply equivLeftPositions.injective
    change leftPositions x.partner.partner.shuffle = leftPositions x.shuffle
    change leftPositions (ofLeftPositions x.partner.swappedLeftPositions) =
      leftPositions x.shuffle
    rw [leftPositions_ofLeftPositions]
    apply SetLike.ext
    intro k
    rw [x.partner.mem_swappedLeftPositions_iff]
    change Equiv.swap x.lowerPosition x.upperPosition k ∈
        leftPositions (ofLeftPositions x.swappedLeftPositions) ↔
      k ∈ x.shuffle.leftPositions
    rw [leftPositions_ofLeftPositions]
    rw [x.mem_swappedLeftPositions_iff]
    simp
  · rfl
  · rfl

theorem partner_ne (x : MixedFace p q) : x.partner ≠ x := by
  intro h
  have hshuffle : x.partner.shuffle = x.shuffle := congrArg MixedFace.shuffle h
  have hmem :
      (x.lowerPosition ∈ x.shuffle.leftPositions ↔
        x.upperPosition ∈ x.shuffle.leftPositions) := by
    calc
      x.lowerPosition ∈ x.shuffle.leftPositions ↔
          x.lowerPosition ∈ x.partner.shuffle.leftPositions := by rw [hshuffle]
      _ ↔ x.lowerPosition ∈ x.swappedLeftPositions := by
        change x.lowerPosition ∈ leftPositions (ofLeftPositions x.swappedLeftPositions) ↔ _
        rw [leftPositions_ofLeftPositions]
      _ ↔ x.upperPosition ∈ x.shuffle.leftPositions := by
        rw [x.mem_swappedLeftPositions_iff]
        simp
  exact (xor_iff_not_iff _ _).mp x.mixed hmem

theorem leftHom_partner_succAbove (x : MixedFace p q) (k : Fin (p + q)) :
    x.shuffle.leftHom.toOrderHom (x.faceIndex.succAbove k) =
      x.partner.shuffle.leftHom.toOrderHom (x.faceIndex.succAbove k) := by
  apply Fin.ext
  rw [leftHom_val_eq_card_filter_leftPositions,
    leftHom_val_eq_card_filter_leftPositions]
  change (x.shuffle.leftPositions.val.filter fun i =>
      i.val < (x.faceIndex.succAbove k).val).card =
    ((leftPositions (ofLeftPositions x.swappedLeftPositions)).val.filter fun i =>
      i.val < (x.faceIndex.succAbove k).val).card
  rw [leftPositions_ofLeftPositions]
  change (x.shuffle.leftPositions.val.filter fun i =>
      i.val < (x.faceIndex.succAbove k).val).card =
    ((x.shuffle.leftPositions.val.map
      (Equiv.swap x.lowerPosition x.upperPosition).toEmbedding).filter fun i =>
        i.val < (x.faceIndex.succAbove k).val).card
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  exact x.swap_lt_deletedVertex_iff i k |>.symm

private theorem mem_partner_rightPositions_iff (x : MixedFace p q)
    (k : Fin (p + q)) :
    k ∈ x.partner.shuffle.rightPositions ↔
      Equiv.swap x.lowerPosition x.upperPosition k ∈ x.shuffle.rightPositions := by
  rw [mem_rightPositions_iff_not_mem_leftPositions,
    mem_rightPositions_iff_not_mem_leftPositions]
  change k ∉ leftPositions (ofLeftPositions x.swappedLeftPositions) ↔ _
  rw [leftPositions_ofLeftPositions]
  exact not_congr (x.mem_swappedLeftPositions_iff k)

theorem rightHom_partner_succAbove (x : MixedFace p q) (k : Fin (p + q)) :
    x.shuffle.rightHom.toOrderHom (x.faceIndex.succAbove k) =
      x.partner.shuffle.rightHom.toOrderHom (x.faceIndex.succAbove k) := by
  apply Fin.ext
  rw [rightHom_val_eq_card_filter_rightPositions,
    rightHom_val_eq_card_filter_rightPositions]
  have hright : x.partner.shuffle.rightPositions.val =
      x.shuffle.rightPositions.val.map
        (Equiv.swap x.lowerPosition x.upperPosition).toEmbedding := by
    ext i
    rw [Finset.mem_map]
    constructor
    · intro hi
      refine ⟨Equiv.swap x.lowerPosition x.upperPosition i,
        (x.mem_partner_rightPositions_iff i).mp hi, ?_⟩
      simp
    · rintro ⟨j, hj, rfl⟩
      apply (x.mem_partner_rightPositions_iff _).mpr
      change Equiv.swap x.lowerPosition x.upperPosition
          (Equiv.swap x.lowerPosition x.upperPosition j) ∈ _
      rw [Equiv.swap_apply_self]
      exact hj
  rw [hright, Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  exact x.swap_lt_deletedVertex_iff i k |>.symm

private theorem shuffleSign_partner (x : MixedFace p q) :
    shuffleSign x.partner.shuffle = -shuffleSign x.shuffle := by
  rw [shuffleSign, shuffleSign, x.partner_perm, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap x.lowerPosition_lt.ne]
  simp

private theorem neg_one_pow_crossingNumber_partner (x : MixedFace p q) :
    (-1 : ℤ) ^ x.partner.shuffle.crossingNumber =
      -((-1 : ℤ) ^ x.shuffle.crossingNumber) := by
  rw [← shuffleSignZ_eq_neg_one_pow_crossingNumber,
    ← shuffleSignZ_eq_neg_one_pow_crossingNumber, shuffleSignZ, shuffleSignZ,
    x.shuffleSign_partner]
  simp

theorem shuffleSignZ_partner (x : MixedFace p q) :
    shuffleSignZ x.partner.shuffle = -shuffleSignZ x.shuffle := by
  rw [shuffleSignZ_eq_neg_one_pow_crossingNumber,
    shuffleSignZ_eq_neg_one_pow_crossingNumber]
  exact x.neg_one_pow_crossingNumber_partner

theorem sum_shuffleSignZ_smul_eq_zero {A : Type*} [AddCommGroup A]
    (f : MixedFace p q → A) (hf : ∀ x, f x.partner = f x) :
    ∑ x, shuffleSignZ x.shuffle • f x = 0 := by
  classical
  apply Finset.sum_involution (fun x _ => x.partner)
  · intro x _
    rw [hf x, x.shuffleSignZ_partner]
    simp
  · intro x _ _
    exact x.partner_ne
  · intro x _
    simp
  · intro x _
    simp

end MixedFace

end Shuffle

end AlgebraicTopology.EilenbergZilber
