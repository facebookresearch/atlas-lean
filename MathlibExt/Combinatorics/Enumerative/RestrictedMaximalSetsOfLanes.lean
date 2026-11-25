/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSingles
import Mathlib.Data.Finset.Max
import MathlibExt.Combinatorics.Enumerative.AbsoluteMaximalSetsOfLanes

/-!
# Maximal sets of lanes without U-turns

The theorem `card_restricted_maximalSetsOfLanes` shows that the maximal sets of lanes of the
restricted standard road intersection of size `n`, in which the U-turns `E_iX_i` are forbidden,
are counted by the lonely singles partitions of `Fin n`.

Removing the U-turns from an absolute maximal set of lanes gives a maximal set of lanes of the
restricted intersection, and adding back every U-turn that meets none of its lanes inverts this.
So the count follows from `card_absolute_maximalSetsOfLanes`.

The geometric input is that a maximal set among all lanes uses every entry and every exit. If the
entry `E_a` were unused, take the farthest exit `X_e` (clockwise from `E_a`) such that no lane has
exactly one end strictly between `E_a` and `X_e`. Then `X_e` would be unused too, and the lane
`E_aX_e` could be added.
-/

namespace MetaMathlibExt
namespace card_restricted_maximalSetsOfLanes

open Finset

variable {n : ℕ}

private abbrev Lane (n : ℕ) := Fin n × Fin n

-- The U-turn `E_kX_k` joins adjacent points, so it meets exactly the lanes that use the index `k`.
private theorem meet_loop_right (ℓ : Lane n) (k : Fin n) :
    lanesMeet ℓ (k, k) ↔ ℓ.1 = k ∨ ℓ.2 = k := by
  obtain ⟨i, j⟩ := ℓ
  simp only [lanesMeet]
  omega

private theorem meet_loop_left (k : Fin n) (ℓ : Lane n) :
    lanesMeet (k, k) ℓ ↔ k = ℓ.1 ∨ k = ℓ.2 := by
  obtain ⟨i, j⟩ := ℓ
  simp only [lanesMeet]
  omega

private theorem meet_comm (ℓ ℓ' : Lane n) : lanesMeet ℓ ℓ' ↔ lanesMeet ℓ' ℓ := by
  obtain ⟨i, j⟩ := ℓ
  obtain ⟨k, l⟩ := ℓ'
  simp only [lanesMeet]
  omega

-- The lanes `E_aX_b` and `E_bX_a` separate the same points other than those of `a` and `b`.
private theorem meet_swap {a b k l : Fin n} (hka : k ≠ a) (hkb : k ≠ b) (hla : l ≠ a)
    (hlb : l ≠ b) : lanesMeet (a, b) (k, l) ↔ lanesMeet (b, a) (k, l) := by
  simp only [lanesMeet]
  omega

private theorem not_meet_swap {a b : Fin n} (hab : a ≠ b) : ¬ lanesMeet (a, b) (b, a) := by
  simp only [lanesMeet]
  omega

-- Cut the circle just before the entry `E_a` and unroll it clockwise: `E_x` and `X_x` then sit at
-- `2 * rank a x` and `2 * rank a x + 1`, from `2 * a` (the entry `E_a`) to `2 * a + 2 * n - 1`.
private def rank (a x : Fin n) : ℕ := if x < a then n + x.val else x.val

private theorem rank_inj {a x y : Fin n} : rank a x = rank a y ↔ x = y := by
  simp only [rank]
  split_ifs <;> omega

-- If `k ≠ a` and `l ≠ e`, the lane `E_aX_e` meets `E_kX_l` exactly when just one of `E_k` and `X_l`
-- lies strictly between `E_a` and `X_e` on the unrolled circle.
private theorem meet_base_iff {a e k l : Fin n} (hk : k ≠ a) (hl : l ≠ e) :
    lanesMeet (a, e) (k, l) ↔ ¬ (rank a k ≤ rank a e ↔ rank a l < rank a e) := by
  simp only [lanesMeet, rank]
  split_ifs <;> omega

-- A lane avoiding `E_cX_e`, where `X_e` comes before `E_c` after the cut, has both ends or no end
-- strictly between `X_e` and `E_c`.
private theorem nested_iff {a c e k l : Fin n} (hec : rank a e < rank a c)
    (h : ¬ lanesMeet (c, e) (k, l)) :
    (rank a e < rank a k ∧ rank a k < rank a c) ↔
      (rank a e < rank a l ∧ rank a l < rank a c) := by
  simp only [lanesMeet, rank] at h hec ⊢
  split_ifs at h hec ⊢ <;> omega

-- A maximal set among all lanes uses every entry.
private theorem exists_lane_from {S : Finset (Lane n)}
    (hS : ∀ ℓ ∈ S, ∀ ℓ' ∈ S, ℓ ≠ ℓ' → ¬ lanesMeet ℓ ℓ')
    (hmax : ∀ ℓ, ℓ ∉ S → ∃ ℓ' ∈ S, lanesMeet ℓ ℓ') (a : Fin n) : ∃ j, (a, j) ∈ S := by
  classical
  by_contra! ha
  -- The exits `X_e` such that no lane has exactly one end strictly between `E_a` and `X_e`.
  let good : Finset (Fin n) := univ.filter fun e =>
    ∀ ℓ ∈ S, (rank a ℓ.1 ≤ rank a e ↔ rank a ℓ.2 < rank a e)
  have mem_good (e : Fin n) :
      e ∈ good ↔ ∀ ℓ ∈ S, (rank a ℓ.1 ≤ rank a e ↔ rank a ℓ.2 < rank a e) := by
    simp [good]
  have ha_good : a ∈ good := by
    rw [mem_good]
    rintro ⟨k, l⟩ hkl
    have hk : k ≠ a := fun h => ha l (h ▸ hkl)
    simp only [rank] at hk ⊢
    split_ifs <;> omega
  obtain ⟨e, he, hmax_e⟩ := good.exists_max_image (rank a) ⟨a, ha_good⟩
  rw [mem_good] at he
  by_cases hexit : ∃ c, (c, e) ∈ S
  · -- The lane `E_cX_e` ends after `X_e`, and the exit `X_c` is a farther good exit.
    obtain ⟨c, hc⟩ := hexit
    have hec : rank a e < rank a c := by
      have := he _ hc
      simp only at this
      omega
    have hc_good : c ∈ good := by
      rw [mem_good]
      rintro ⟨k, l⟩ hkl
      by_cases heq : (k, l) = (c, e)
      · rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only
        omega
      · have hd := hS _ hc _ hkl (Ne.symm heq)
        have h1 := nested_iff hec hd
        have h2 := he _ hkl
        have h3 : rank a k ≠ rank a c := fun h => hd (Or.inl (rank_inj.mp h).symm)
        have h4 : rank a l ≠ rank a e := fun h => hd (Or.inr (Or.inl (rank_inj.mp h).symm))
        simp only at h2 ⊢
        omega
    have := hmax_e c hc_good
    omega
  · -- Otherwise the lane `E_aX_e` meets no lane of `S`.
    push Not at hexit
    obtain ⟨⟨k, l⟩, hkl, hm⟩ := hmax (a, e) (ha e)
    have hk : k ≠ a := fun h => ha l (h ▸ hkl)
    have hl : l ≠ e := fun h => hexit k (h ▸ hkl)
    exact (meet_base_iff hk hl).mp hm (he _ hkl)

-- A maximal set among all lanes uses every exit: its lanes have distinct entries and exits.
private theorem exists_lane_to {S : Finset (Lane n)}
    (hS : ∀ ℓ ∈ S, ∀ ℓ' ∈ S, ℓ ≠ ℓ' → ¬ lanesMeet ℓ ℓ')
    (hmax : ∀ ℓ, ℓ ∉ S → ∃ ℓ' ∈ S, lanesMeet ℓ ℓ') (b : Fin n) : ∃ i, (i, b) ∈ S := by
  classical
  have hfst : Set.InjOn Prod.fst (S : Set (Lane n)) := fun ℓ hℓ ℓ' hℓ' h =>
    by_contra fun hne => hS ℓ hℓ ℓ' hℓ' hne (Or.inl h)
  have hsnd : Set.InjOn Prod.snd (S : Set (Lane n)) := fun ℓ hℓ ℓ' hℓ' h =>
    by_contra fun hne => hS ℓ hℓ ℓ' hℓ' hne (Or.inr (Or.inl h))
  have himage : S.image Prod.fst = univ := eq_univ_of_forall fun a => by
    obtain ⟨j, hj⟩ := exists_lane_from hS hmax a
    exact mem_image.mpr ⟨(a, j), hj, rfl⟩
  have hcard : S.card = n := by
    rw [← card_image_of_injOn hfst, himage, card_univ, Fintype.card_fin]
  have himage' : S.image Prod.snd = univ := eq_univ_of_card _ (by
    rw [card_image_of_injOn hsnd, hcard, Fintype.card_fin])
  obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp (himage' ▸ mem_univ b)
  exact ⟨ℓ.1, hℓ⟩

-- The lanes of `S` that are not U-turns.
private def withoutLoops (S : Finset (Lane n)) : Finset (Lane n) :=
  S.filter fun ℓ => ℓ.1 ≠ ℓ.2

-- Add to `T` every U-turn whose index no lane of `T` uses.
private def withLoops (T : Finset (Lane n)) : Finset (Lane n) :=
  T ∪ univ.filter fun ℓ => ℓ.1 = ℓ.2 ∧ ∀ m ∈ T, m.1 ≠ ℓ.1 ∧ m.2 ≠ ℓ.1

private theorem mem_withLoops {T : Finset (Lane n)} {ℓ : Lane n} :
    ℓ ∈ withLoops T ↔ ℓ ∈ T ∨ (ℓ.1 = ℓ.2 ∧ ∀ m ∈ T, m.1 ≠ ℓ.1 ∧ m.2 ≠ ℓ.1) := by
  simp [withLoops]

-- Adding the free U-turns to a maximal set without U-turns gives an absolute maximal set.
private theorem isAbsolute_withLoops {T : Finset (Lane n)}
    (hT : IsMaximalSetOfLanes (univ.filter fun ℓ : Lane n => ℓ.1 ≠ ℓ.2) T) :
    IsAbsoluteMaximalSetOfLanes (withLoops T) := by
  obtain ⟨hsub, hind, hmax⟩ := hT
  have hTne (m : Lane n) (hm : m ∈ T) : m.1 ≠ m.2 := (mem_filter.mp (hsub hm)).2
  have hmsl : IsMaximalSetOfLanes univ (withLoops T) := by
    refine ⟨subset_univ _, ?_, ?_⟩
    · intro x hx y hy hne
      rw [mem_withLoops] at hx hy
      rcases hx with hx | ⟨hx1, hx2⟩ <;> rcases hy with hy | ⟨hy1, hy2⟩
      · exact hind x hx y hy hne
      · obtain ⟨k, k'⟩ := y
        obtain rfl : k = k' := hy1
        rw [meet_loop_right]
        have := hy2 x hx
        tauto
      · obtain ⟨k, k'⟩ := x
        obtain rfl : k = k' := hx1
        rw [meet_loop_left]
        have := hx2 y hy
        simp only at this ⊢
        omega
      · obtain ⟨k, k'⟩ := x
        obtain rfl : k = k' := hx1
        obtain ⟨l, l'⟩ := y
        obtain rfl : l = l' := hy1
        rw [meet_loop_left]
        simp only [ne_eq, Prod.mk.injEq, and_self] at hne ⊢
        tauto
    · intro ℓ _ hℓ
      rw [mem_withLoops] at hℓ
      push Not at hℓ
      by_cases hloop : ℓ.1 = ℓ.2
      · obtain ⟨m, hm, hmeet⟩ := hℓ.2 hloop
        refine ⟨m, mem_union_left _ hm, ?_⟩
        obtain ⟨k, k'⟩ := ℓ
        obtain rfl : k = k' := hloop
        rw [meet_loop_left]
        simp only at hmeet ⊢
        by_cases h : m.1 = k
        · exact Or.inl h.symm
        · exact Or.inr (hmeet h).symm
      · obtain ⟨m, hm, hmeet⟩ := hmax ℓ (mem_filter.mpr ⟨mem_univ _, hloop⟩) hℓ.1
        exact ⟨m, mem_union_left _ hm, hmeet⟩
  refine ⟨hmsl, ?_⟩
  -- After exchanging two free U-turns, the lane `E_iX_j` would still meet a lane of `T`.
  rintro ⟨i, j, hij, hi, -, hexch⟩
  have hi' : ∀ m ∈ T, m.1 ≠ i ∧ m.2 ≠ i := by
    rcases mem_withLoops.mp hi with hi | ⟨-, hi⟩
    · exact absurd rfl (hTne _ hi)
    · exact hi
  have hijT : (i, j) ∉ T := fun h => (hi' _ h).1 rfl
  obtain ⟨m, hm, hmeet⟩ := hmax (i, j) (mem_filter.mpr ⟨mem_univ _, hij⟩) hijT
  have hm' : m ∈ insert (i, j) (insert (j, i) (((withLoops T).erase (i, i)).erase (j, j))) := by
    refine mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_,
      mem_union_left _ hm⟩⟩))
    · rintro rfl
      exact hTne _ hm rfl
    · rintro rfl
      exact hTne _ hm rfl
  exact hexch.2.1 (i, j) (mem_insert_self _ _) m hm' (fun h => hijT (h ▸ hm)) hmeet

-- Removing the U-turns from an absolute maximal set gives a maximal set without U-turns.
private theorem isMaximal_withoutLoops {S : Finset (Lane n)}
    (hS : IsAbsoluteMaximalSetOfLanes S) :
    IsMaximalSetOfLanes (univ.filter fun ℓ : Lane n => ℓ.1 ≠ ℓ.2) (withoutLoops S) := by
  obtain ⟨⟨-, hind, hmax⟩, habs⟩ := hS
  have hmax' (ℓ : Lane n) (hℓ : ℓ ∉ S) : ∃ ℓ' ∈ S, lanesMeet ℓ ℓ' := hmax ℓ (mem_univ _) hℓ
  refine ⟨fun ℓ hℓ => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hℓ).2⟩,
    fun ℓ hℓ ℓ' hℓ' => hind ℓ (filter_subset _ _ hℓ) ℓ' (filter_subset _ _ hℓ'), ?_⟩
  rintro ⟨a, b⟩ hab hnot
  replace hab : a ≠ b := (mem_filter.mp hab).2
  by_contra hno
  push Not at hno
  -- The entry `E_a` and the exit `X_b` are used by U-turns.
  obtain ⟨d, hd⟩ := exists_lane_from hind hmax' a
  obtain rfl : a = d := by
    by_contra hda
    exact hno (a, d) (mem_filter.mpr ⟨hd, hda⟩) (Or.inl rfl)
  obtain ⟨c, hc⟩ := exists_lane_to hind hmax' b
  obtain rfl : b = c := by
    by_contra hcb
    exact hno (c, b) (mem_filter.mpr ⟨hc, Ne.symm hcb⟩) (Or.inr (Or.inl rfl))
  -- Exchanging them for `E_aX_b` and `E_bX_a` gives a maximal set, contradicting absoluteness.
  apply habs
  refine ⟨a, b, hab, hd, hc, ?_⟩
  set R := (S.erase (a, a)).erase (b, b) with hR
  have mem_R {m : Lane n} : m ∈ R ↔ m ≠ (b, b) ∧ m ≠ (a, a) ∧ m ∈ S := by
    simp [hR]
  -- The lanes of `R` avoid the indices `a` and `b`.
  have avoid {m : Lane n} (hm : m ∈ R) : m.1 ≠ a ∧ m.2 ≠ a ∧ m.1 ≠ b ∧ m.2 ≠ b := by
    obtain ⟨hmb, hma, hmS⟩ := mem_R.mp hm
    have h1 := (meet_loop_right m a).not.mp (hind m hmS _ hd hma)
    have h2 := (meet_loop_right m b).not.mp (hind m hmS _ hc hmb)
    tauto
  have not_meet_ab {m : Lane n} (hm : m ∈ R) : ¬ lanesMeet (a, b) m := by
    obtain ⟨hmb, hma, hmS⟩ := mem_R.mp hm
    by_cases hloop : m.1 = m.2
    · obtain ⟨k, k'⟩ := m
      obtain rfl : k = k' := hloop
      have := avoid hm
      rw [meet_loop_right]
      simp only at this ⊢
      tauto
    · exact hno m (mem_filter.mpr ⟨hmS, hloop⟩)
  have not_meet_ba {m : Lane n} (hm : m ∈ R) : ¬ lanesMeet (b, a) m := by
    obtain ⟨k, l⟩ := m
    have := avoid hm
    rw [← meet_swap this.1 this.2.2.1 this.2.1 this.2.2.2]
    exact not_meet_ab hm
  refine ⟨subset_univ _, ?_, ?_⟩
  · intro x hx y hy hne
    simp only [mem_insert] at hx hy
    rcases hx with rfl | rfl | hx <;> rcases hy with rfl | rfl | hy
    · exact absurd rfl hne
    · exact not_meet_swap hab
    · exact not_meet_ab hy
    · exact not_meet_swap (Ne.symm hab)
    · exact absurd rfl hne
    · exact not_meet_ba hy
    · rw [meet_comm]
      exact not_meet_ab hx
    · rw [meet_comm]
      exact not_meet_ba hx
    · exact hind x (mem_R.mp hx).2.2 y (mem_R.mp hy).2.2 hne
  · intro ℓ _ hℓ
    simp only [mem_insert, not_or] at hℓ
    obtain ⟨hℓab, hℓba, hℓR⟩ := hℓ
    by_cases hℓa : ℓ = (a, a)
    · subst hℓa
      exact ⟨(a, b), mem_insert_self _ _, Or.inl rfl⟩
    by_cases hℓb : ℓ = (b, b)
    · subst hℓb
      exact ⟨(b, a), mem_insert_of_mem (mem_insert_self _ _), Or.inl rfl⟩
    have hℓS : ℓ ∉ S := fun h => hℓR (mem_R.mpr ⟨hℓb, hℓa, h⟩)
    obtain ⟨m, hm, hmeet⟩ := hmax' ℓ hℓS
    by_cases hma : m = (a, a)
    · subst hma
      rcases (meet_loop_right ℓ a).mp hmeet with h | h
      · exact ⟨(a, b), mem_insert_self _ _, Or.inl h⟩
      · exact ⟨(b, a), mem_insert_of_mem (mem_insert_self _ _), Or.inr (Or.inl h)⟩
    by_cases hmb : m = (b, b)
    · subst hmb
      rcases (meet_loop_right ℓ b).mp hmeet with h | h
      · exact ⟨(b, a), mem_insert_of_mem (mem_insert_self _ _), Or.inl h⟩
      · exact ⟨(a, b), mem_insert_self _ _, Or.inr (Or.inl h)⟩
    exact ⟨m, mem_insert_of_mem (mem_insert_of_mem (mem_R.mpr ⟨hmb, hma, hm⟩)), hmeet⟩

private theorem withoutLoops_withLoops {T : Finset (Lane n)} (hT : ∀ m ∈ T, m.1 ≠ m.2) :
    withoutLoops (withLoops T) = T := by
  ext ℓ
  simp only [withoutLoops, mem_filter, mem_withLoops]
  constructor
  · rintro ⟨h | ⟨h1, -⟩, h2⟩
    · exact h
    · exact absurd h1 h2
  · intro h
    exact ⟨Or.inl h, hT ℓ h⟩

-- A U-turn lies in a maximal set among all lanes exactly when no other lane of it uses its index.
private theorem withLoops_withoutLoops {S : Finset (Lane n)}
    (hS : IsMaximalSetOfLanes univ S) : withLoops (withoutLoops S) = S := by
  obtain ⟨-, hind, hmax⟩ := hS
  ext ℓ
  simp only [mem_withLoops, withoutLoops, mem_filter]
  by_cases hloop : ℓ.1 = ℓ.2
  · obtain ⟨k, k'⟩ := ℓ
    obtain rfl : k = k' := hloop
    simp only [ne_eq, not_true_eq_false, and_false, true_and, false_or, and_imp]
    constructor
    · intro h
      by_contra hk
      obtain ⟨m, hm, hmeet⟩ := hmax (k, k) (mem_univ _) hk
      rw [meet_loop_left] at hmeet
      by_cases hm' : m.1 = m.2
      · obtain ⟨i, j⟩ := m
        obtain rfl : i = j := hm'
        simp only [or_self] at hmeet
        exact hk (hmeet ▸ hm)
      · have := h m hm hm'
        tauto
    · intro hk m hm hm'
      have hne : m ≠ (k, k) := by
        rintro rfl
        exact hm' rfl
      have := (meet_loop_right m k).not.mp (hind m hm _ hk hne)
      tauto
  · simp [hloop]

end card_restricted_maximalSetsOfLanes

open card_restricted_maximalSetsOfLanes in
/-- **Maximal sets of lanes without U-turns are counted by lonely singles partitions.** For every
$n \ge 0$, consider the restricted standard road intersection of size $n$, in which the lane
$E_iX_j$ from the entry $E_i$ to the exit $X_j$, for $i, j \in \{0, \dots, n-1\}$, is allowed
exactly when $i \ne j$ (the U-turns $E_iX_i$ are forbidden). The number of maximal sets of lanes
among these allowed lanes equals $L_n$, the number of noncrossing partitions of
$\{0, \dots, n-1\}$ that are not marriageable singles partitions.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 19
(`jis-2025-25.1.1-cor-19`). -/
public theorem card_restricted_maximalSetsOfLanes (n : ℕ) :
    (Finset.univ.filter fun S : Finset (Fin n × Fin n) =>
      IsMaximalSetOfLanes (Finset.univ.filter fun ℓ : Fin n × Fin n => ℓ.1 ≠ ℓ.2) S).card =
      lonelySinglesCount n := by
  rw [← card_absolute_maximalSetsOfLanes]
  refine Finset.card_nbij' withLoops withoutLoops (fun T hT => ?_) (fun S hS => ?_)
    (fun T hT => ?_) (fun S hS => ?_)
  · replace hT := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isAbsolute_withLoops hT⟩)
  · replace hS := (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isMaximal_withoutLoops hS⟩)
  · replace hT := (Finset.mem_filter.mp (Finset.mem_coe.mp hT)).2
    exact withoutLoops_withLoops fun m hm => (Finset.mem_filter.mp (hT.1 hm)).2
  · exact withLoops_withoutLoops (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).2.1

end MetaMathlibExt
