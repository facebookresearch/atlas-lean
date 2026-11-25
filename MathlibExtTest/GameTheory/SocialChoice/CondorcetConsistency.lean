/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import MathlibExt.GameTheory.SocialChoice.CondorcetConsistency
set_option autoImplicit false
namespace MathlibExtTest.GameTheory.SocialChoice.CondorcetConsistency
open Classical
open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open MathlibExt.GameTheory.SocialChoice
open scoped BigOperators
@[expose] public section
def rankA : Fin 3 → ℕ := fun x => x.val
def rankB : Fin 3 → ℕ :=
  fun x => if x = 1 then 0 else if x = 2 then 1 else 2
def orderA : MathlibExt.Order.StrictTotalOrder (Fin 3) where
  lt := fun x y => rankA x < rankA y
  irrefl := fun x => lt_irrefl _
  trans := fun {x y z} h1 h2 => lt_trans h1 h2
  total := fun {x y} h => by
    have hne : rankA x ≠ rankA y := fun heq => h (Fin.ext heq)
    have htri := lt_or_gt_of_ne hne
    cases htri with
    | inl hlt => exact Or.inl hlt
    | inr hgt => exact Or.inr hgt
theorem orderB_total : ∀ x y : Fin 3,
    x ≠ y → rankB x < rankB y ∨ rankB y < rankB x := by
  decide
def orderB : MathlibExt.Order.StrictTotalOrder (Fin 3) where
  lt := fun x y => rankB x < rankB y
  irrefl := fun _x => lt_irrefl _
  trans := fun {_x _y _z} h1 h2 => lt_trans h1 h2
  total := fun {x y} h => orderB_total x y h
/-- Five-voter profile over three alternatives: voters `0, 1, 2` rank
`0` above `1` above `2`, while voters `3, 4` rank `1` above `2` above `0`. -/
def bordaP : Profile (Fin 3) (Fin 5) :=
  fun i => if i.val < 3 then orderA else orderB
private theorem bordaP_eq_orderA (i : Fin 5) (h : i.val < 3) :
    bordaP i = orderA := by
  unfold bordaP
  rw [ite_eq_left h]
private theorem bordaP_eq_orderB (i : Fin 5) (h : ¬ i.val < 3) :
    bordaP i = orderB := by
  unfold bordaP
  rw [ite_eq_right h]
private theorem bordaP_lt_01 (i : Fin 5) : (bordaP i).lt 0 1 ↔ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bordaP_eq_orderA i h]
    show (0 : Fin 3).val < (1 : Fin 3).val ↔ i.val < 3
    exact iff_of_true (by decide) h
  · rw [bordaP_eq_orderB i h]
    show rankB 0 < rankB 1 ↔ i.val < 3
    exact iff_of_false (by decide) h
private theorem bordaP_lt_10 (i : Fin 5) : (bordaP i).lt 1 0 ↔ ¬ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bordaP_eq_orderA i h]
    show (1 : Fin 3).val < (0 : Fin 3).val ↔ ¬ i.val < 3
    exact iff_of_false (by decide) (not_not_intro h)
  · rw [bordaP_eq_orderB i h]
    show rankB 1 < rankB 0 ↔ ¬ i.val < 3
    exact iff_of_true (by decide) h
private theorem bordaP_lt_02 (i : Fin 5) : (bordaP i).lt 0 2 ↔ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bordaP_eq_orderA i h]
    show (0 : Fin 3).val < (2 : Fin 3).val ↔ i.val < 3
    exact iff_of_true (by decide) h
  · rw [bordaP_eq_orderB i h]
    show rankB 0 < rankB 2 ↔ i.val < 3
    exact iff_of_false (by decide) h
private theorem bordaP_lt_20 (i : Fin 5) : (bordaP i).lt 2 0 ↔ ¬ i.val < 3 := by
  by_cases h : i.val < 3
  · rw [bordaP_eq_orderA i h]
    show (2 : Fin 3).val < (0 : Fin 3).val ↔ ¬ i.val < 3
    exact iff_of_false (by decide) (not_not_intro h)
  · rw [bordaP_eq_orderB i h]
    show rankB 2 < rankB 0 ↔ ¬ i.val < 3
    exact iff_of_true (by decide) h
private theorem filter_lt_01 :
    Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 0 1) = {0, 1, 2} := by
  have hcongr : Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 0 1)
      = Finset.univ.filter (fun i : Fin 5 => i.val < 3) :=
    Finset.filter_congr (fun i _ => bordaP_lt_01 i)
  rw [hcongr]
  decide
private theorem filter_lt_10 :
    Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 1 0) = {3, 4} := by
  have hcongr : Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 1 0)
      = Finset.univ.filter (fun i : Fin 5 => ¬ i.val < 3) :=
    Finset.filter_congr (fun i _ => bordaP_lt_10 i)
  rw [hcongr]
  decide
private theorem filter_lt_02 :
    Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 0 2) = {0, 1, 2} := by
  have hcongr : Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 0 2)
      = Finset.univ.filter (fun i : Fin 5 => i.val < 3) :=
    Finset.filter_congr (fun i _ => bordaP_lt_02 i)
  rw [hcongr]
  decide
private theorem filter_lt_20 :
    Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 2 0) = {3, 4} := by
  have hcongr : Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 2 0)
      = Finset.univ.filter (fun i : Fin 5 => ¬ i.val < 3) :=
    Finset.filter_congr (fun i _ => bordaP_lt_20 i)
  rw [hcongr]
  decide
private theorem card_lt_01 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 0 1)).card = 3 := by
  rw [filter_lt_01]
  decide
private theorem card_lt_10 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 1 0)).card = 2 := by
  rw [filter_lt_10]
  decide
private theorem card_lt_02 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 0 2)).card = 3 := by
  rw [filter_lt_02]
  decide
private theorem card_lt_20 :
    (Finset.univ.filter (fun i : Fin 5 => (bordaP i).lt 2 0)).card = 2 := by
  rw [filter_lt_20]
  decide
private theorem h01 : CondorcetCycle.MajorityPrefers bordaP 0 1 := by
  rw [majorityPrefers_iff_netPreference_pos]
  simp only [netPreference]
  rw [card_lt_01, card_lt_10]
  decide
private theorem h02 : CondorcetCycle.MajorityPrefers bordaP 0 2 := by
  rw [majorityPrefers_iff_netPreference_pos]
  simp only [netPreference]
  rw [card_lt_02, card_lt_20]
  decide
theorem t1_borda_condorcet_winner : IsCondorcetWinner bordaP 0 := by
  intro b hb
  have hb0 : b.val ≠ 0 :=
    fun h => hb (Fin.ext (by show b.val = (0 : Fin 3).val; rw [h]; rfl))
  have hv2 : b.val = 1 ∨ b.val = 2 := by
    have h3 := b.isLt
    omega
  cases hv2 with
  | inl h1 =>
    have hb1 : b = 1 :=
      Fin.ext (by show b.val = (1 : Fin 3).val; rw [h1]; rfl)
    rw [hb1]
    exact h01
  | inr h2 =>
    have hb2 : b = 2 :=
      Fin.ext (by show b.val = (2 : Fin 3).val; rw [h2]; rfl)
    rw [hb2]
    exact h02
private theorem innerA0 :
    Finset.univ.filter (fun b : Fin 3 => orderA.lt 0 b) = {1, 2} := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => orderA.lt 0 b)
      = Finset.univ.filter (fun b : Fin 3 => (0 : Fin 3).val < b.val) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem innerB0 :
    Finset.univ.filter (fun b : Fin 3 => orderB.lt 0 b) = ∅ := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => orderB.lt 0 b)
      = Finset.univ.filter (fun b : Fin 3 => rankB 0 < rankB b) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem innerA1 :
    Finset.univ.filter (fun b : Fin 3 => orderA.lt 1 b) = {2} := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => orderA.lt 1 b)
      = Finset.univ.filter (fun b : Fin 3 => (1 : Fin 3).val < b.val) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem innerB1 :
    Finset.univ.filter (fun b : Fin 3 => orderB.lt 1 b) = {2, 0} := by
  have hcongr : Finset.univ.filter (fun b : Fin 3 => orderB.lt 1 b)
      = Finset.univ.filter (fun b : Fin 3 => rankB 1 < rankB b) :=
    Finset.filter_congr (fun b _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem hper0 : ∀ i ∈ Finset.univ,
    (Finset.univ.filter (fun b : Fin 3 => (bordaP i).lt 0 b)).card =
      (if i.val < 3 then 2 else 0) := by
  intro i _
  by_cases h : i.val < 3
  · rw [ite_eq_left h, bordaP_eq_orderA i h, innerA0]
    decide
  · rw [ite_eq_right h, bordaP_eq_orderB i h, innerB0]
    exact Finset.card_empty
private theorem hper1 : ∀ i ∈ Finset.univ,
    (Finset.univ.filter (fun b : Fin 3 => (bordaP i).lt 1 b)).card =
      (if i.val < 3 then 1 else 2) := by
  intro i _
  by_cases h : i.val < 3
  · rw [ite_eq_left h, bordaP_eq_orderA i h, innerA1]
    exact Finset.card_singleton 2
  · rw [ite_eq_right h, bordaP_eq_orderB i h, innerB1]
    decide
private theorem bordaScore_zero : bordaScore bordaP 0 = 6 := by
  simp only [bordaScore]
  rw [Finset.sum_congr rfl hper0]
  decide
private theorem bordaScore_one : bordaScore bordaP 1 = 7 := by
  simp only [bordaScore]
  rw [Finset.sum_congr rfl hper1]
  decide
theorem t2_borda_not_consistent : bordaScore bordaP 0 = 6 ∧
    bordaScore bordaP 1 = 7 ∧
    (0 : Fin 3) ∉ winners (fun a => (bordaScore bordaP a : ℤ)) := by
  refine ⟨bordaScore_zero, bordaScore_one, ?_⟩
  intro hmem
  simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  have hle := hmem 1
  rw [bordaScore_zero, bordaScore_one] at hle
  exact absurd hle (by decide)
theorem t3_borda_copeland_consistent :
    winners (copelandScore bordaP) = {0} :=
  winners_copelandScore_of_isCondorcetWinner bordaP t1_borda_condorcet_winner
private theorem not_isCondorcetWinner_one :
    ¬ IsCondorcetWinner bordaP 1 := by
  intro hw
  have h10 := (isCondorcetWinner_iff bordaP 1).mp hw 0 (by decide)
  have h01pos := (majorityPrefers_iff_netPreference_pos bordaP 0 1).mp h01
  have hanti := netPreference_antisymm bordaP 1 0
  omega
theorem t4_borda_condorcet_margins :
    (∀ b ≠ (0 : Fin 3), 0 < netPreference bordaP 0 b) ∧
      ¬ IsCondorcetWinner bordaP 1 :=
  ⟨(isCondorcetWinner_iff bordaP 0).mp t1_borda_condorcet_winner,
    not_isCondorcetWinner_one⟩
theorem t5_borda_maximin_consistent :
    winners (maximinScore bordaP) = {0} :=
  winners_maximinScore_of_isCondorcetWinner bordaP
    t1_borda_condorcet_winner
theorem t6_borda_kemeny_top :
    ∃ r, IsKemenyRanking bordaP r ∧ r.lt 0 1 ∧ r.lt 0 2 := by
  obtain ⟨r, hr⟩ := exists_isKemenyRanking bordaP
  refine ⟨r, hr, ?_, ?_⟩
  · exact isKemenyRanking_top_of_isCondorcetWinner bordaP
      t1_borda_condorcet_winner hr 1 (by decide)
  · exact isKemenyRanking_top_of_isCondorcetWinner bordaP
      t1_borda_condorcet_winner hr 2 (by decide)
theorem t7_borda_dodgson_consistent :
    dodgsonScore bordaP 0 = 0 ∧ dodgsonScore bordaP 1 ≠ 0 :=
  ⟨(dodgsonScore_eq_zero_iff bordaP 0).mpr t1_borda_condorcet_winner,
    fun h => not_isCondorcetWinner_one
      ((dodgsonScore_eq_zero_iff bordaP 1).mp h)⟩
theorem t8_borda_prod_not_consistent :
    IsCondorcetWinner bordaP 0 ∧
      (0 : Fin 3) ∉ winners (fun a => (bordaScore bordaP a : ℤ)) ∧
      ∃ (P : Profile (Fin 3) (Fin 5)) (a : Fin 3),
        IsCondorcetWinner P a ∧ a ∉ winners (fun x => (bordaScore P x : ℤ)) :=
  ⟨t1_borda_condorcet_winner, t2_borda_not_consistent.2.2,
    exists_isCondorcetWinner_notMem_winners_bordaScore⟩
end
end MathlibExtTest.GameTheory.SocialChoice.CondorcetConsistency
