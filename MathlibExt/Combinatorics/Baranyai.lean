/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace MetaMathlibExt

section

/-- Count of positions `(i, j)` with `A i j = S`. -/
private def baranyai_cnt {n L a : ℕ} (A : Fin L → Fin a → Finset (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = S)).card

/-- The strengthened induction hypothesis: `L` partial classes over `U`. -/
private def baranyai_Good (n k L a : ℕ) (U : Finset (Fin n))
    (A : Fin L → Fin a → Finset (Fin n)) : Prop :=
  (∀ i j, A i j ⊆ U) ∧
  (∀ i j j', j ≠ j' → Disjoint (A i j) (A i j')) ∧
  (∀ i, Finset.univ.biUnion (A i) = U) ∧
  (∀ i j, (A i j).card ≤ k) ∧
  (∀ S ⊆ U, S.card ≤ k → baranyai_cnt A S = (n - U.card).choose (k - S.card))

/-- Insert `x` into the chosen block of each class. -/
private def baranyai_extend {n L a : ℕ} (A : Fin L → Fin a → Finset (Fin n))
    (J : Fin L → Fin a) (x : Fin n) : Fin L → Fin a → Finset (Fin n) :=
  fun i j => if j = J i then insert x (A i j) else A i j

private theorem baranyai_exists_dims (n h : ℕ) (hd : h ∣ n) :
    ∃ L a : ℕ, a * h = n ∧ L * a = n.choose h := by
  by_cases hh : h = 0
  · subst hh
    have hn : n = 0 := Nat.eq_zero_of_zero_dvd hd
    subst hn
    exact ⟨1, 1, by simp, by simp⟩
  · refine ⟨(n - 1).choose (h - 1), n / h, Nat.div_mul_cancel hd, ?_⟩
    by_cases hn : n = 0
    · subst hn
      have hpos : 0 < h := Nat.pos_of_ne_zero hh
      simp [Nat.choose_eq_zero_of_lt hpos]
    · have hpos : 0 < h := Nat.pos_of_ne_zero hh
      have key := Nat.add_one_mul_choose_eq (n - 1) (h - 1)
      rw [Nat.sub_one_add_one hn, Nat.sub_one_add_one hh] at key
      have hmul : (n - 1).choose (h - 1) * (n / h) * h = n.choose h * h := by
        rw [mul_assoc, Nat.div_mul_cancel hd, mul_comm]
        exact key
      exact Nat.eq_of_mul_eq_mul_right hpos hmul

private theorem baranyai_choose_mul (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    r * d.choose r = d * (d - 1).choose (r - 1) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := d) (by omega)
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := r) (by omega)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq d' r'
  rw [mul_comm (r' + 1) _, ← h, mul_comm]

private theorem baranyai_choose_pascal (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    d.choose r = (d - 1).choose (r - 1) + (d - 1).choose r := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := d) (by omega)
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := r) (by omega)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  exact Nat.choose_succ_succ' d' r'

private theorem baranyai_good_empty (n k L a : ℕ) (HLa : L * a = n.choose k) :
    baranyai_Good n k L a ∅ (fun _ _ => ∅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact Finset.empty_subset _
  · intro i j j' _
    exact Finset.disjoint_empty_left _
  · intro i
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨_, _, hj⟩ := hy
    exact Finset.notMem_empty y hj
  · intro i j
    rw [Finset.card_empty]
    exact Nat.zero_le _
  · intro S hsub _
    have hS0 : S = ∅ := Finset.subset_empty.mp hsub
    subst hS0
    unfold baranyai_cnt
    have hfilter : Finset.univ.filter
        (fun p : Fin L × Fin a => (fun _ _ => (∅ : Finset (Fin n))) p.1 p.2 = ∅) =
        Finset.univ := by
      apply Finset.filter_true_of_mem
      intro p _
      rfl
    rw [hfilter, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Finset.card_empty, Nat.sub_zero, Nat.sub_zero]
    exact HLa

private theorem baranyai_rowSum {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a U A) (Hak : a * k = n) (i : Fin L) :
    ∑ j : Fin a, (k - (A i j).card) = n - U.card := by
  obtain ⟨_, hG2, hG3, hG4, _⟩ := hG
  have hdisj : (↑(Finset.univ : Finset (Fin a)) : Set (Fin a)).PairwiseDisjoint
      (A i) := by
    intro j _ j' _ hne
    exact hG2 i j j' hne
  have hcard := Finset.card_biUnion hdisj
  rw [hG3 i] at hcard
  have hsum : ∑ j ∈ Finset.univ, (A i j).card = U.card := hcard.symm
  have hadd : (∑ j : Fin a, (k - (A i j).card)) + (∑ j : Fin a, (A i j).card) =
      ∑ _j : Fin a, k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Nat.sub_add_cancel (hG4 i j)
  have hconst : (∑ _j : Fin a, k) = n := by
    have h2 : ∑ _x ∈ (Finset.univ : Finset (Fin a)), k =
        (Finset.univ : Finset (Fin a)).card * k :=
      Finset.sum_const_nat (fun x _ => rfl)
    rw [Finset.card_fin] at h2
    rw [h2, Hak]
  omega

private theorem baranyai_fiberSum {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a U A) (hlt : U.card < n)
    (N : Finset (Finset (Fin n)))
    (hN : ∀ S ∈ N, S ⊆ U ∧ S.card < k) :
    (n - U.card) * ∑ S ∈ N, (n - U.card - 1).choose (k - S.card - 1) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 ∈ N),
        (k - (A p.1 p.2).card) := by
  obtain ⟨_, _, _, _, hG5⟩ := hG
  have hd_pos : 0 < n - U.card := Nat.sub_pos_of_lt hlt
  have hterm : ∀ S ∈ N, (n - U.card) * ((n - U.card - 1).choose (k - S.card - 1)) =
      (k - S.card) * baranyai_cnt A S := by
    intro S hS
    obtain ⟨hSU, hSk⟩ := hN S hS
    have hkle : S.card ≤ k := by omega
    have hr : 0 < k - S.card := by omega
    rw [hG5 S hSU hkle]
    exact (baranyai_choose_mul (n - U.card) (k - S.card) hd_pos hr).symm
  have hinner : ∀ S ∈ N,
      (∑ p ∈ (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 ∈ N)).filter
        (fun p => A p.1 p.2 = S), (k - (A p.1 p.2).card)) =
      (k - S.card) * baranyai_cnt A S := by
    intro S hS
    have hset : ((Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 ∈ N)).filter
        (fun p => A p.1 p.2 = S)) =
        Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = S) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h
        exact h.2
      · intro h
        constructor
        · rw [h]
          exact hS
        · exact h
    rw [hset]
    have hconst : ∀ p ∈ Finset.univ.filter
        (fun p : Fin L × Fin a => A p.1 p.2 = S),
        (k - (A p.1 p.2).card) = (k - S.card) := by
      intro p hp
      have heq : A p.1 p.2 = S := (Finset.mem_filter.mp hp).2
      rw [heq]
    have hcc := Finset.sum_const_nat hconst
    unfold baranyai_cnt
    rw [hcc, mul_comm]
  rw [Finset.mul_sum]
  have hmaps : ∀ p ∈ Finset.univ.filter
      (fun p : Fin L × Fin a => A p.1 p.2 ∈ N),
      (fun p : Fin L × Fin a => A p.1 p.2) p ∈ N := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p : Fin L × Fin a => (k - (A p.1 p.2).card))
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [hterm S hS, hinner S hS]

private theorem baranyai_hall_condition {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a U A) (Hak : a * k = n) (hlt : U.card < n)
    (s : Finset (Fin L)) :
    s.card ≤
      ∑ S ∈ s.biUnion
        (fun i : Fin L => (Finset.univ.image (A i)).filter (fun S => S.card < k)),
        (n - U.card - 1).choose (k - S.card - 1) := by
  have hG1 : ∀ (i : Fin L) (j : Fin a), A i j ⊆ U := by
    obtain ⟨h1, _, _, _, _⟩ := hG
    exact h1
  have hd_pos : 0 < n - U.card := Nat.sub_pos_of_lt hlt
  have h1 : (n - U.card) * s.card =
      ∑ i ∈ s, ∑ j : Fin a, (k - (A i j).card) := by
    have hcc : ∑ _i ∈ s, (n - U.card) = s.card * (n - U.card) :=
      Finset.sum_const_nat (fun i _ => rfl)
    rw [mul_comm (n - U.card) s.card, ← hcc]
    apply Finset.sum_congr rfl
    intro i _
    exact (baranyai_rowSum hG Hak i).symm
  have h2 : (∑ i ∈ s, ∑ j : Fin a, (k - (A i j).card)) =
      ∑ p ∈ s ×ˢ Finset.univ, (k - (A p.1 p.2).card) := by
    rw [Finset.sum_product]
  have h3 : (∑ p ∈ (s ×ˢ Finset.univ).filter
      (fun p : Fin L × Fin a => (A p.1 p.2).card < k),
        (k - (A p.1 p.2).card)) =
      ∑ p ∈ s ×ˢ Finset.univ, (k - (A p.1 p.2).card) := by
    apply Finset.sum_filter_of_ne
    intro p _ hne
    omega
  have h23 : (∑ i ∈ s, ∑ j : Fin a, (k - (A i j).card)) =
      ∑ p ∈ (s ×ˢ Finset.univ).filter
        (fun p : Fin L × Fin a => (A p.1 p.2).card < k),
          (k - (A p.1 p.2).card) :=
    h2.trans h3.symm
  have hsub : ((s ×ˢ Finset.univ).filter
      (fun p : Fin L × Fin a => (A p.1 p.2).card < k)) ⊆
      Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 ∈ s.biUnion
        (fun i : Fin L => (Finset.univ.image (A i)).filter
          (fun S => S.card < k))) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hmem, hltp⟩ := hp
    constructor
    · exact Finset.mem_univ p
    · rw [Finset.mem_product] at hmem
      obtain ⟨hi, _⟩ := hmem
      have hmem2 : A p.1 p.2 ∈ (Finset.univ.image (A p.1)).filter
          (fun S => S.card < k) := by
        rw [Finset.mem_filter]
        constructor
        · apply Finset.mem_image_of_mem
          exact Finset.mem_univ p.2
        · exact hltp
      exact Finset.mem_biUnion.mpr ⟨p.1, hi, hmem2⟩
  have h4 : (∑ p ∈ (s ×ˢ Finset.univ).filter
      (fun p : Fin L × Fin a => (A p.1 p.2).card < k),
        (k - (A p.1 p.2).card)) ≤
      (∑ p ∈ Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 ∈ s.biUnion
        (fun i : Fin L => (Finset.univ.image (A i)).filter
          (fun S => S.card < k))), (k - (A p.1 p.2).card)) :=
    Finset.sum_le_sum_of_subset hsub
  have hNB : ∀ S ∈ s.biUnion
      (fun i : Fin L => (Finset.univ.image (A i)).filter (fun S => S.card < k)),
      S ⊆ U ∧ S.card < k := by
    intro S hS
    rw [Finset.mem_biUnion] at hS
    obtain ⟨i, _, hi⟩ := hS
    rw [Finset.mem_filter] at hi
    obtain ⟨himg, hltS⟩ := hi
    rw [Finset.mem_image] at himg
    obtain ⟨j, _, hAj⟩ := himg
    constructor
    · rw [← hAj]
      exact hG1 i j
    · exact hltS
  have h5 := baranyai_fiberSum hG hlt _ hNB
  have hle : (n - U.card) * s.card ≤ (n - U.card) *
      (∑ S ∈ s.biUnion
        (fun i : Fin L => (Finset.univ.image (A i)).filter (fun S => S.card < k)),
        (n - U.card - 1).choose (k - S.card - 1)) := by
    rw [h1, h23, h5]
    exact h4
  exact Nat.le_of_mul_le_mul_left hle hd_pos

private theorem baranyai_total {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a U A) (Hak : a * k = n) (hlt : U.card < n) :
    ∑ S ∈ U.powerset.filter (fun S => S.card < k),
      (n - U.card - 1).choose (k - S.card - 1) = L := by
  have hG1 : ∀ (i : Fin L) (j : Fin a), A i j ⊆ U := by
    obtain ⟨h1, _, _, _, _⟩ := hG
    exact h1
  have hd_pos : 0 < n - U.card := Nat.sub_pos_of_lt hlt
  have hNCol : ∀ S ∈ U.powerset.filter (fun S => S.card < k),
      S ⊆ U ∧ S.card < k := by
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨hpow, hltS⟩ := hS
    constructor
    · exact Finset.mem_powerset.mp hpow
    · exact hltS
  have hfib := baranyai_fiberSum hG hlt
    (U.powerset.filter (fun S => S.card < k)) hNCol
  have hdrop : (∑ p ∈ Finset.univ.filter
      (fun p : Fin L × Fin a => A p.1 p.2 ∈ U.powerset.filter
        (fun S => S.card < k)), (k - (A p.1 p.2).card)) =
      ∑ p ∈ (Finset.univ : Finset (Fin L × Fin a)), (k - (A p.1 p.2).card) := by
    apply Finset.sum_filter_of_ne
    intro p _ hne
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_powerset]
      exact hG1 p.1 p.2
    · omega
  have hprod : (∑ p ∈ (Finset.univ : Finset (Fin L × Fin a)),
      (k - (A p.1 p.2).card)) =
      ∑ i : Fin L, ∑ j : Fin a, (k - (A i j).card) :=
    Fintype.sum_prod_type _
  have hrowsum : (∑ i ∈ (Finset.univ : Finset (Fin L)),
      ∑ j : Fin a, (k - (A i j).card)) = L * (n - U.card) := by
    have hcongr : (∑ i ∈ (Finset.univ : Finset (Fin L)),
        ∑ j : Fin a, (k - (A i j).card)) =
        ∑ _i ∈ (Finset.univ : Finset (Fin L)), (n - U.card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact baranyai_rowSum hG Hak i
    rw [hcongr]
    have h2 : ∑ _i ∈ (Finset.univ : Finset (Fin L)), (n - U.card) =
        (Finset.univ : Finset (Fin L)).card * (n - U.card) :=
      Finset.sum_const_nat (fun i _ => rfl)
    rw [h2, Finset.card_fin]
  have htot : (n - U.card) *
      (∑ S ∈ U.powerset.filter (fun S => S.card < k),
        (n - U.card - 1).choose (k - S.card - 1)) =
      L * (n - U.card) := by
    rw [hfib, hdrop, hprod]
    exact hrowsum
  have htot2 : (n - U.card) *
      (∑ S ∈ U.powerset.filter (fun S => S.card < k),
        (n - U.card - 1).choose (k - S.card - 1)) =
      (n - U.card) * L := by
    rw [htot, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hd_pos htot2

private theorem baranyai_card_slots (n : ℕ) (c : Finset (Fin n) → ℕ)
    (N : Finset (Finset (Fin n))) :
    (N.biUnion (fun S => ({S} : Finset (Finset (Fin n))) ×ˢ Finset.range (c S))).card =
      ∑ S ∈ N, c S := by
  have hdisj : (↑N : Set (Finset (Fin n))).PairwiseDisjoint
      (fun S => ({S} : Finset (Finset (Fin n))) ×ˢ Finset.range (c S)) := by
    intro S _ S' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_product]
    exact Or.inl (Finset.disjoint_singleton.mpr hne)
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul]

private theorem baranyai_choice {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a U A) (Hak : a * k = n) (hlt : U.card < n) :
    ∃ J : Fin L → Fin a, (∀ i, (A i (J i)).card < k) ∧
      ∀ S ⊆ U, S.card < k →
        (Finset.univ.filter (fun i : Fin L => A i (J i) = S)).card =
          (n - U.card - 1).choose (k - S.card - 1) := by
  have hG1 : ∀ (i : Fin L) (j : Fin a), A i j ⊆ U := by
    obtain ⟨h1, _, _, _, _⟩ := hG
    exact h1
  have hHallCond : ∀ s : Finset (Fin L), s.card ≤ (s.biUnion (fun i : Fin L =>
      ((Finset.univ.image (A i)).filter (fun S => S.card < k)).biUnion
        (fun S => ({S} : Finset (Finset (Fin n))) ×ˢ
          Finset.range ((n - U.card - 1).choose (k - S.card - 1))))).card := by
    intro s
    rw [← Finset.biUnion_biUnion, baranyai_card_slots]
    exact baranyai_hall_condition hG Hak hlt s
  obtain ⟨f, hfinj, hfm⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp hHallCond
  have hcomb : ∀ i : Fin L, ∃ j : Fin a,
      A i j = (f i).1 ∧ ((f i).1).card < k := by
    intro i
    have hmem := hfm i
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨S, hSAdj, hSslot⟩ := hmem
    rw [Finset.mem_product] at hSslot
    obtain ⟨h1, h2⟩ := hSslot
    rw [Finset.mem_singleton] at h1
    rw [Finset.mem_range] at h2
    rw [Finset.mem_filter] at hSAdj
    obtain ⟨himg, hltS⟩ := hSAdj
    rw [Finset.mem_image] at himg
    obtain ⟨j, _, hAj⟩ := himg
    refine ⟨j, ?_, ?_⟩
    · rw [hAj, ← h1]
    · rw [h1]
      exact hltS
  choose J hJ using hcomb
  have hfst : ∀ i, A i (J i) = (f i).1 := fun i => (hJ i).1
  have hltf : ∀ i, ((f i).1).card < k := fun i => (hJ i).2
  have hslot : ∀ i, (f i).2 <
      (n - U.card - 1).choose (k - (f i).1.card - 1) := by
    intro i
    have hmem := hfm i
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨S, _, hSslot⟩ := hmem
    rw [Finset.mem_product] at hSslot
    obtain ⟨h1, h2⟩ := hSslot
    rw [Finset.mem_singleton] at h1
    rw [Finset.mem_range] at h2
    rw [h1]
    exact h2
  have J1 : ∀ i, (A i (J i)).card < k := by
    intro i
    rw [hfst i]
    exact hltf i
  have hle_S : ∀ S : Finset (Fin n), S ⊆ U → S.card < k →
      (Finset.univ.filter (fun i : Fin L => A i (J i) = S)).card ≤
        (n - U.card - 1).choose (k - S.card - 1) := by
    intro S hSU hSk
    have hcard : (Finset.range
        ((n - U.card - 1).choose (k - S.card - 1))).card =
        (n - U.card - 1).choose (k - S.card - 1) :=
      Finset.card_range _
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun i : Fin L => (f i).2)
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      obtain ⟨_, hAi⟩ := hi
      rw [Finset.mem_coe, Finset.mem_range]
      have hSi : (f i).1 = S := by
        rw [← hfst i]
        exact hAi
      rw [← hSi]
      exact hslot i
    · intro i hi i' hi' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hi hi'
      obtain ⟨_, hAi⟩ := hi
      obtain ⟨_, hAi'⟩ := hi'
      have h1 : (f i).1 = S := by
        rw [← hfst i]
        exact hAi
      have h2 : (f i').1 = S := by
        rw [← hfst i']
        exact hAi'
      have hfst_eq : (f i).1 = (f i').1 := by
        rw [h1, h2]
      have hfull : f i = f i' := Prod.ext hfst_eq heq
      exact hfinj hfull
  have hCol : ∀ i ∈ (Finset.univ : Finset (Fin L)),
      (fun i : Fin L => A i (J i)) i ∈
        U.powerset.filter (fun S => S.card < k) := by
    intro i _
    change A i (J i) ∈ U.powerset.filter (fun S => S.card < k)
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_powerset.mpr (hG1 i (J i))
    · exact J1 i
  have hfib2 := Finset.card_eq_sum_card_fiberwise hCol
  rw [Finset.card_fin] at hfib2
  have htot := baranyai_total hG Hak hlt
  have hle_all : ∀ S ∈ U.powerset.filter (fun S => S.card < k),
      (Finset.univ.filter (fun i : Fin L => A i (J i) = S)).card ≤
        (n - U.card - 1).choose (k - S.card - 1) := by
    intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨hpow, hltS⟩ := hS
    exact hle_S S (Finset.mem_powerset.mp hpow) hltS
  have hsum_eq : (∑ S ∈ U.powerset.filter (fun S => S.card < k),
      (Finset.univ.filter (fun i : Fin L => A i (J i) = S)).card) =
      ∑ S ∈ U.powerset.filter (fun S => S.card < k),
        (n - U.card - 1).choose (k - S.card - 1) := by
    rw [← hfib2, htot]
  have hpt := (Finset.sum_eq_sum_iff_of_le hle_all).mp hsum_eq
  refine ⟨J, J1, ?_⟩
  intro S hSU hSk
  have hSCol : S ∈ U.powerset.filter (fun S => S.card < k) := by
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_powerset.mpr hSU
    · exact hSk
  exact hpt S hSCol

private theorem baranyai_extend_apply_ne {n L a : ℕ}
    {A : Fin L → Fin a → Finset (Fin n)} {J : Fin L → Fin a} {x : Fin n}
    {i : Fin L} {j : Fin a} (hne : j ≠ J i) :
    baranyai_extend A J x i j = A i j := by
  unfold baranyai_extend
  simp [hne]

private theorem baranyai_extend_apply_eq {n L a : ℕ}
    {A : Fin L → Fin a → Finset (Fin n)} {J : Fin L → Fin a} {x : Fin n}
    (i : Fin L) :
    baranyai_extend A J x i (J i) = insert x (A i (J i)) := by
  unfold baranyai_extend
  simp

private theorem baranyai_extend_struct {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)} {x : Fin n} {J : Fin L → Fin a}
    (hG : baranyai_Good n k L a U A) (hx : x ∉ U)
    (J1 : ∀ i, (A i (J i)).card < k) :
    (∀ i j, baranyai_extend A J x i j ⊆ insert x U) ∧
    (∀ i j j', j ≠ j' → Disjoint (baranyai_extend A J x i j)
      (baranyai_extend A J x i j')) ∧
    (∀ i, Finset.univ.biUnion (baranyai_extend A J x i) = insert x U) ∧
    (∀ i j, (baranyai_extend A J x i j).card ≤ k) := by
  obtain ⟨hG1, hG2, hG3, hG4, _⟩ := hG
  have hsub : ∀ i j, baranyai_extend A J x i j ⊆ insert x U := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      rw [baranyai_extend_apply_eq]
      exact Finset.insert_subset_insert x (hG1 i _)
    · rw [baranyai_extend_apply_ne hj]
      exact Finset.Subset.trans (hG1 i j) (Finset.subset_insert x U)
  have hdisj : ∀ i j j', j ≠ j' → Disjoint (baranyai_extend A J x i j)
      (baranyai_extend A J x i j') := by
    intro i j j' hne
    by_cases hj : j = J i <;> by_cases hj' : j' = J i
    · subst hj
      subst hj'
      exact absurd rfl hne
    · subst hj
      rw [baranyai_extend_apply_eq, baranyai_extend_apply_ne hj']
      have hxj' : x ∉ A i j' := fun hmem => hx (hG1 i j' hmem)
      exact Finset.disjoint_insert_left.mpr ⟨hxj', hG2 i _ _ hne⟩
    · subst hj'
      rw [baranyai_extend_apply_ne hj, baranyai_extend_apply_eq]
      have hxj : x ∉ A i j := fun hmem => hx (hG1 i j hmem)
      exact Finset.disjoint_insert_right.mpr ⟨hxj, hG2 i _ _ hne⟩
    · rw [baranyai_extend_apply_ne hj, baranyai_extend_apply_ne hj']
      exact hG2 i _ _ hne
  have hbi : ∀ i, Finset.univ.biUnion (baranyai_extend A J x i) =
      insert x U := by
    intro i
    ext y
    rw [Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro ⟨j, _, hj⟩
      have hmem := hsub i j hj
      rw [Finset.mem_insert] at hmem
      exact hmem
    · rintro (h | hyU)
      · rw [h]
        refine ⟨J i, Finset.mem_univ _, ?_⟩
        rw [baranyai_extend_apply_eq]
        exact Finset.mem_insert_self x _
      · rw [← hG3 i] at hyU
        rw [Finset.mem_biUnion] at hyU
        obtain ⟨j, hjU, hyj⟩ := hyU
        refine ⟨j, hjU, ?_⟩
        by_cases hj : j = J i
        · subst hj
          rw [baranyai_extend_apply_eq]
          exact Finset.mem_insert_of_mem hyj
        · rw [baranyai_extend_apply_ne hj]
          exact hyj
  have hcard : ∀ i j, (baranyai_extend A J x i j).card ≤ k := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      rw [baranyai_extend_apply_eq]
      calc (insert x (A i (J i))).card ≤ (A i (J i)).card + 1 :=
            Finset.card_insert_le x _
        _ ≤ k := by
            have hlt := J1 i
            omega
    · rw [baranyai_extend_apply_ne hj]
      exact hG4 i j
  exact ⟨hsub, hdisj, hbi, hcard⟩

private theorem baranyai_extend_cnt_mem {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)} {x : Fin n} {J : Fin L → Fin a}
    (hG : baranyai_Good n k L a U A) (_hlt : U.card < n) (hx : x ∉ U)
    (_J1 : ∀ i, (A i (J i)).card < k)
    (J2 : ∀ S ⊆ U, S.card < k →
      (Finset.univ.filter (fun i : Fin L => A i (J i) = S)).card =
        (n - U.card - 1).choose (k - S.card - 1))
    (T : Finset (Fin n)) (hTU : T ⊆ insert x U) (hxT : x ∈ T) (hkT : T.card ≤ k) :
    baranyai_cnt (baranyai_extend A J x) T =
      (n - (insert x U).card).choose (k - T.card) := by
  have hG1 : ∀ (i : Fin L) (j : Fin a), A i j ⊆ U := by
    obtain ⟨h1, _, _, _, _⟩ := hG
    exact h1
  have hSU : T.erase x ⊆ U := Finset.subset_insert_iff.mp hTU
  have hcardS : (T.erase x).card = T.card - 1 := Finset.card_erase_of_mem hxT
  have hposT : 0 < T.card := Finset.card_pos.mpr ⟨x, hxT⟩
  have hSk : (T.erase x).card < k := by omega
  have hset : Finset.univ.filter
      (fun p : Fin L × Fin a => baranyai_extend A J x p.1 p.2 = T) =
      (Finset.univ.filter (fun i : Fin L => A i (J i) = T.erase x)).image
        (fun i => (i, J i)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hAT
      by_cases hj : j = J i
      · subst hj
        rw [baranyai_extend_apply_eq] at hAT
        have hmem : x ∉ A i (J i) := fun hmem => hx (hG1 i (J i) hmem)
        have herase : (insert x (A i (J i))).erase x = A i (J i) :=
          Finset.erase_insert hmem
        rw [hAT] at herase
        refine ⟨i, herase.symm, rfl⟩
      · rw [baranyai_extend_apply_ne hj] at hAT
        have hxA : x ∉ A i j := fun hmem => hx (hG1 i j hmem)
        rw [hAT] at hxA
        exact (hxA hxT).elim
    · rintro ⟨i', hi', hpair⟩
      have hfst : i' = i := congrArg Prod.fst hpair
      have hsnd : J i' = j := congrArg Prod.snd hpair
      subst hfst
      subst hsnd
      rw [baranyai_extend_apply_eq]
      rw [hi']
      exact Finset.insert_erase hxT
  have hinj : Function.Injective (fun i : Fin L => (i, J i)) := by
    intro i i' h
    exact congrArg Prod.fst h
  have hcardImg := Finset.card_image_of_injective
    (Finset.univ.filter (fun i : Fin L => A i (J i) = T.erase x))
    hinj
  have hJ2 := J2 _ hSU hSk
  have hcnt : baranyai_cnt (baranyai_extend A J x) T =
      (n - U.card - 1).choose (k - (T.erase x).card - 1) := by
    unfold baranyai_cnt
    rw [hset, hcardImg, hJ2]
  have hcardU : (insert x U).card = U.card + 1 := Finset.card_insert_of_notMem hx
  have harg1 : n - (insert x U).card = n - U.card - 1 := by
    rw [hcardU, Nat.sub_sub]
  have harg2 : k - T.card = k - (T.erase x).card - 1 := by omega
  rw [hcnt, harg1, harg2]

private theorem baranyai_extend_cnt_not_mem {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)} {x : Fin n} {J : Fin L → Fin a}
    (hG : baranyai_Good n k L a U A) (hlt : U.card < n) (hx : x ∉ U)
    (J1 : ∀ i, (A i (J i)).card < k)
    (J2 : ∀ S ⊆ U, S.card < k →
      (Finset.univ.filter (fun i : Fin L => A i (J i) = S)).card =
        (n - U.card - 1).choose (k - S.card - 1))
    (T : Finset (Fin n)) (hTU : T ⊆ insert x U) (hxT : x ∉ T) (hkT : T.card ≤ k) :
    baranyai_cnt (baranyai_extend A J x) T =
      (n - (insert x U).card).choose (k - T.card) := by
  have hG1 : ∀ (i : Fin L) (j : Fin a), A i j ⊆ U := by
    obtain ⟨h1, _, _, _, _⟩ := hG
    exact h1
  have hG5 : ∀ S ⊆ U, S.card ≤ k →
      baranyai_cnt A S = (n - U.card).choose (k - S.card) := by
    obtain ⟨_, _, _, _, h5⟩ := hG
    exact h5
  have hTU' : T ⊆ U := by
    have h1 : T.erase x ⊆ U := Finset.subset_insert_iff.mp hTU
    rw [Finset.erase_eq_of_notMem hxT] at h1
    exact h1
  have hF : (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = T)).card =
      (n - U.card).choose (k - T.card) := by
    have h := hG5 T hTU' hkT
    unfold baranyai_cnt at h
    exact h
  have hFa : (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = T)).filter
      (fun p => p.2 = J p.1) =
      (Finset.univ.filter (fun i : Fin L => A i (J i) = T)).image
        (fun i => (i, J i)) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hAT, hj⟩
      have hAT' : A i (J i) = T := by
        rw [← hj]
        exact hAT
      exact ⟨i, hAT', by rw [hj]⟩
    · rintro ⟨i', hi', hpair⟩
      have hfst : i' = i := congrArg Prod.fst hpair
      have hsnd : J i' = j := congrArg Prod.snd hpair
      subst hfst
      subst hsnd
      exact ⟨hi', rfl⟩
  have hFb : (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = T)).filter
      (fun p => ¬ p.2 = J p.1) =
      Finset.univ.filter
        (fun p : Fin L × Fin a => baranyai_extend A J x p.1 p.2 = T) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hAT, hne⟩
      rw [baranyai_extend_apply_ne hne]
      exact hAT
    · intro hAT
      by_cases hj : j = J i
      · subst hj
        rw [baranyai_extend_apply_eq] at hAT
        have hmem : x ∈ T := hAT ▸ Finset.mem_insert_self x _
        exact (hxT hmem).elim
      · rw [baranyai_extend_apply_ne hj] at hAT
        exact ⟨hAT, hj⟩
  have hinj : Function.Injective (fun i : Fin L => (i, J i)) := by
    intro i i' h
    exact congrArg Prod.fst h
  have hcardImg := Finset.card_image_of_injective
    (Finset.univ.filter (fun i : Fin L => A i (J i) = T)) hinj
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = T))
    (fun p : Fin L × Fin a => p.2 = J p.1)
  rw [hFa, hFb, hcardImg, hF] at hsplit
  have hcardU : (insert x U).card = U.card + 1 := Finset.card_insert_of_notMem hx
  have harg1 : n - (insert x U).card = n - U.card - 1 := by
    rw [hcardU, Nat.sub_sub]
  by_cases hltT : T.card < k
  · have hd_pos : 0 < n - U.card := Nat.sub_pos_of_lt hlt
    have hr : 0 < k - T.card := by omega
    have hpascal := baranyai_choose_pascal (n - U.card) (k - T.card) hd_pos hr
    have hDT := J2 T hTU' hltT
    rw [hDT] at hsplit
    rw [hpascal] at hsplit
    have hC : (Finset.univ.filter
        (fun p : Fin L × Fin a => baranyai_extend A J x p.1 p.2 = T)).card =
        (n - U.card - 1).choose (k - T.card) :=
      Nat.add_left_cancel hsplit
    unfold baranyai_cnt
    rw [harg1]
    exact hC
  · have hTeq : T.card = k := by omega
    have hDT0 : Finset.univ.filter (fun i : Fin L => A i (J i) = T) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _ hcon
      have hltJ := J1 i
      rw [hcon, hTeq] at hltJ
      exact absurd hltJ (lt_irrefl k)
    have hD0 : (Finset.univ.filter (fun i : Fin L => A i (J i) = T)).card = 0 := by
      rw [hDT0, Finset.card_empty]
    rw [hD0] at hsplit
    have hCk : (n - U.card).choose (k - T.card) = 1 := by
      rw [hTeq, Nat.sub_self]
      exact Nat.choose_zero_right _
    have hCt : (n - (insert x U).card).choose (k - T.card) = 1 := by
      rw [hTeq, Nat.sub_self]
      exact Nat.choose_zero_right _
    rw [hCk, Nat.zero_add] at hsplit
    unfold baranyai_cnt
    rw [hCt]
    exact hsplit

private theorem baranyai_step {n k L a : ℕ} {U : Finset (Fin n)}
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a U A) (Hak : a * k = n) {x : Fin n} (hx : x ∉ U) :
    ∃ A', baranyai_Good n k L a (insert x U) A' := by
  have hlt : U.card < n := by
    have h1 : (insert x U).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem hx, Fintype.card_fin] at h1
    omega
  obtain ⟨J, J1, J2⟩ := baranyai_choice hG Hak hlt
  obtain ⟨h1, h2, h3, h4⟩ := baranyai_extend_struct hG hx J1
  refine ⟨baranyai_extend A J x, h1, h2, h3, h4, ?_⟩
  intro T hTU hkT
  by_cases hxT : x ∈ T
  · exact baranyai_extend_cnt_mem hG hlt hx J1 J2 T hTU hxT hkT
  · exact baranyai_extend_cnt_not_mem hG hlt hx J1 J2 T hTU hxT hkT

private theorem baranyai_good_univ (n k L a : ℕ) (HLa : L * a = n.choose k)
    (Hak : a * k = n) :
    ∃ A : Fin L → Fin a → Finset (Fin n), baranyai_Good n k L a Finset.univ A := by
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?_ ?_
  · exact ⟨_, baranyai_good_empty n k L a HLa⟩
  · intro a s hx ih
    obtain ⟨A, hA⟩ := ih
    obtain ⟨A', hA'⟩ := baranyai_step hA Hak hx
    exact ⟨A', hA'⟩

private theorem baranyai_extract (n k L a : ℕ)
    {A : Fin L → Fin a → Finset (Fin n)}
    (hG : baranyai_Good n k L a Finset.univ A) :
    ∃ P : Finset (Finset (Finset (Fin n))),
      P.biUnion id = Finset.powersetCard k Finset.univ ∧
        (∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂) ∧
        ∀ M ∈ P, M.biUnion id = Finset.univ ∧
          ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  obtain ⟨_, hG2, hG3, hG4, hG5⟩ := hG
  have hcardU : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
  have E1 : ∀ i j, (A i j).card = k := by
    intro i j
    by_cases hlt : (A i j).card < k
    · have hsub : A i j ⊆ Finset.univ := Finset.subset_univ _
      have hle : (A i j).card ≤ k := hG4 i j
      have hcnt := hG5 _ hsub hle
      rw [hcardU, Nat.sub_self] at hcnt
      have hpos : 0 < k - (A i j).card := by omega
      have hzero : Nat.choose 0 (k - (A i j).card) = 0 :=
        Nat.choose_eq_zero_of_lt hpos
      rw [hzero] at hcnt
      have hmem : (i, j) ∈ Finset.univ.filter
          (fun p : Fin L × Fin a => A p.1 p.2 = A i j) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, rfl⟩
      have hposcard : 0 < (Finset.univ.filter
          (fun p : Fin L × Fin a => A p.1 p.2 = A i j)).card :=
        Finset.card_pos.mpr ⟨(i, j), hmem⟩
      unfold baranyai_cnt at hcnt
      rw [hcnt] at hposcard
      omega
    · have hle := hG4 i j
      omega
  have E2 : ∀ S : Finset (Fin n), S.card = k → baranyai_cnt A S = 1 := by
    intro S hSk
    have hsub : S ⊆ Finset.univ := Finset.subset_univ _
    have hle : S.card ≤ k := by omega
    have hcnt := hG5 S hsub hle
    rw [hcardU, Nat.sub_self, hSk, Nat.sub_self, Nat.choose_zero_right] at hcnt
    exact hcnt
  have E2ex : ∀ S : Finset (Fin n), S.card = k →
      ∃ p : Fin L × Fin a, A p.1 p.2 = S := by
    intro S hSk
    have h1 := E2 S hSk
    unfold baranyai_cnt at h1
    have hpos : 0 < (Finset.univ.filter
        (fun p : Fin L × Fin a => A p.1 p.2 = S)).card := by
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hp
    exact ⟨p, hp.2⟩
  have E2uniq : ∀ p q : Fin L × Fin a, A p.1 p.2 = A q.1 q.2 →
      (A p.1 p.2).card = k → p = q := by
    intro p q hSS hk
    have hcnt := E2 _ hk
    unfold baranyai_cnt at hcnt
    have hp : p ∈ Finset.univ.filter
        (fun r : Fin L × Fin a => A r.1 r.2 = A p.1 p.2) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    have hq : q ∈ Finset.univ.filter
        (fun r : Fin L × Fin a => A r.1 r.2 = A p.1 p.2) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hSS.symm⟩
    have hle : (Finset.univ.filter
        (fun r : Fin L × Fin a => A r.1 r.2 = A p.1 p.2)).card ≤ 1 := by
      rw [hcnt]
    exact Finset.card_le_one.mp hle p hp q hq
  refine ⟨Finset.univ.image (fun i => Finset.univ.image (A i)), ?_, ?_, ?_⟩
  · ext S
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨M, hMP, hSM⟩
      rw [Finset.mem_image] at hMP
      obtain ⟨i, _, hMi⟩ := hMP
      have hSM' : S ∈ M := hSM
      rw [← hMi] at hSM'
      rw [Finset.mem_image] at hSM'
      obtain ⟨j, _, hSj⟩ := hSM'
      rw [Finset.mem_powersetCard_univ]
      rw [← hSj]
      exact E1 i j
    · intro hS
      rw [Finset.mem_powersetCard_univ] at hS
      obtain ⟨⟨i, j⟩, hp⟩ := E2ex S hS
      exact ⟨Finset.univ.image (A i),
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hp⟩⟩
  · intro M₁ h₁ M₂ h₂ hne
    rw [Finset.mem_image] at h₁ h₂
    obtain ⟨i, _, hi⟩ := h₁
    obtain ⟨i', _, hi'⟩ := h₂
    rw [Finset.disjoint_left]
    intro S hS1 hS2
    rw [← hi] at hS1
    rw [← hi'] at hS2
    rw [Finset.mem_image] at hS1 hS2
    obtain ⟨j, _, hj⟩ := hS1
    obtain ⟨j', _, hj'⟩ := hS2
    have hSS : A i j = A i' j' := hj.trans hj'.symm
    have hpair := E2uniq (i, j) (i', j') hSS (E1 i j)
    have hi_eq : i = i' := congrArg Prod.fst hpair
    apply hne
    rw [← hi, ← hi', hi_eq]
  · intro M hM
    rw [Finset.mem_image] at hM
    obtain ⟨i, _, hi⟩ := hM
    constructor
    · have hunion : (Finset.univ.image (A i)).biUnion id = Finset.univ := by
        rw [Finset.image_biUnion]
        simp only [id]
        exact hG3 i
      rw [← hi]
      exact hunion
    · intro e₁ he₁ e₂ he₂ hne
      rw [← hi] at he₁ he₂
      rw [Finset.mem_image] at he₁ he₂
      obtain ⟨j, _, hj⟩ := he₁
      obtain ⟨j', _, hj'⟩ := he₂
      have hjne : j ≠ j' := by
        intro hcon
        apply hne
        rw [← hj, ← hj', hcon]
      rw [← hj, ← hj']
      exact hG2 i j j' hjne

/-- **Baranyai's theorem.** Let $n$ and $h$ be natural numbers with $h \mid n$, and let
$V = \{0, \dots, n-1\}$. The $h$-element subsets of $V$, the edges of the complete
$h$-uniform hypergraph on $V$, can be partitioned into perfect matchings: there is a finite
family $\mathcal{P}$ of sets of subsets of $V$ such that the union of the members of
$\mathcal{P}$ is exactly the set of $h$-element subsets of $V$, distinct members of
$\mathcal{P}$ are disjoint, and each member of $\mathcal{P}$ consists of pairwise disjoint sets
whose union is $V$.

Proves `Wanted` entry `baranyai_theorem`.

Source: statement `baranyai-s1` from https://en.wikipedia.org/wiki/Baranyai%27s_theorem.
-/
theorem baranyai_theorem : ∀ (n h : ℕ), h ∣ n →
    ∃ P : Finset (Finset (Finset (Fin n))),
      P.biUnion id = Finset.powersetCard h Finset.univ ∧
        (∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂) ∧
        ∀ M ∈ P, M.biUnion id = Finset.univ ∧
          ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  intro n h hd
  obtain ⟨L, a, Hak, HLa⟩ := baranyai_exists_dims n h hd
  obtain ⟨A, hA⟩ := baranyai_good_univ n h L a HLa Hak
  exact baranyai_extract n h L a hA

end
end MetaMathlibExt
