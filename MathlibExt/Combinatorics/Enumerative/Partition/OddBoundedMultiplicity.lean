/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

private theorem avoid_card_eq_of_inter_eq
    {α : Type*}
    (A B : Finset α) (s : Finset ℕ)
    (EA EB : ℕ → α → Prop) [∀ j, DecidablePred (EA j)] [∀ j, DecidablePred (EB j)]
    (h : ∀ t ∈ s.powerset, (A.filter fun a => ∀ j ∈ t, EA j a).card =
      (B.filter fun a => ∀ j ∈ t, EB j a).card) :
    (A.filter fun a => ∀ j ∈ s, ¬ EA j a).card =
      (B.filter fun a => ∀ j ∈ s, ¬ EB j a).card := by
  classical
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    have h0 := h ∅ (by simp)
    simpa using h0
  | insert a s _ ih =>
    have hsub : ∀ t ∈ s.powerset, (A.filter fun x => ∀ j ∈ t, EA j x).card =
        (B.filter fun x => ∀ j ∈ t, EB j x).card := by
      intro t ht
      exact h t (Finset.mem_powerset.mpr
        (Finset.Subset.trans (Finset.mem_powerset.mp ht) (Finset.subset_insert a s)))
    have e1 := ih A B hsub
    have insA : ∀ (t : Finset ℕ), (A.filter fun x => ∀ j ∈ insert a t, EA j x) =
        ((A.filter (EA a ·)).filter fun x => ∀ j ∈ t, EA j x) := by
      intro t
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨⟨hx.1, hx.2 a (Finset.mem_insert_self a t)⟩,
          fun j hj => hx.2 j (Finset.mem_insert_of_mem hj)⟩
      · intro hx
        exact ⟨hx.1.1, fun j hj => by
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hx.1.2
          · exact hx.2 j hj⟩
    have insB : ∀ (t : Finset ℕ), (B.filter fun x => ∀ j ∈ insert a t, EB j x) =
        ((B.filter (EB a ·)).filter fun x => ∀ j ∈ t, EB j x) := by
      intro t
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨⟨hx.1, hx.2 a (Finset.mem_insert_self a t)⟩,
          fun j hj => hx.2 j (Finset.mem_insert_of_mem hj)⟩
      · intro hx
        exact ⟨hx.1.1, fun j hj => by
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hx.1.2
          · exact hx.2 j hj⟩
    have hsub' : ∀ t ∈ s.powerset,
        (((A.filter (EA a ·)).filter fun x => ∀ j ∈ t, EA j x)).card =
        (((B.filter (EB a ·)).filter fun x => ∀ j ∈ t, EB j x)).card := by
      intro t ht
      rw [← insA t, ← insB t]
      exact h (insert a t) (Finset.mem_powerset.mpr
        (Finset.insert_subset_insert a (Finset.mem_powerset.mp ht)))
    have e2 := ih (A.filter (EA a ·)) (B.filter (EB a ·)) hsub'
    have rshA : ((A.filter (EA a ·)).filter fun x => ∀ j ∈ s, ¬ EA j x) =
        ((A.filter fun x => ∀ j ∈ s, ¬ EA j x).filter (EA a ·)) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hxA, hxa⟩, hxav⟩
        exact ⟨⟨hxA, hxav⟩, hxa⟩
      · rintro ⟨⟨hxA, hxav⟩, hxa⟩
        exact ⟨⟨hxA, hxa⟩, hxav⟩
    have rshB : ((B.filter (EB a ·)).filter fun x => ∀ j ∈ s, ¬ EB j x) =
        ((B.filter fun x => ∀ j ∈ s, ¬ EB j x).filter (EB a ·)) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hxB, hxb⟩, hxbv⟩
        exact ⟨⟨hxB, hxbv⟩, hxb⟩
      · rintro ⟨⟨hxB, hxbv⟩, hxb⟩
        exact ⟨⟨hxB, hxb⟩, hxbv⟩
    rw [rshA, rshB] at e2
    have splitA : (A.filter fun x => ∀ j ∈ insert a s, ¬ EA j x) =
        ((A.filter fun x => ∀ j ∈ s, ¬ EA j x).filter fun x => ¬ EA a x) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨⟨hx.1, fun j hj => hx.2 j (Finset.mem_insert_of_mem hj)⟩,
          hx.2 a (Finset.mem_insert_self a s)⟩
      · rintro ⟨⟨hxA, hxav⟩, hxa⟩
        exact ⟨hxA, fun j hj => by
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hxa
          · exact hxav j hj⟩
    have splitB : (B.filter fun x => ∀ j ∈ insert a s, ¬ EB j x) =
        ((B.filter fun x => ∀ j ∈ s, ¬ EB j x).filter fun x => ¬ EB a x) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨⟨hx.1, fun j hj => hx.2 j (Finset.mem_insert_of_mem hj)⟩,
          hx.2 a (Finset.mem_insert_self a s)⟩
      · rintro ⟨⟨hxA, hxav⟩, hxa⟩
        exact ⟨hxA, fun j hj => by
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hxa
          · exact hxav j hj⟩
    rw [splitA, splitB]
    have cA := Finset.card_filter_add_card_filter_not
      (s := (A.filter fun x => ∀ j ∈ s, ¬ EA j x)) (EA a ·)
    have cB := Finset.card_filter_add_card_filter_not
      (s := (B.filter fun x => ∀ j ∈ s, ¬ EB j x)) (EB a ·)
    omega

private theorem count_sum_replicate_four (t : Finset ℕ) (a : ℕ) :
    (∑ j ∈ t, Multiset.replicate 4 (2 * j + 1)).count a =
      ∑ j ∈ t, (if 2 * j + 1 = a then 4 else 0) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert j s hjs ih =>
    simp only [Finset.sum_insert hjs, Multiset.count_add, ih, Multiset.count_replicate]

private theorem count_sum_pair (t : Finset ℕ) (a : ℕ) :
    (∑ j ∈ t, ((4 * j + 1) ::ₘ ({(4 * j + 3)} : Multiset ℕ))).count a =
      ∑ j ∈ t, ((if a = 4 * j + 1 then 1 else 0) + (if a = 4 * j + 3 then 1 else 0)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert j s hjs ih =>
    simp only [Finset.sum_insert hjs, Multiset.count_add, ih, Multiset.count_cons,
      Multiset.count_singleton]
    ring

private theorem L_le_iff (M : Multiset ℕ) (t : Finset ℕ) :
    (∑ j ∈ t, Multiset.replicate 4 (2 * j + 1)) ≤ M ↔
      ∀ j ∈ t, 4 ≤ M.count (2 * j + 1) := by
  rw [Multiset.le_iff_count]
  constructor
  · intro h j hj
    have hle : Multiset.replicate 4 (2 * j + 1) ≤
        ∑ k ∈ t, Multiset.replicate 4 (2 * k + 1) :=
      Finset.single_le_sum (s := t) (f := fun k => Multiset.replicate 4 (2 * k + 1))
        (fun k _ => zero_le) hj
    have hcc := le_trans (Multiset.le_iff_count.mp hle (2 * j + 1)) (h (2 * j + 1))
    rw [Multiset.count_replicate] at hcc
    simpa using hcc
  · intro h a
    rw [count_sum_replicate_four]
    by_cases hex : ∃ j ∈ t, 2 * j + 1 = a
    · obtain ⟨j0, hj0t, hj0e⟩ := hex
      have hzero : ∀ j ∈ t, j ≠ j0 → (if 2 * j + 1 = a then 4 else 0) = 0 := by
        intro j hjt hne
        have hne' : ¬ (2 * j + 1 = a) := fun hcon => hne (by omega)
        simp [hne']
      rw [Finset.sum_eq_single j0 hzero (fun h => absurd hj0t h)]
      have h4 : (4 : ℕ) ≤ M.count a := hj0e ▸ h j0 hj0t
      simpa [hj0e] using h4
    · have hex' : ∀ j ∈ t, 2 * j + 1 ≠ a := fun j hj he => hex ⟨j, hj, he⟩
      rw [Finset.sum_eq_zero (fun j hj => by simp [hex' j hj])]
      exact Nat.zero_le _

private theorem R_le_iff (M : Multiset ℕ) (t : Finset ℕ) :
    (∑ j ∈ t, ((4 * j + 1) ::ₘ ({(4 * j + 3)} : Multiset ℕ))) ≤ M ↔
      ∀ j ∈ t, (4 * j + 1 ∈ M ∧ 4 * j + 3 ∈ M) := by
  constructor
  · intro h j hj
    have hle : ((4 * j + 1) ::ₘ ({(4 * j + 3)} : Multiset ℕ)) ≤
        ∑ k ∈ t, ((4 * k + 1) ::ₘ ({(4 * k + 3)} : Multiset ℕ)) :=
      Finset.single_le_sum (s := t)
        (f := fun k => ((4 * k + 1) ::ₘ ({(4 * k + 3)} : Multiset ℕ)))
        (fun k _ => zero_le) hj
    have hleM := le_trans hle h
    constructor
    · exact Multiset.singleton_le.mp (le_trans
        (Multiset.singleton_le.mpr (Multiset.mem_cons_self _ _)) hleM)
    · exact Multiset.singleton_le.mp (le_trans
        (Multiset.singleton_le.mpr
          (Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _))) hleM)
  · intro h
    rw [Multiset.le_iff_count]
    intro a
    rw [count_sum_pair]
    have f_le_one : ∀ j : ℕ, (if a = 4 * j + 1 then (1 : ℕ) else 0) +
        (if a = 4 * j + 3 then 1 else 0) ≤ 1 := by
      intro j
      by_cases h1 : a = 4 * j + 1
      · simp [h1]
      · by_cases h3 : a = 4 * j + 3
        · simp [h3]
        · simp [h1, h3]
    have extract : ∀ j : ℕ, (if a = 4 * j + 1 then (1 : ℕ) else 0) +
        (if a = 4 * j + 3 then 1 else 0) ≠ 0 → a = 4 * j + 1 ∨ a = 4 * j + 3 := by
      intro j hj
      by_contra hc
      have hc' : a ≠ 4 * j + 1 ∧ a ≠ 4 * j + 3 := by
        simpa using hc
      simp [hc'.1, hc'.2] at hj
    have key : ∀ j₁ ∈ t, ∀ j₂ ∈ t,
        ((if a = 4 * j₁ + 1 then (1 : ℕ) else 0) + (if a = 4 * j₁ + 3 then 1 else 0)) ≠ 0 →
        ((if a = 4 * j₂ + 1 then (1 : ℕ) else 0) + (if a = 4 * j₂ + 3 then 1 else 0)) ≠ 0 →
        j₁ = j₂ := by
      intro j₁ _ j₂ _ h1 h2
      rcases extract j₁ h1 with e1 | e1 <;> rcases extract j₂ h2 with e2 | e2 <;> omega
    by_cases hex : ∃ j ∈ t, ((if a = 4 * j + 1 then (1 : ℕ) else 0) +
        (if a = 4 * j + 3 then 1 else 0)) ≠ 0
    · obtain ⟨j0, hj0t, hj0ne⟩ := hex
      have hzero : ∀ j ∈ t, j ≠ j0 →
          ((if a = 4 * j + 1 then (1 : ℕ) else 0) +
            (if a = 4 * j + 3 then 1 else 0)) = 0 := by
        intro j hjt hne
        by_contra hcon
        exact hne (key j hjt j0 hj0t hcon hj0ne)
      rw [Finset.sum_eq_single j0 hzero (fun h => absurd hj0t h)]
      rcases extract j0 hj0ne with e | e
      · have haM : a ∈ M := by
          rw [e]
          exact (h j0 hj0t).1
        exact le_trans (f_le_one j0) (Multiset.one_le_count_iff_mem.mpr haM)
      · have haM : a ∈ M := by
          rw [e]
          exact (h j0 hj0t).2
        exact le_trans (f_le_one j0) (Multiset.one_le_count_iff_mem.mpr haM)
    · have hex' : ∀ j ∈ t, ((if a = 4 * j + 1 then (1 : ℕ) else 0) +
          (if a = 4 * j + 3 then 1 else 0)) = 0 := by
        intro j hj
        by_contra hcon
        exact hex ⟨j, hj, hcon⟩
      rw [Finset.sum_eq_zero hex']
      exact Nat.zero_le _

private theorem sum_L_eq_sum_R (t : Finset ℕ) :
    (∑ j ∈ t, Multiset.replicate 4 (2 * j + 1)).sum =
    (∑ j ∈ t, ((4 * j + 1) ::ₘ ({(4 * j + 3)} : Multiset ℕ))).sum := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert j s hjs ih =>
    rw [Finset.sum_insert hjs, Finset.sum_insert hjs, Multiset.sum_add, Multiset.sum_add, ih,
      Multiset.sum_replicate, Multiset.sum_cons, Multiset.sum_singleton]
    rw [smul_eq_mul]
    ring

private theorem mem_L_oddpos (t : Finset ℕ) :
    ∀ x ∈ (∑ j ∈ t, Multiset.replicate 4 (2 * j + 1)), Odd x ∧ 0 < x := by
  induction t using Finset.induction_on with
  | empty =>
    intro x hx
    simp at hx
  | insert j s hjs ih =>
    intro x hx
    rw [Finset.sum_insert hjs, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · rw [Multiset.mem_replicate] at hx
      obtain ⟨_, rfl⟩ := hx
      exact ⟨⟨j, rfl⟩, by omega⟩
    · exact ih x hx

private theorem mem_R_oddpos (t : Finset ℕ) :
    ∀ x ∈ (∑ j ∈ t, ((4 * j + 1) ::ₘ ({(4 * j + 3)} : Multiset ℕ))), Odd x ∧ 0 < x := by
  induction t using Finset.induction_on with
  | empty =>
    intro x hx
    simp at hx
  | insert j s hjs ih =>
    intro x hx
    rw [Finset.sum_insert hjs, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · rw [Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨2 * j, by ring⟩, by omega⟩
      · exact ⟨⟨2 * j + 1, by ring⟩, by omega⟩
    · exact ih x hx

private theorem surgery_card (n : ℕ) (L R : Multiset ℕ)
    (hsum : L.sum = R.sum)
    (hoddL : ∀ x ∈ L, Odd x) (hposL : ∀ x ∈ L, 0 < x)
    (hoddR : ∀ x ∈ R, Odd x) (hposR : ∀ x ∈ R, 0 < x) :
    ((Nat.Partition.odds n).filter fun p => L ≤ p.parts).card =
    ((Nat.Partition.odds n).filter fun p => R ≤ p.parts).card := by
  have odd_not_even : ∀ x : ℕ, Odd x → ¬ Even x := by
    intro x hx
    obtain ⟨m, rfl⟩ := hx
    exact Nat.not_even_iff.mpr (by omega)
  have hFGparts : ∀ (p : Nat.Partition n),
      p ∈ (Nat.Partition.odds n).filter (fun p => L ≤ p.parts) →
      (p.parts - L + R) - R + L = p.parts := by
    intro p hp
    have hle : L ≤ p.parts := (Finset.mem_filter.mp hp).2
    rw [Multiset.add_sub_cancel_right]
    exact Multiset.sub_add_cancel hle
  have hGFparts : ∀ (q : Nat.Partition n),
      q ∈ (Nat.Partition.odds n).filter (fun q => R ≤ q.parts) →
      (q.parts - R + L) - L + R = q.parts := by
    intro q hq
    have hle : R ≤ q.parts := (Finset.mem_filter.mp hq).2
    rw [Multiset.add_sub_cancel_right]
    exact Multiset.sub_add_cancel hle
  refine Finset.card_bij
    (fun (p : Nat.Partition n)
      (hp : p ∈ (Nat.Partition.odds n).filter (fun p => L ≤ p.parts)) =>
      (⟨p.parts - L + R, fun hi => by
        rw [Multiset.mem_add] at hi
        rcases hi with hi | hi
        · exact p.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)
        · exact hposR _ hi, by
        have hle : L ≤ p.parts := (Finset.mem_filter.mp hp).2
        have hsub := Multiset.sub_add_cancel hle
        have e1 : (p.parts - L + L).sum = p.parts.sum := congrArg Multiset.sum hsub
        rw [Multiset.sum_add] at e1 ⊢
        have e2 := p.parts_sum
        omega⟩ : Nat.Partition n))
    ?_ ?_ ?_
  · intro p hp
    have hodd : ∀ i ∈ p.parts, ¬ Even i :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    rw [Finset.mem_filter]
    constructor
    · simp only [Nat.Partition.odds, Nat.Partition.restricted, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro i hi
      have hi' : i ∈ p.parts - L + R := hi
      rw [Multiset.mem_add] at hi'
      rcases hi' with hi' | hi'
      · exact hodd i (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi')
      · exact odd_not_even i (hoddR i hi')
    · change R ≤ p.parts - L + R
      exact Multiset.le_add_left _ _
  · intro p1 h1 p2 h2 heq
    have eparts : p1.parts - L + R = p2.parts - L + R :=
      congrArg Nat.Partition.parts heq
    have e1 := hFGparts p1 h1
    have e2 := hFGparts p2 h2
    rw [eparts] at e1
    rw [e2] at e1
    exact Nat.Partition.ext e1.symm
  · intro q hq
    have hGmem : (⟨q.parts - R + L, fun hi => by
          rw [Multiset.mem_add] at hi
          rcases hi with hi | hi
          · exact q.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)
          · exact hposL _ hi, by
          have hle : R ≤ q.parts := (Finset.mem_filter.mp hq).2
          have hsub := Multiset.sub_add_cancel hle
          have e1 : (q.parts - R + R).sum = q.parts.sum := congrArg Multiset.sum hsub
          rw [Multiset.sum_add] at e1 ⊢
          have e2 := q.parts_sum
          omega⟩ : Nat.Partition n) ∈
        (Nat.Partition.odds n).filter (fun p => L ≤ p.parts) := by
      have hodd : ∀ i ∈ q.parts, ¬ Even i :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
      rw [Finset.mem_filter]
      constructor
      · simp only [Nat.Partition.odds, Nat.Partition.restricted, Finset.mem_filter,
          Finset.mem_univ, true_and]
        intro i hi
        have hi' : i ∈ q.parts - R + L := hi
        rw [Multiset.mem_add] at hi'
        rcases hi' with hi' | hi'
        · exact hodd i (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi')
        · exact odd_not_even i (hoddL i hi')
      · change L ≤ q.parts - R + L
        exact Multiset.le_add_left _ _
    refine ⟨_, hGmem, ?_⟩
    apply Nat.Partition.ext
    change (q.parts - R + L) - L + R = q.parts
    exact hGFparts q hq

private theorem left_eq (n : ℕ) :
    Nat.Partition.odds n ∩ Nat.Partition.countRestricted n 4 =
    (Nat.Partition.odds n).filter fun p =>
      ∀ j ∈ Finset.range (n + 1), ¬ 4 ≤ p.parts.count (2 * j + 1) := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, Nat.Partition.odds,
    Nat.Partition.restricted, Nat.Partition.countRestricted, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hO, hC⟩
    refine ⟨hO, fun j _ => ?_⟩
    by_cases hj : 2 * j + 1 ∈ p.parts
    · exact Nat.not_le.mpr (hC _ hj)
    · rw [Multiset.count_eq_zero_of_notMem hj]
      omega
  · rintro ⟨hO, hV⟩
    refine ⟨hO, fun i hi => ?_⟩
    have hodd : ¬ Even i := hO i hi
    have h2 : i % 2 = 1 := Nat.not_even_iff.mp hodd
    have hle : i ≤ n := Nat.Partition.le_of_mem_parts hi
    have hmem : i / 2 ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      have hdiv : i / 2 ≤ i := Nat.div_le_self i 2
      omega
    have hVj := hV (i / 2) hmem
    have hii : i = 2 * (i / 2) + 1 := by omega
    rw [hii]
    exact Nat.not_le.mp hVj

private theorem right_eq (n : ℕ) :
    (Finset.univ.filter fun p : Nat.Partition n ↦
      (∀ i ∈ p.parts, i % 4 = 1 ∨ i % 4 = 3) ∧
        ∀ j ∈ Finset.range (n + 1),
          ¬ (4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts)) =
    (Nat.Partition.odds n).filter fun p =>
      ∀ j ∈ Finset.range (n + 1), ¬ (4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts) := by
  have odd_iff : ∀ (p : Nat.Partition n),
      (∀ i ∈ p.parts, ¬ Even i) ↔ (∀ i ∈ p.parts, i % 4 = 1 ∨ i % 4 = 3) := by
    intro p
    constructor
    · intro h i hi
      have h2 : i % 2 = 1 := Nat.not_even_iff.mp (h i hi)
      omega
    · intro h i hi
      have h4 := h i hi
      intro hev
      obtain ⟨m, rfl⟩ := hev
      omega
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.Partition.odds,
    Nat.Partition.restricted]
  constructor
  · rintro ⟨hm, hav⟩
    exact ⟨(odd_iff p).mpr hm, hav⟩
  · rintro ⟨ho, hav⟩
    exact ⟨(odd_iff p).mp ho, hav⟩

private theorem inter_eq (n : ℕ) (t : Finset ℕ) :
    ((Nat.Partition.odds n).filter fun p => ∀ j ∈ t, 4 ≤ p.parts.count (2 * j + 1)).card =
    ((Nat.Partition.odds n).filter fun p =>
      ∀ j ∈ t, (4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts)).card := by
  have eL : (Nat.Partition.odds n).filter (fun p => ∀ j ∈ t, 4 ≤ p.parts.count (2 * j + 1)) =
      (Nat.Partition.odds n).filter
        (fun p => (∑ j ∈ t, Multiset.replicate 4 (2 * j + 1)) ≤ p.parts) := by
    apply Finset.filter_congr
    intro p _
    exact (L_le_iff p.parts t).symm
  have eR : (Nat.Partition.odds n).filter
        (fun p => ∀ j ∈ t, (4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts)) =
      (Nat.Partition.odds n).filter
        (fun p => (∑ j ∈ t, ((4 * j + 1) ::ₘ ({(4 * j + 3)} : Multiset ℕ))) ≤ p.parts) := by
    apply Finset.filter_congr
    intro p _
    exact (R_le_iff p.parts t).symm
  rw [eL, eR]
  exact surgery_card n _ _ (sum_L_eq_sum_R t)
    (fun x hx => (mem_L_oddpos t x hx).1) (fun x hx => (mem_L_oddpos t x hx).2)
    (fun x hx => (mem_R_oddpos t x hx).1) (fun x hx => (mem_R_oddpos t x hx).2)

/--
**Andrews–Lewis identity.** For every natural number $n$, the number of partitions of $n$ into
odd parts in which each part occurs at most three times equals the number of partitions of $n$
into parts congruent to $1$ or $3$ modulo $4$ such that for no natural number $j \le n$ are both
$4j + 1$ and $4j + 3$ parts.

Proves `Wanted` entry `card_odd_countRestricted_four_eq_card_mod_four_pair_excluding`.

Source: the Andrews–Lewis identity (G. E. Andrews and R. P. Lewis, "An algebraic identity of
F. H. Jackson and its implications for partitions," Discrete Math. 232 (2001), 77–83) as quoted in
Michael D. Hirschhorn and James A. Sellers, "A Congruence Modulo 3 for Partitions into Distinct
Non-Multiples of Four," Journal of Integer Sequences 17 (2014), Article 14.9.6,
Theorem (label W-identity), lines 99–102.
`https://cs.uwaterloo.ca/journals/JIS/VOL17/Sellers/sellers32.tex`
-/
theorem card_odd_countRestricted_four_eq_card_mod_four_pair_excluding
    (n : ℕ) :
    (Nat.Partition.odds n ∩ Nat.Partition.countRestricted n 4).card =
      (Finset.univ.filter fun p : Nat.Partition n ↦
        (∀ i ∈ p.parts, i % 4 = 1 ∨ i % 4 = 3) ∧
          ∀ j ∈ Finset.range (n + 1),
            ¬ (4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts)).card := by
  rw [left_eq n, right_eq n]
  exact avoid_card_eq_of_inter_eq (Nat.Partition.odds n) (Nat.Partition.odds n)
    (Finset.range (n + 1)) (fun j p => 4 ≤ p.parts.count (2 * j + 1))
    (fun j p => 4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts) (fun t _ => inter_eq n t)

end MetaMathlibExt
end
