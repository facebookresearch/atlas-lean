/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ImpartialPebblingGame
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Replicate

/-!
# The all-N pebbling threshold on even complete graphs

The proof follows Lemmas 4, 6 and 7 and Theorem 1(e) of Fiorini, Lind, Woldar, and Wong,
*Characterizing Winning Positions in the Impartial Two-Player Pebbling Game on Complete Graphs*,
Journal of Integer Sequences 24 (2021), Article 21.6.4.
We work with multisets of piles: on a complete graph only the two pile sizes and their
multiplicities matter. A finite inverse-move computation identifies the P-positions two totals
above a known layer. Its result is stable under adding sufficiently many singleton piles.
-/

namespace MetaMathlibExt

open SpragueGrundy

namespace PebblingCompleteEven

private abbrev Bag := Multiset ℕ

private def Move (s t : Bag) : Prop :=
  ∃ x y r, s = (x + 2) ::ₘ y ::ₘ r ∧ t = x ::ₘ (y + 1) ::ₘ r

private theorem Move.sum_eq {s t : Bag} (h : Move s t) : t.sum + 1 = s.sum := by
  obtain ⟨x, y, r, rfl, rfl⟩ := h
  simp only [Multiset.sum_cons]
  omega

private theorem Move.card_eq {s t : Bag} (h : Move s t) : t.card = s.card := by
  obtain ⟨x, y, r, rfl, rfl⟩ := h
  simp

-- Enumerate ordered pairs, removing one occurrence of the first value before picking the second.
private def pairs (s : Bag) : Multiset (ℕ × ℕ × Bag) :=
  s.dedup.bind fun x => (s.erase x).dedup.map fun y => (x, y, (s.erase x).erase y)

private theorem mem_pairs {s r : Bag} {x y : ℕ} : (x, y, r) ∈ pairs s ↔ s = x ::ₘ y ::ₘ r := by
  simp only [pairs, Multiset.mem_bind, Multiset.mem_map, Multiset.mem_dedup, Prod.mk.injEq]
  constructor
  · rintro ⟨_, hx, _, hy, rfl, rfl, rfl⟩
    rw [Multiset.cons_erase hy, Multiset.cons_erase hx]
  · rintro rfl
    refine ⟨x, by simp, y, ?_, rfl, rfl, ?_⟩
    · simp
    · simp

private def options (s : Bag) : Multiset Bag :=
  ((pairs s).filter fun p => 2 ≤ p.1).map fun (x, y, r) => (x - 2) ::ₘ (y + 1) ::ₘ r

private def parents (t : Bag) : Multiset Bag :=
  ((pairs t).filter fun p => 1 ≤ p.2.1).map fun (x, y, r) => (x + 2) ::ₘ (y - 1) ::ₘ r

private theorem mem_options {s t : Bag} : t ∈ options s ↔ Move s t := by
  simp only [options, Multiset.mem_map, Multiset.mem_filter]
  constructor
  · rintro ⟨⟨x, y, r⟩, ⟨hp, hx⟩, rfl⟩
    exact ⟨x - 2, y, r, by simpa only [Nat.sub_add_cancel hx] using mem_pairs.mp hp, rfl⟩
  · rintro ⟨x, y, r, rfl, rfl⟩
    exact ⟨(x + 2, y, r), ⟨mem_pairs.mpr rfl, by simp⟩, by simp⟩

private theorem mem_parents {s t : Bag} : s ∈ parents t ↔ Move s t := by
  simp only [parents, Multiset.mem_map, Multiset.mem_filter]
  constructor
  · rintro ⟨⟨x, y, r⟩, ⟨hp, hy⟩, rfl⟩
    exact ⟨x, y - 1, r, rfl, by simpa only [Nat.sub_add_cancel hy] using mem_pairs.mp hp⟩
  · rintro ⟨x, y, r, rfl, rfl⟩
    exact ⟨(x, y + 1, r), ⟨mem_pairs.mpr rfl, by simp⟩, by simp⟩

private def allB {α : Type} (s : Multiset α) (p : α → Bool) : Bool :=
  (s.filter fun a => p a = false).card == 0

private theorem allB_eq {α : Type} (s : Multiset α) (p : α → Bool) :
    allB s p = true ↔ ∀ a ∈ s, p a = true := by
  simp [allB, Multiset.eq_zero_iff_forall_notMem]

private def outcomes : ℕ → Bag → Bool
  | 0, _ => true
  | fuel + 1, s => allB (options s) fun t => !(outcomes fuel t)

private def P (s : Bag) : Prop := outcomes s.sum s = true

private theorem outcomes_spec {fuel : ℕ} {s : Bag} (h : s.sum ≤ fuel) :
    outcomes fuel s = true ↔ P s := by
  induction fuel generalizing s with
  | zero => rw [P, show s.sum = 0 by omega]
  | succ fuel ih =>
    cases hs : s.sum with
    | zero =>
      have he : options s = 0 := Multiset.eq_zero_of_forall_notMem fun t ht => by
        have := (mem_options.mp ht).sum_eq
        omega
      simp [outcomes, allB_eq, he, P, hs]
    | succ m =>
      rw [P, hs, outcomes, outcomes]
      simp only [allB_eq, mem_options, Bool.not_eq_true']
      exact forall_congr' fun t => forall_congr' fun hst => by
        have := hst.sum_eq
        have hf : t.sum ≤ fuel := by omega
        have he : t.sum = m := by omega
        have hm : outcomes m t = true ↔ P t := by rw [P, he]
        simpa only [Bool.not_eq_true] using not_congr ((ih hf).trans hm.symm)

private theorem p_iff (s : Bag) : P s ↔ ∀ t, Move s t → ¬ P t := by
  cases hs : s.sum with
  | zero =>
    refine ⟨fun _ t ht => ?_, fun _ => by simp [P, hs, outcomes]⟩
    have := ht.sum_eq
    omega
  | succ m =>
    rw [P, hs, outcomes]
    simp only [allB_eq, mem_options, Bool.not_eq_true']
    exact forall_congr' fun t => forall_congr' fun hst => by
      have := hst.sum_eq
      simpa only [Bool.not_eq_true] using not_congr (outcomes_spec (s := t) (fuel := m) (by omega))

private theorem not_p_iff (s : Bag) : ¬ P s ↔ ∃ t, Move s t ∧ P t := by
  rw [p_iff]
  push Not
  rfl

private def bag {n : ℕ} (a : Fin n → ℕ) : Bag := Finset.univ.val.map a

private theorem bag_card {n : ℕ} (a : Fin n → ℕ) : (bag a).card = n := by
  simp [bag]

private theorem bag_sum {n : ℕ} (a : Fin n → ℕ) : (bag a).sum = ∑ i, a i := rfl

private theorem bag_surj {n : ℕ} (s : Bag) (hs : s.card = n) : ∃ a : Fin n → ℕ, bag a = s := by
  induction s using Quotient.inductionOn with
  | _ l =>
    have hl : l.length = n := hs
    subst n
    refine ⟨l.get, ?_⟩
    unfold bag
    rw [Fin.univ_def]
    change (((List.finRange l.length).map l.get : List ℕ) : Bag) = (l : Bag)
    rw [List.finRange, List.map_ofFn]
    change (↑(List.ofFn l.get) : Bag) = ↑l
    rw [List.ofFn_get]

private theorem map_erase {n : ℕ} (a : Fin n → ℕ) {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ S) : S.val.map a = a i ::ₘ (S.erase i).val.map a := by
  calc
    S.val.map a = (insert i (S.erase i)).val.map a := by rw [Finset.insert_erase hi]
    _ = _ := by rw [Finset.insert_val_of_notMem (Finset.notMem_erase _ _), Multiset.map_cons]

private theorem bag_split {n : ℕ} (a : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j) :
    bag a = a i ::ₘ a j ::ₘ (((Finset.univ.erase i).erase j).val.map a) := by
  unfold bag
  rw [map_erase a (Finset.mem_univ i), map_erase a (by simp [hij.symm] : j ∈ Finset.univ.erase i)]

private theorem bag_step {n : ℕ} (a : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j) :
    bag (pebblingStep 1 a i j) = (a i - 2) ::ₘ (a j + 1) ::ₘ
      (((Finset.univ.erase i).erase j).val.map a) := by
  rw [bag_split _ hij]
  simp only [pebblingStep, Function.update_of_ne hij, Function.update_self]
  congr 2
  exact Multiset.map_congr rfl fun v hv => by
    change v ∈ (Finset.univ.erase i).erase j at hv
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hv),
      Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hv))]

private theorem move_bag {n : ℕ} (a : Fin n → ℕ) (t : Bag) :
    Move (bag a) t ↔ ∃ b ∈ pebblingMoves (⊤ : SimpleGraph (Fin n)) 1 a, bag b = t := by
  constructor
  · rintro ⟨x, y, r, hs, rfl⟩
    have hx : x + 2 ∈ bag a := by simp [hs]
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hx
    have he : bag a = a i ::ₘ ((Finset.univ.erase i).val.map a) :=
      map_erase a (Finset.mem_univ i)
    rw [he, hi, Multiset.cons_inj_right] at hs
    have hy : y ∈ (Finset.univ.erase i).val.map a := by
      rw [hs]
      exact Multiset.mem_cons_self _ _
    obtain ⟨j, hj, haj⟩ := Multiset.mem_map.mp hy
    have hij : i ≠ j := (Finset.ne_of_mem_erase (show j ∈ Finset.univ.erase i from hj)).symm
    have hr : (((Finset.univ.erase i).erase j).val.map a) = r := by
      have hh := (bag_split a hij).symm.trans (he.trans (congrArg (a i ::ₘ ·) hs))
      simpa only [haj, Multiset.cons_inj_right] using hh
    exact ⟨_, (mem_pebblingMoves _ _ _ _).2 ⟨i, j, (SimpleGraph.top_adj _ _).2 hij, by omega, rfl⟩,
      by rw [bag_step _ hij, hi, haj, hr, Nat.add_sub_cancel]⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨i, j, hij, hi, rfl⟩ := (mem_pebblingMoves _ _ _ _).1 hb
    have hne := hij.ne
    exact ⟨a i - 2, a j, _, by rw [Nat.sub_add_cancel hi]; exact bag_split a hne, bag_step a hne⟩

private theorem isP_bag {n : ℕ} (a : Fin n → ℕ) :
    IsP (pebblingGame (⊤ : SimpleGraph (Fin n)) 1) a ↔ P (bag a) := by
  generalize hm : (bag a).sum = m
  induction m using Nat.strong_induction_on generalizing a with
  | ind m ih =>
    rw [p_iff]
    constructor
    · intro ha t ht
      obtain ⟨b, hb, rfl⟩ := (move_bag a t).mp ht
      have := ht.sum_eq
      exact fun hp => (isP_iff (pebblingGame (⊤ : SimpleGraph (Fin n)) 1) a).1 ha b hb
        ((ih _ (by omega) b rfl).2 hp)
    · intro ha
      refine (isP_iff (pebblingGame (⊤ : SimpleGraph (Fin n)) 1) a).2 fun b hb hp => ?_
      have ht := (move_bag a (bag b)).mpr ⟨b, hb, rfl⟩
      have := ht.sum_eq
      exact ha _ ht ((ih _ (by omega) b rfl).1 hp)

private def pad (u k : ℕ) (s : Bag) : Bag := s + Multiset.replicate k u

-- A pair selected after padding can already be selected before padding if the smaller
-- multiset contains enough copies of the padding value for this pair.
private theorem split_pad {u k a b : ℕ} {s r : Bag}
    (h : (a ::ₘ b ::ₘ (0 : Bag)).count u ≤ s.count u)
    (e : pad u k s = a ::ₘ b ::ₘ r) :
    ∃ t, s = a ::ₘ b ::ₘ t ∧ r = pad u k t := by
  have hsub : a ::ₘ b ::ₘ (0 : Bag) ≤ s := by
    refine Multiset.le_iff_count.mpr fun v => ?_
    by_cases hv : v = u
    · simpa only [hv] using h
    · have he := congrArg (Multiset.count v) e
      simp only [pad, Multiset.count_add, Multiset.count_replicate, ite_eq_right (Ne.symm hv),
        Nat.add_zero, Multiset.count_cons, Multiset.count_zero] at he ⊢
      omega
  obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hsub
  have hs : s = a ::ₘ b ::ₘ t := by simpa only [Multiset.cons_add, zero_add] using ht
  have hr : pad u k t = r := by
    simpa only [pad, hs, Multiset.cons_add, Multiset.cons_inj_right] using e
  exact ⟨t, hs, hr.symm⟩

private theorem Move.add_piles {s t : Bag} (h : Move s t) (u k : ℕ) :
    Move (pad u k s) (pad u k t) := by
  obtain ⟨x, y, r, rfl, rfl⟩ := h
  refine ⟨x, y, pad u k r, ?_, ?_⟩ <;> simp [pad]

private theorem Move.unpad {u k : ℕ} {s t : Bag} (hcount : 2 ≤ s.count u)
    (h : Move (pad u k s) t) : ∃ t₀, Move s t₀ ∧ t = pad u k t₀ := by
  obtain ⟨x, y, r, hs, rfl⟩ := h
  have h : ((x + 2) ::ₘ y ::ₘ (0 : Bag)).count u ≤ s.count u :=
    (Multiset.count_le_card _ _).trans (by simpa using hcount)
  obtain ⟨r₀, hr, rfl⟩ := split_pad h hs
  exact ⟨x ::ₘ (y + 1) ::ₘ r₀, ⟨x, y, r₀, hr, rfl⟩, by simp [pad]⟩

private theorem Move.unpad_rev {u k : ℕ} {s t : Bag} (hcount : 2 ≤ t.count u)
    (h : Move s (pad u k t)) : ∃ s₀, Move s₀ t ∧ s = pad u k s₀ := by
  obtain ⟨x, y, r, rfl, ht⟩ := h
  have h : (x ::ₘ (y + 1) ::ₘ (0 : Bag)).count u ≤ t.count u :=
    (Multiset.count_le_card _ _).trans (by simpa using hcount)
  obtain ⟨r₀, hr, rfl⟩ := split_pad h ht
  exact ⟨(x + 2) ::ₘ y ::ₘ r₀, ⟨x, y, r₀, rfl, hr⟩, by simp [pad]⟩

private theorem Move.count_bounds {s t : Bag} (h : Move s t) (u : ℕ) :
    s.count u ≤ t.count u + 2 ∧ t.count u ≤ s.count u + 2 := by
  obtain ⟨x, y, r, rfl, rfl⟩ := h
  simp only [Multiset.count_cons]
  split <;> split <;> split <;> split <;> omega

private theorem Move.count_zero {s t : Bag} (h : Move s t) : s.count 0 ≤ t.count 0 + 1 := by
  obtain ⟨x, y, r, rfl, rfl⟩ := h
  simp only [Multiset.count_cons]
  have hx : ¬ 0 = x + 2 := by omega
  have hy : ¬ 0 = y + 1 := by omega
  simp only [hx, hy, ite_false, Nat.add_zero]
  split <;> split <;> omega

private theorem pad_injective (u k : ℕ) : Function.Injective (pad u k) :=
  fun _ _ h => add_right_cancel h

private theorem pad_card (u k : ℕ) (s : Bag) : (pad u k s).card = s.card + k := by
  simp [pad]

private theorem pad_sum (u k : ℕ) (s : Bag) : (pad u k s).sum = s.sum + k * u := by
  simp [pad]

private theorem card_le_sum_add_zeros (s : Bag) : s.card ≤ s.sum + s.count 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x r ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.count_cons]
    split <;> omega

private theorem no_big_of_card_eq (s : Bag) (h : s.sum + s.count 0 ≤ s.card) :
    ∀ x ∈ s, x ≤ 1 := by
  intro x hx
  have he := Multiset.cons_erase hx
  have hr := card_le_sum_add_zeros (s.erase x)
  rw [← he] at h
  simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.count_cons] at h
  split at h <;> omega

private theorem terminal (s : Bag) (h : ∀ x ∈ s, x ≤ 1) : P s := by
  refine (p_iff s).2 ?_
  rintro _ ⟨x, y, r, rfl, _⟩
  have := h (x + 2) (Multiset.mem_cons_self _ _)
  omega

-- Lemma 4: a legal move uses at most one zero, and the count bound is preserved.
private theorem zeros_neutral (s : Bag) (k : ℕ) (h : s.sum ≤ s.card + s.count 0) :
    P (pad 0 k s) ↔ P s := by
  generalize hm : s.sum = m
  induction m using Nat.strong_induction_on generalizing s with
  | ind m ih =>
    have lower {t : Bag} (ht : Move s t) : P (pad 0 k t) ↔ P t := by
      have := ht.sum_eq
      have := ht.card_eq
      have := ht.count_zero
      exact ih t.sum (by omega) t (by omega) rfl
    constructor
    · intro hp
      exact (p_iff s).2 fun t ht htp =>
        (p_iff _).1 hp _ (ht.add_piles 0 k) ((lower ht).2 htp)
    · intro hp
      refine (p_iff _).2 fun t ht htp => ?_
      obtain ⟨x, y, r, hs, rfl⟩ := ht
      have hpos : 1 ≤ s.count 0 := by
        by_contra! hz
        have hx : x + 2 ∈ s := by
          have hx : x + 2 ∈ pad 0 k s := hs ▸ Multiset.mem_cons_self _ _
          simpa [pad, Multiset.mem_add, Multiset.mem_replicate] using hx
        have := no_big_of_card_eq s (by omega) (x + 2) hx
        omega
      have hcount : ((x + 2) ::ₘ y ::ₘ (0 : Bag)).count 0 ≤ s.count 0 := by
        have hx : ¬ 0 = x + 2 := by omega
        simp only [Multiset.count_cons, Multiset.count_zero, hx, ite_false, Nat.add_zero]
        split <;> omega
      obtain ⟨r₀, he, rfl⟩ := split_pad hcount hs
      have hmove : Move s (x ::ₘ (y + 1) ::ₘ r₀) := ⟨x, y, r₀, he, rfl⟩
      exact (p_iff s).1 hp _ hmove ((lower hmove).1 (by simpa [pad] using htp))

private def Layer (n m : ℕ) (Q : Multiset Bag) : Prop :=
  ∀ s : Bag, s.card = n → s.sum = m → (P s ↔ s ∈ Q)

private theorem has_move {s : Bag} (hcard : 2 ≤ s.card) (hsum : s.card < s.sum) :
    ∃ t, Move s t := by
  induction s using Multiset.induction_on with
  | empty => simp at hcard
  | cons x r _ =>
    have hbig : ∃ a ∈ x ::ₘ r, 2 ≤ a := by
      by_contra! h
      have hbound (s : Bag) : (∀ a ∈ s, a < 2) → s.sum ≤ s.card := by
        induction s using Multiset.induction_on with
        | empty => simp
        | cons y t ih =>
          intro h
          have := h y (Multiset.mem_cons_self _ _)
          have := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
          simp only [Multiset.card_cons, Multiset.sum_cons]
          omega
      exact (not_le_of_gt hsum) (hbound _ h)
    obtain ⟨a, ha, h₂⟩ := hbig
    let t := (x ::ₘ r).erase a
    have ht : a ::ₘ t = x ::ₘ r := Multiset.cons_erase ha
    have hne : t ≠ 0 := by
      intro h
      rw [← ht, h] at hcard
      simp at hcard
    obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hne
    refine ⟨(a - 2) ::ₘ (b + 1) ::ₘ t.erase b, a - 2, b, t.erase b, ?_, rfl⟩
    rw [Nat.sub_add_cancel h₂, Multiset.cons_erase hb, ht]

private def HasReply (Q : Multiset Bag) (s : Bag) : Prop :=
  ∀ t, Move s t → ∃ v ∈ Q, Move t v

private def replyB (Q : Multiset Bag) (s : Bag) : Bool :=
  allB (options s) fun t => !allB (options t) fun v => !(decide (v ∈ Q))

private theorem replyB_eq (Q : Multiset Bag) (s : Bag) : replyB Q s = true ↔ HasReply Q s := by
  classical
  simp only [replyB, allB_eq, Bool.not_eq_true', ← Bool.not_eq_true, mem_options, decide_eq_true_eq,
    HasReply]
  push Not
  exact forall_congr' fun t => forall_congr' fun _ => exists_congr fun v => and_comm

private def advance (Q : Multiset Bag) : Multiset Bag :=
  ((((Q.bind parents).bind parents).dedup).filter fun s => replyB Q s = true)

private theorem mem_advance {s : Bag} {Q : Multiset Bag} :
    s ∈ advance Q ↔ HasReply Q s ∧ ∃ v ∈ Q, ∃ t, Move s t ∧ Move t v := by
  simp only [advance, Multiset.mem_filter, Multiset.mem_dedup, Multiset.mem_bind, mem_parents,
    replyB_eq]
  constructor
  · rintro ⟨⟨t, ⟨v, hv, htv⟩, hst⟩, hr⟩
    exact ⟨hr, v, hv, t, hst, htv⟩
  · rintro ⟨hr, v, hv, t, hst, htv⟩
    exact ⟨⟨t, ⟨v, hv, htv⟩, hst⟩, hr⟩

private theorem layer_advance {n m : ℕ} {Q : Multiset Bag} (hn : 2 ≤ n) (hm : n < m + 2)
    (h : Layer n m Q) : Layer n (m + 2) (advance Q) := by
  intro s hs hm'
  have he : P s ↔ HasReply Q s := by
    rw [p_iff]
    refine forall_congr' fun t => forall_congr' fun hst => ?_
    rw [not_p_iff]
    refine exists_congr fun v => Iff.trans (and_congr_right fun htv => ?_) and_comm
    have := hst.sum_eq
    have := htv.sum_eq
    exact h v (htv.card_eq.trans (hst.card_eq.trans hs)) (by omega)
  rw [he, mem_advance]
  refine ⟨fun hr => ⟨hr, ?_⟩, And.left⟩
  obtain ⟨t, ht⟩ := has_move (by omega : 2 ≤ s.card) (by omega : s.card < s.sum)
  obtain ⟨v, hv, htv⟩ := hr t ht
  exact ⟨v, hv, t, ht, htv⟩

private theorem reply_pad {Q : Multiset Bag} {s : Bag} (k : ℕ) (hc : 4 ≤ s.count 1) :
    HasReply (Q.map (pad 1 k)) (pad 1 k s) ↔ HasReply Q s := by
  constructor
  · intro h t ht
    obtain ⟨v', hv', hm⟩ := h _ (ht.add_piles 1 k)
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hv'
    have := (ht.count_bounds 1).1
    obtain ⟨v₀, hm₀, he⟩ := hm.unpad (by omega)
    exact ⟨v, hv, (pad_injective 1 k he).symm ▸ hm₀⟩
  · intro h t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht.unpad (by omega)
    obtain ⟨v, hv, hm⟩ := h t₀ ht₀
    exact ⟨pad 1 k v, Multiset.mem_map.mpr ⟨v, hv, rfl⟩, hm.add_piles 1 k⟩

-- The computation inspects only two reverse moves followed by at most two forward moves.
-- Eight singleton piles per input suffice: each of the four decompositions uses at most two.
private theorem advance_pad (Q : Multiset Bag) (k : ℕ) (hc : ∀ v ∈ Q, 8 ≤ v.count 1) :
    advance (Q.map (pad 1 k)) = (advance Q).map (pad 1 k) := by
  have hn (R : Multiset Bag) : (advance R).Nodup :=
    (Multiset.nodup_dedup _).filter _
  apply (Multiset.Nodup.ext (hn _) ((hn _).map (pad_injective 1 k))).2
  intro s'
  refine ⟨?_, ?_⟩
  · intro hs
    obtain ⟨hr, v', hv', t', hst, htv⟩ := mem_advance.mp hs
    obtain ⟨v, hv, hve⟩ := Multiset.mem_map.mp hv'
    subst v'
    have hv₁ := hc v hv
    obtain ⟨t, htv₀, hte⟩ := htv.unpad_rev (by omega)
    subst t'
    have ht₁ := (htv₀.count_bounds 1).2
    obtain ⟨s, hst₀, hse⟩ := hst.unpad_rev (by omega)
    subst s'
    have hs₁ := (hst₀.count_bounds 1).2
    exact Multiset.mem_map.mpr ⟨s, mem_advance.mpr
      ⟨(reply_pad k (by omega)).1 hr, v, hv, t, hst₀, htv₀⟩, rfl⟩
  · intro hs
    obtain ⟨s, hs₀, hse⟩ := Multiset.mem_map.mp hs
    subst s'
    obtain ⟨hr, v, hv, t, hst, htv⟩ := mem_advance.mp hs₀
    have hv₁ := hc v hv
    have ht₁ := (htv.count_bounds 1).2
    have hs₁ := (hst.count_bounds 1).2
    exact mem_advance.mpr ⟨(reply_pad k (by omega)).2 hr, _,
      Multiset.mem_map.mpr ⟨v, hv, rfl⟩, _, hst.add_piles 1 k, htv.add_piles 1 k⟩

private theorem no_parent_pad (Q : Multiset Bag) (k : ℕ) (s : Bag)
    (hc : ∀ v ∈ Q, 2 ≤ v.count 1) :
    pad 1 k s ∉ (Q.map (pad 1 k)).bind parents ↔ s ∉ Q.bind parents := by
  simp only [Multiset.mem_bind, Multiset.mem_map, mem_parents]
  apply not_congr
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hm⟩
    obtain ⟨s₀, he, heq⟩ := hm.unpad_rev (hc v hv)
    exact ⟨v, hv, pad_injective 1 k heq ▸ he⟩
  · rintro ⟨v, hv, hm⟩
    exact ⟨pad 1 k v, ⟨v, hv, rfl⟩, hm.add_piles 1 k⟩

private theorem p_of_no_parent {n m : ℕ} {Q : Multiset Bag} {s : Bag}
    (h : Layer n m Q) (hs : s.card = n) (ht : s.sum = m + 1)
    (hs' : s ∉ Q.bind parents) : P s := by
  refine (p_iff s).2 fun v hmove hv => hs' ?_
  have := hmove.sum_eq
  exact Multiset.mem_bind.mpr ⟨v, (h v (hmove.card_eq.trans hs) (by omega)).1 hv,
    mem_parents.mpr hmove⟩

-- Fill the remaining vertices with ones. A shape is used only at widths admitting its list.
private def shape (n : ℕ) (l : List ℕ) : Bag := pad 1 (n - l.length) (l : Bag)

private def below (n : ℕ) : Multiset Bag := {shape n [0]}
private def first (n : ℕ) : Multiset Bag := {shape n [2]}
private def third (n : ℕ) : Multiset Bag := shape n [5, 0] ::ₘ shape n [3, 3, 0] ::ₘ 0
private def fifth (n : ℕ) : Multiset Bag := {shape n [6]}

private theorem shape_pad (n k : ℕ) (l : List ℕ) (hl : l.length ≤ n) :
    shape (n + k) l = pad 1 k (shape n l) := by
  have he : n + k - l.length = n - l.length + k := by omega
  simp only [shape, pad, he, Multiset.replicate_add, add_assoc]

-- The two-move computation is performed only on the inverse images of the indicated
-- P-positions. In particular, a candidate requiring more than six places cannot be generated
-- by the width-six computation. The last three tests supply the even-offset witnesses.
private def Certificate (n : ℕ) : Prop :=
  advance (below n) = first n ∧ advance (first n) = third n ∧
  advance (third n) = fifth n ∧ advance (fifth n) = 0 ∧
  shape n [2, 2] ∉ (first n).bind parents ∧
  shape n [5] ∉ (third n).bind parents ∧
  shape n [8, 2, 0, 0] ∉ (fifth n).bind parents

private instance (n : ℕ) : Decidable (Certificate n) := by
  unfold Certificate
  infer_instance

section

-- Bound the kernel reductions for these four fixed inverse-move tables.
set_option maxRecDepth 4096

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the fixed inverse-move table.
private theorem certificate_six : Certificate 6 := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the fixed inverse-move table.
private theorem certificate_eight : Certificate 8 := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the fixed inverse-move table.
private theorem certificate_ten : Certificate 10 := by decide

set_option maxHeartbeats 2000000 in
-- Kernel reduction checks the fixed inverse-move table.
private theorem certificate_twelve : Certificate 12 := by decide

end

private theorem certificate_large (k : ℕ) : Certificate (12 + k) := by
  have hb : below (12 + k) = (below 12).map (pad 1 k) := by
    simp [below, shape_pad 12 k [0] (by decide)]
  have hf : first (12 + k) = (first 12).map (pad 1 k) := by
    simp [first, shape_pad 12 k [2] (by decide)]
  have ht : third (12 + k) = (third 12).map (pad 1 k) := by
    simp [third, shape_pad 12 k [5, 0] (by decide), shape_pad 12 k [3, 3, 0] (by decide)]
  have hi : fifth (12 + k) = (fifth 12).map (pad 1 k) := by
    simp [fifth, shape_pad 12 k [6] (by decide)]
  have hb₈ : ∀ s ∈ below 12, 8 ≤ (s : Bag).count 1 := by
    simp only [below, Multiset.mem_singleton]
    rintro _ rfl
    decide
  have hf₈ : ∀ s ∈ first 12, 8 ≤ (s : Bag).count 1 := by
    simp only [first, Multiset.mem_singleton]
    rintro _ rfl
    decide
  have ht₈ : ∀ s ∈ third 12, 8 ≤ (s : Bag).count 1 := by
    simp only [third, Multiset.mem_cons, Multiset.notMem_zero, or_false]
    rintro _ (rfl | rfl) <;> decide
  have hi₈ : ∀ s ∈ fifth 12, 8 ≤ (s : Bag).count 1 := by
    simp only [fifth, Multiset.mem_singleton]
    rintro _ rfl
    decide
  obtain ⟨e₁, e₂, e₃, e₄, h₂, h₄, h₆⟩ := certificate_twelve
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb, advance_pad _ _ hb₈, e₁, ← hf]
  · rw [hf, advance_pad _ _ hf₈, e₂, ← ht]
  · rw [ht, advance_pad _ _ ht₈, e₃, ← hi]
  · rw [hi, advance_pad _ _ hi₈, e₄, Multiset.map_zero]
  · rw [hf, shape_pad 12 k [2, 2] (by decide)]
    exact (no_parent_pad _ _ _ fun s hs => (by decide : 2 ≤ 8).trans (hf₈ s hs)).2 h₂
  · rw [ht, shape_pad 12 k [5] (by decide)]
    exact (no_parent_pad _ _ _ fun s hs => (by decide : 2 ≤ 8).trans (ht₈ s hs)).2 h₄
  · rw [hi, shape_pad 12 k [8, 2, 0, 0] (by decide)]
    exact (no_parent_pad _ _ _ fun s hs => (by decide : 2 ≤ 8).trans (hi₈ s hs)).2 h₆

private theorem certificate (n : ℕ) (hn : 6 ≤ n) (heven : Even n) : Certificate n := by
  by_cases hl : 12 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl
    exact certificate_large k
  · obtain ⟨j, hj⟩ := heven
    have hns : n = 6 ∨ n = 8 ∨ n = 10 := by omega
    rcases hns with rfl | rfl | rfl
    · exact certificate_six
    · exact certificate_eight
    · exact certificate_ten

private def distributions : ℕ → ℕ → Multiset Bag
  | 0, m => if m = 0 then {0} else 0
  | n + 1, m => ((Multiset.range (m + 1)).bind fun x =>
      (distributions n (m - x)).map (x ::ₘ ·)).dedup

private theorem mem_distributions (s : Bag) : s ∈ distributions s.card s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [distributions]
  | cons x r ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons, distributions, Multiset.mem_dedup,
      Multiset.mem_bind, Multiset.mem_range, Multiset.mem_map]
    exact ⟨x, by omega, r, by simpa using ih, rfl⟩

private theorem layer_base : Layer 6 7 (first 6) := by
  have h : ((distributions 6 7).filter fun s => outcomes s.sum s = true) = first 6 := by decide
  intro s hs ht
  have hm := mem_distributions s
  rw [hs, ht] at hm
  rw [← h, Multiset.mem_filter]
  exact ⟨fun hp => ⟨hm, hp⟩, And.right⟩

private theorem small_counts (s : Bag) (hs : ∀ x ∈ s, x ≤ 1) :
    s.count 1 = s.sum ∧ s.count 0 + s.sum = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x r ih =>
    have hr := ih fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have hx := hs x (Multiset.mem_cons_self _ _)
    have he : x = 0 ∨ x = 1 := by omega
    rcases he with rfl | rfl <;> simp <;> omega

-- First half of Lemma 7: on n+2 vertices at total n+1, only the binary shape is P.
private theorem layer_below {n : ℕ} (hn : 6 ≤ n) (h : Layer n (n + 1) (first n)) :
    Layer (n + 2) ((n + 2) - 1) (below (n + 2)) := by
  intro s hc hm
  rw [below, Multiset.mem_singleton]
  have hb : shape (n + 2) [0] = pad 1 (n + 1) ({0} : Bag) := by
    simp [shape]
  rw [hb]
  refine ⟨fun hp => ?_, ?_⟩
  · by_cases hz : 3 ≤ s.count 0
    · have hsub : Multiset.replicate 2 0 ≤ s := by
        refine Multiset.le_iff_count.mpr fun x => ?_
        by_cases hx : x = 0
        · subst x
          simpa [Multiset.count_replicate] using (by omega : 2 ≤ s.count 0)
        · simp only [Multiset.count_replicate, ite_eq_right (Ne.symm hx), Nat.zero_le]
      obtain ⟨r, hr⟩ := Multiset.le_iff_exists_add.mp hsub
      have he : s = pad 0 2 r := by simpa [pad, add_comm] using hr
      rw [he, pad_card] at hc
      rw [he, pad_sum, Nat.mul_zero, Nat.add_zero] at hm
      have hrz : 1 ≤ r.count 0 := by
        simpa [he, pad, Multiset.count_add, Multiset.count_replicate] using hz
      rw [he, zeros_neutral r 2 (by omega)] at hp
      have hf := (h r (by omega) (by omega)).1 hp
      rw [first, Multiset.mem_singleton] at hf
      rw [hf] at hrz
      simp [shape, pad, Multiset.count_replicate] at hrz
    · by_cases hbig : ∃ x ∈ s, 2 ≤ x
      · obtain ⟨x, hx, hx₂⟩ := hbig
        let r := s.erase x
        have he : s = x ::ₘ r := (Multiset.cons_erase hx).symm
        have hzx : s.count 0 = r.count 0 := by
          rw [he, Multiset.count_cons]
          simp [show (0 : ℕ) ≠ x by omega]
        have hsc : s.card = r.card + 1 := by rw [he, Multiset.card_cons]
        have hss : s.sum = x + r.sum := by rw [he, Multiset.sum_cons]
        have hbound := card_le_sum_add_zeros r
        have hxe : x = 2 := by omega
        have hrz : 0 ∈ r := by
          exact Multiset.count_pos.mp (by omega : 0 < r.count 0)
        have hsmall := no_big_of_card_eq r (by omega)
        have hmove : Move s (0 ::ₘ 1 ::ₘ r.erase 0) :=
          ⟨0, 0, _, by rw [Multiset.cons_erase hrz, he, hxe], rfl⟩
        have hp' := terminal (0 ::ₘ 1 ::ₘ r.erase 0) (by
          intro v hv
          simp only [Multiset.mem_cons] at hv
          rcases hv with rfl | rfl | hv
          · decide
          · decide
          · exact hsmall v (Multiset.mem_of_mem_erase hv))
        exact ((p_iff _).1 hp _ hmove hp').elim
      · push Not at hbig
        have hle : ∀ x ∈ s, x ≤ 1 := fun x hx => by have := hbig x hx; omega
        have ⟨h1, h0⟩ := small_counts s hle
        apply Multiset.ext.mpr
        intro x
        by_cases hx0 : x = 0
        · subst x
          simp [pad, Multiset.count_replicate]
          omega
        by_cases hx1 : x = 1
        · subst x
          simp [pad]
          omega
        have hx : x ∉ s := fun hx => by have := hle x hx; omega
        simp [hx0, hx1, Ne.symm hx1, pad,
          Multiset.count_replicate, Multiset.count_eq_zero_of_notMem hx]
  · rintro rfl
    apply terminal
    intro v hv
    simp only [pad, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate] at hv
    rcases hv with rfl | ⟨_, rfl⟩ <;> decide

private theorem layer_first (n : ℕ) (hn : 6 ≤ n) (heven : Even n) :
    Layer n (n + 1) (first n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases he : n = 6
    · subst n
      exact layer_base
    · have hn' : 6 ≤ n - 2 := by obtain ⟨k, hk⟩ := heven; omega
      have he' : Even (n - 2) := by
        obtain ⟨k, hk⟩ := heven
        exact ⟨k - 1, by omega⟩
      have h := layer_below hn' (ih (n - 2) (by omega) hn' he')
      have heq : n - 2 + 2 = n := by omega
      rw [heq] at h
      have h' := layer_advance (by omega) (by omega) h
      rw [(certificate n hn heven).1, show n - 1 + 2 = n + 1 by omega] at h'
      exact h'

private theorem shape_card {n : ℕ} {l : List ℕ} (hl : l.length ≤ n) :
    (shape n l).card = n := by
  simp [shape, pad_card, Nat.add_sub_of_le hl]

private theorem shape_sum (n : ℕ) (l : List ℕ) :
    (shape n l).sum = l.sum + (n - l.length) := by
  simp [shape, pad_sum]

private theorem p_below_seven {n m : ℕ} (hn : 6 ≤ n) (hm : m < n + 7)
    (h₁ : Layer n (n + 1) (first n)) (h₃ : Layer n (n + 3) (third n))
    (h₅ : Layer n (n + 5) (fifth n)) (cert : Certificate n) :
    ∃ s : Bag, s.card = n ∧ s.sum = m ∧ P s := by
  by_cases hmn : m ≤ n
  · let s := pad 0 (n - m) (Multiset.replicate m 1)
    refine ⟨s, by simp [s, pad_card, Nat.add_sub_of_le hmn], by simp [s, pad_sum], terminal s ?_⟩
    intro v hv
    simp only [s, pad, Multiset.mem_add, Multiset.mem_replicate] at hv
    rcases hv with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  obtain ⟨_, _, _, _, h₂, h₄, h₆⟩ := cert
  have hoff : m = n + 1 ∨ m = n + 2 ∨ m = n + 3 ∨ m = n + 4 ∨ m = n + 5 ∨ m = n + 6 := by
    omega
  rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : (shape n [2]).card = n := shape_card (by simp; omega)
    have hs : (shape n [2]).sum = n + 1 := by rw [shape_sum]; simp; omega
    exact ⟨_, hc, hs, (h₁ _ hc hs).2 (by simp [first])⟩
  · have hc : (shape n [2, 2]).card = n := shape_card (by simp; omega)
    have hs : (shape n [2, 2]).sum = n + 2 := by rw [shape_sum]; simp; omega
    exact ⟨_, hc, hs, p_of_no_parent h₁ hc hs h₂⟩
  · have hc : (shape n [5, 0]).card = n := shape_card (by simp; omega)
    have hs : (shape n [5, 0]).sum = n + 3 := by rw [shape_sum]; simp; omega
    exact ⟨_, hc, hs, (h₃ _ hc hs).2 (by simp [third])⟩
  · have hc : (shape n [5]).card = n := shape_card (by simp; omega)
    have hs : (shape n [5]).sum = n + 4 := by rw [shape_sum]; simp; omega
    exact ⟨_, hc, hs, p_of_no_parent h₃ hc hs h₄⟩
  · have hc : (shape n [6]).card = n := shape_card (by simp; omega)
    have hs : (shape n [6]).sum = n + 5 := by rw [shape_sum]; simp; omega
    exact ⟨_, hc, hs, (h₅ _ hc hs).2 (by simp [fifth])⟩
  · have hc : (shape n [8, 2, 0, 0]).card = n := shape_card (by simp; omega)
    have hs : (shape n [8, 2, 0, 0]).sum = n + 6 := by rw [shape_sum]; simp; omega
    exact ⟨_, hc, hs, p_of_no_parent h₅ hc hs h₆⟩

end PebblingCompleteEven

/-- **All-N threshold of $(2:1)$-pebbling on $K_n$ for even $n$.** For every even $n \ge 6$, the
least number $m$ such that every $(2:1)$-pebbling game on the complete graph $K_n$ with $m$
pebbles in total is an N-game, written $m^{(2:1)}(K_n)$, exists and equals $n + 7$.

Source: Barker, DeStefano, Fiorini, Gohn, Miller, Roeder, and Wong, *Generalized Impartial
Two-player Pebbling Games on `K_3` and `C_4`*, Journal of Integer Sequences 27 (2024),
Article 24.5.8, Theorem 1(e), quoting Fiorini, Lind, Woldar, and Wong (2021). -/
public theorem isLeast_pebblingAllNTotals_complete_even (n : ℕ) (hn : 6 ≤ n)
    (heven : Even n) : IsLeast (pebblingAllNTotals (⊤ : SimpleGraph (Fin n)) 1) (n + 7) := by
  open PebblingCompleteEven in
  have cert := certificate n hn heven
  have h₁ := layer_first n hn heven
  have h₃ := layer_advance (by omega) (by omega) h₁
  rw [cert.2.1] at h₃
  have h₅ := layer_advance (by omega) (by omega) h₃
  rw [cert.2.2.1] at h₅
  have h₇ := layer_advance (by omega) (by omega) h₅
  rw [cert.2.2.2.1] at h₇
  refine ⟨?_, ?_⟩
  · intro a ha hp
    have hs := h₇ (bag a) (bag_card a) ((bag_sum a).trans ha)
    exact Multiset.notMem_zero _ (hs.1 ((isP_bag a).1 hp))
  · intro m hm
    by_contra! hlt
    obtain ⟨s, hsc, hsm, hp⟩ := p_below_seven hn hlt h₁ h₃ h₅ cert
    obtain ⟨a, hbag⟩ := bag_surj s hsc
    exact hm a (by rw [← bag_sum, hbag, hsm]) ((isP_bag a).2 (hbag ▸ hp))

end MetaMathlibExt
