/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Inventory sequences end in short loops

Source record `OPG-37226`, ported from the Open Problem Garden entry
"Sequence defined on multisets"
(http://www.openproblemgarden.org/op/a_sequence_defined_on_multisets).

Starting from a `2 × n` array whose first row lists distinct increasing
positive integers and whose second row holds arbitrary positive integers,
each step replaces the array by the sorted list of all integers occurring
anywhere in it together with their total multiplicities. The theorem `conjecture_holds`
shows that the process always reaches a loop of one, two, or three arrays.
Multiplicities are counted across both rows of the array.

The proof uses the multiset inventory map of Cain and Enin. First the set of keys stabilizes.
For a fixed set of keys, the multiset of counts follows a histogram recurrence. At a minimum
of the histogram cardinality, two further steps give a multiset with at most four entries.
The resulting finite table includes the period-three case. -/

@[expose] public section

namespace MathlibExt.Combinatorics.MultisetSequenceLoopWanted

/-- **Inventory step.** The inventory step sends a pair of finite lists of natural numbers (the two
rows of an array) to the pair consisting of the increasing list of the distinct numbers occurring
in either list and the list of how many times each of these numbers occurs in the two lists
together. -/
def step : List ℕ × List ℕ → List ℕ × List ℕ := fun (keys, mults) =>
  let all := keys ++ mults
  let vals := all.toFinset.sort (· ≤ ·)
  (vals, vals.map (fun v => all.count v))

/-- **Inventory loop conjecture.** Let $a_1 < \dots < a_n$ and $b_1, \dots, b_n$ be positive
integers, and iterate the inventory step starting from the pair of rows $(a_1, \dots, a_n)$ and
$(b_1, \dots, b_n)$, where the inventory step replaces a pair of rows by the increasing list of the
distinct integers occurring in either row together with the list of the number of times each of
them occurs in the two rows combined. Then there are a natural number $t$ and a
$p \in \{1, 2, 3\}$ such that the $(t + p)$-th iterate equals the $t$-th iterate. -/
def conjecture : Prop :=
  ∀ keys mults : List ℕ, keys.Pairwise (· < ·) →
    (∀ a ∈ keys, 0 < a) → (∀ b ∈ mults, 0 < b) →
    keys.length = mults.length →
    ∃ t p : ℕ, 1 ≤ p ∧ p ≤ 3 ∧
      (step^[t + p]) (keys, mults) = (step^[t]) (keys, mults)

open Multiset

/-- The multiset of positive multiplicities, one per distinct entry of the input. -/
private def freq (s : Multiset ℕ) : Multiset ℕ := s.dedup.map (fun a => s.count a)

private theorem mem_freq {s : Multiset ℕ} {v : ℕ} :
    v ∈ freq s ↔ ∃ a ∈ s, s.count a = v := by simp [freq]

private theorem pos_freq {s : Multiset ℕ} {v : ℕ} (h : v ∈ freq s) : 0 < v := by
  obtain ⟨a, ha, rfl⟩ := mem_freq.mp h
  exact count_pos.mpr ha

private theorem card_freq (s : Multiset ℕ) : (freq s).card = s.toFinset.card := by
  simp [freq, card_toFinset]

private theorem sum_freq (s : Multiset ℕ) : (freq s).sum = s.card :=
  s.toFinset_sum_count_eq

private def extra (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

/-- On a fixed set of `n` keys, encode a row of counts by subtracting one from
each count and discarding the zeros. Taking inventory of that row counts each
positive entry in the encoding and, if present, the omitted zeros. -/
private def hist (n : ℕ) (s : Multiset ℕ) : Multiset ℕ :=
  freq s + extra (n - s.card)

private theorem hist_width (n : ℕ) (s : Multiset ℕ) :
    (hist n s).card ≤ s.toFinset.card + 1 := by
  simp [hist, extra, apply_ite, card_add, card_freq]
  split <;> omega

private def Short {α : Type} (f : α → α) (x : α) : Prop :=
  ∃ t p : ℕ, 1 ≤ p ∧ p ≤ 3 ∧ f^[t + p] x = f^[t] x

private theorem short_of_iterate {α : Type} {f : α → α} {x : α} {i : ℕ}
    (h : Short f (f^[i] x)) : Short f x := by
  obtain ⟨t, p, hp, hp', h⟩ := h
  refine ⟨t + i, p, hp, hp', ?_⟩
  rw [show t + i + p = (t + p) + i by omega, Function.iterate_add_apply,
    Function.iterate_add_apply f t i]
  exact h

private theorem short_of_step {α : Type} {f : α → α} {x : α} (h : Short f (f x)) :
    Short f x := short_of_iterate (i := 1) h

-- At an iterate of minimum cardinality, taking the histogram cannot decrease the
-- cardinality. Thus there is at most one repeated entry beyond the distinct entries.
-- The next histogram uses only 1, 2 and the number of omitted zeros.
private theorem reaches_small (n : ℕ) (s : Multiset ℕ) :
    ∃ i, ((hist n)^[i] s).card ≤ 4 := by
  classical
  obtain ⟨k, hk⟩ := Nat.find_spec (show ∃ k, ∃ i, ((hist n)^[i] s).card = k from
    ⟨_, 0, rfl⟩)
  let a := (hist n)^[k] s
  have hmin : a.card ≤ (hist n a).card := by
    rw [show a.card = _ from hk]
    apply Nat.find_min'
    exact ⟨k + 1, by simp [Function.iterate_succ_apply', a]⟩
  have hm := card_le_card_toFinset_add_one_iff.mp (hmin.trans (hist_width n a))
  have hf : ∀ v ∈ freq a, v = 1 ∨ v = 2 := by
    intro v hv
    have hp := pos_freq hv
    obtain ⟨x, hx, rfl⟩ := mem_freq.mp hv
    by_cases h : 1 < a.count x
    · exact Or.inr (hm x x h h).2
    · omega
  have hsub : (hist n a).toFinset ⊆ {1, 2, n - a.card} := by
    intro v hv
    simp only [mem_toFinset, hist, mem_add] at hv
    rcases hv with h | h
    · rcases hf v h with rfl | rfl <;> simp
    · by_cases he : n - a.card = 0 <;> simp_all [extra]
  have hc := Finset.card_le_card hsub
  have hi := hist_width n (hist n a)
  have h3 : ({1, 2, n - a.card} : Finset ℕ).card ≤ 3 := by
    have := Finset.card_insert_le 2 {n - a.card}
    simp at this
    exact (Finset.card_insert_le ..).trans (by omega)
  have hsmall : (hist n (hist n a)).card ≤ 4 := by omega
  exact ⟨k + 2, by simpa [Function.iterate_succ_apply', a] using hsmall⟩

-- Enumerate all multisets of positive entries with sum at most four.
private def words : ℕ → List (Multiset ℕ)
  | 0 => [0]
  | n + 1 => 0 :: [1, 2, 3, 4].flatMap (fun x => (words n).map (cons x))

private theorem mem_words (s : Multiset ℕ) (n : ℕ) (hc : s.card ≤ n)
    (hv : ∀ x ∈ s, x ∈ ([1, 2, 3, 4] : List ℕ)) : s ∈ words n := by
  induction n generalizing s with
  | zero =>
    have : s = 0 := card_eq_zero.mp (by omega)
    simp [this, words]
  | succ n ih =>
    induction s using Multiset.induction_on with
    | empty => simp [words]
    | cons a s _ =>
      have ha := hv a (mem_cons_self ..)
      simp only [words, List.mem_cons, List.mem_flatMap, List.mem_map]
      right
      refine ⟨a, by simpa only [List.mem_cons] using ha, s, ih s (by simpa using hc) ?_, rfl⟩
      exact fun x hx => hv x (mem_cons_of_mem hx)

private def patterns := (words 4).filter (fun p => p.sum ≤ 4)

private theorem freq_pattern (s : Multiset ℕ) (hs : s.card ≤ 4) : freq s ∈ patterns := by
  apply List.mem_filter.mpr
  refine ⟨mem_words _ _ ((card_freq s) ▸ s.toFinset_card_le.trans hs) ?_, by simpa [sum_freq]⟩
  intro v hv
  have hp := pos_freq hv
  obtain ⟨x, hx, rfl⟩ := mem_freq.mp hv
  have h := count_le_card x s
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private def repeats {α : Type} [DecidableEq α] (f : α → α) (a : α) : Bool :=
  f a == a || f (f a) == a || f (f (f a)) == a

private theorem short_of_repeats {α : Type} [DecidableEq α] {f : α → α} {a : α}
    (h : repeats f a) : Short f a := by
  simp only [repeats, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact ⟨0, 1, by decide, by decide, h⟩
  · exact ⟨0, 2, by decide, by decide, h⟩
  · exact ⟨0, 3, by decide, by decide, h⟩

private def smallCheck (n : ℕ) (p : Multiset ℕ) : Bool :=
  repeats (hist n) ((hist n)^[6] (p + extra (n - p.sum)))

private theorem small_table : (List.range 14).all (fun n => patterns.all (smallCheck n)) := by
  decide

-- For large supports, distinguish the single entry equal to `n - p.sum`. As long as
-- this exceeds every entry in `p`, the evolution of the other entries is independent of `n`.
private def core (p : Multiset ℕ) : Multiset ℕ := 1 ::ₘ freq p

private def liftCore (n : ℕ) (p : Multiset ℕ) : Multiset ℕ := (n - p.sum) ::ₘ p

private theorem freq_cons_fresh (v : ℕ) (p : Multiset ℕ) (hv : v ∉ p) :
    freq (v ::ₘ p) = 1 ::ₘ freq p := by
  simp only [freq, dedup_cons_of_notMem hv, map_cons, count_cons_self, count_eq_zero.mpr hv,
    Nat.zero_add]
  congr 1
  apply Multiset.map_congr rfl
  intro x hx
  have h : x ≠ v := by rintro rfl; exact hv (mem_dedup.mp hx)
  simp [h]

private theorem hist_lift (n : ℕ) (p : Multiset ℕ) (h : 2 * p.sum + p.card + 1 < n) :
    hist n (liftCore n p) = liftCore n (core p) := by
  have hv : n - p.sum ∉ p := by
    intro hm
    have := Multiset.le_sum_of_mem hm
    omega
  have hk : n - (p.card + 1) ≠ 0 := by omega
  simp [hist, liftCore, core, freq_cons_fresh _ _ hv, sum_freq, extra, hk, add_comm,
    Multiset.cons_swap]

private theorem large_table : patterns.all (fun p =>
    (List.range 6).all (fun i => let q := core^[i] p; 2 * q.sum + q.card + 1 < 14) &&
      core^[6] p == core^[4] p) := by decide

private theorem short_hist (n : ℕ) (s : Multiset ℕ) : Short (hist n) s := by
  obtain ⟨i, hi⟩ := reaches_small n s
  apply short_of_iterate (i := i)
  apply short_of_step
  let a := (hist n)^[i] s
  let p := freq a
  have hp : p ∈ patterns := freq_pattern _ hi
  have he : hist n a = p + extra (n - p.sum) := by simp [p, hist, sum_freq]
  change Short _ (hist n a)
  rw [he]
  by_cases hn : n < 14
  · apply short_of_iterate (i := 6)
    apply short_of_repeats
    exact List.all_eq_true.mp (List.all_eq_true.mp small_table n (List.mem_range.mpr hn)) p hp
  have ht := List.all_eq_true.mp large_table p hp
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at ht
  have hh : ∀ j ≤ 6, (hist n)^[j] (liftCore n p) = liftCore n (core^[j] p) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
      exact hist_lift _ _ ((ht.1 j (by omega)).trans_le (by omega))
  have hsmall : p.sum ≤ 4 := by simpa [p, sum_freq] using hi
  have hk : n - p.sum ≠ 0 := by omega
  rw [show p + extra (n - p.sum) = liftCore n p by
    simp [extra, liftCore, hk, ← singleton_add, add_comm]]
  refine ⟨4, 2, by decide, by decide, ?_⟩
  rw [hh 6 (by decide), hh 4 (by decide), ht.2]

private def next (s : Multiset ℕ) := s.dedup + freq s

private theorem support_mono (s : Multiset ℕ) : s.toFinset ⊆ (next s).toFinset := by
  intro a ha
  simp_all [next]

private theorem card_next (s : Multiset ℕ) : (next s).card = 2 * s.toFinset.card := by
  simp [next, card_freq, card_toFinset, Nat.two_mul]

private theorem next_avg (s : Multiset ℕ) : (next s).card ≤ 2 * (next s).toFinset.card := by
  rw [card_next]
  exact Nat.mul_le_mul_left _ (Finset.card_le_card (support_mono s))

private theorem few_distinct (p : Multiset ℕ) (hd : p.Nodup) (hs : p.sum ≤ 2 * p.card) :
    p.card ≤ 9 := by
  let l := p.filter (· < 3)
  let h := p.filter (fun x => ¬x < 3)
  have eq : l + h = p := filter_add_not ..
  have hsub : l.toFinset ⊆ Finset.range 3 := by simp [l, Finset.subset_iff]
  have hl : l.card ≤ 3 := by
    simpa only [toFinset_card_of_nodup (show l.Nodup from hd.filter _), Finset.card_range] using
      Finset.card_le_card hsub
  have hh : 3 * h.card ≤ h.sum := by
    simpa [mul_comm] using (card_nsmul_le_sum (s := h) (a := 3) (by simp [h]))
  have hc := congrArg card eq
  have hv := congrArg Multiset.sum eq
  simp only [card_add, sum_add] at hc hv
  omega

-- If every entry of an inventory has the same multiplicity, that multiplicity is
-- at most two. In either case the previous multiplicities are distinct. Their mean
-- is at most two, so the preceding inventory had at most nine distinct entries.
private theorem uniform_bound (s : Multiset ℕ) (hs : s.card ≤ 2 * s.toFinset.card)
    (m : ℕ) (hu : ∀ x ∈ next s, (next s).count x = m) : (next s).toFinset.card ≤ 18 := by
  have hsum := sum_freq (next s)
  have he : freq (next s) = replicate (freq (next s)).card m := by
    apply eq_replicate_of_mem
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_freq.mp hv
    exact hu x hx
  rw [he, sum_replicate, card_freq, card_next, Nat.nsmul_eq_mul] at hsum
  have hc := Finset.card_le_card (support_mono s)
  by_cases hz : s.toFinset.card = 0
  · simp_all [next, freq]
  have hm : m ≤ 2 := by
    by_contra! h
    have := Nat.mul_le_mul hc (show 3 ≤ m by omega)
    omega
  have hd : (freq s).Nodup := by
    apply nodup_iff_count_le_one.mpr
    intro v
    by_contra! h
    have hv : v ∈ freq s := count_pos.mp (by omega)
    have heq := hu v (mem_add.mpr (Or.inr hv))
    simp only [next, count_add, count_dedup] at heq
    have htwo : m = 2 := by omega
    have hcard : (next s).toFinset.card = s.toFinset.card := by rw [htwo] at hsum; omega
    have hsets := Finset.eq_of_subset_of_card_le (support_mono s) hcard.le
    have hmem : v ∈ s := by
      rw [← mem_toFinset, hsets]
      exact mem_toFinset.mpr (mem_add.mpr (Or.inr hv))
    simp [hmem] at heq
    omega
  have h9 := few_distinct (freq s) hd (by simpa [sum_freq, card_freq] using hs)
  have hc' := (next s).toFinset_card_le
  rw [card_next] at hc'
  rw [card_freq] at h9
  omega

private def bounded (m : ℕ) (s : Multiset ℕ) := s.toFinset ⊆ Finset.Icc 1 m

-- To exceed a bound `m`, a count would have to use one key and all `m` counts
-- from the previous inventory. Uniform multiplicities are impossible at this size.
private theorem bound_step (m : ℕ) (hm : 18 < m) (s : Multiset ℕ)
    (hs : s.card ≤ 2 * s.toFinset.card) (hb : bounded m (next (next s))) :
    bounded m (next (next (next s))) := by
  let c := next s
  change (next (next c)).toFinset ⊆ _
  have hc : c.toFinset.card ≤ m := by
    simpa using Finset.card_le_card ((support_mono c).trans hb)
  intro v hv
  rw [mem_toFinset, next, mem_add] at hv
  rcases hv with hv | hv
  · exact hb (mem_toFinset.mpr (mem_dedup.mp hv))
  have hvpos := pos_freq hv
  obtain ⟨a, ha, rfl⟩ := mem_freq.mp hv
  apply Finset.mem_Icc.mpr
  refine ⟨hvpos, ?_⟩
  by_contra! h
  have hcount : (next c).count a ≤ 1 + (freq c).count a := by
    simp only [next, count_add, count_dedup]
    split <;> omega
  have hle := count_le_card a (freq c)
  have hcard := card_freq c
  have hall := count_eq_card.mp (show (freq c).count a = (freq c).card by omega)
  have hsmall := uniform_bound s hs a (fun x hx => (hall _ (mem_freq.mpr ⟨x, hx, rfl⟩)).symm)
  change c.toFinset.card ≤ 18 at hsmall
  omega

private theorem positive_next {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) :
    ∀ x ∈ next s, 0 < x := by
  intro x hx
  rcases mem_add.mp hx with h | h
  · exact hs x (mem_dedup.mp h)
  · exact pos_freq h

private theorem stable_support (s : Multiset ℕ) (hs : ∀ x ∈ s, 0 < x) :
    ∃ t, ∀ j, (next^[j] (next^[t] s)).toFinset = (next^[t] s).toFinset := by
  classical
  let a (i : ℕ) := next^[i + 3] s
  let m := (a 0).sum + 19
  have hb : ∀ i, bounded m (a i) := by
    intro i
    induction i with
    | zero =>
      intro x hx
      have hmem := mem_toFinset.mp hx
      have hpos := positive_next (positive_next (positive_next hs))
      have hle := le_sum_of_mem hmem
      exact Finset.mem_Icc.mpr ⟨hpos _ hmem, by dsimp [m]; omega⟩
    | succ i ih =>
      have he : a i = next (next (next (next^[i] s))) := by simp [a, Function.iterate_succ_apply']
      rw [he] at ih
      simpa [a, Function.iterate_succ_apply'] using
        bound_step m (by dsimp [m]; omega) _ (next_avg (next^[i] s)) ih
  have ham : Monotone (fun i => (a i).toFinset) := by
    apply monotone_nat_of_le_succ
    intro i
    simpa [a, Function.iterate_succ_apply'] using support_mono (a i)
  have hc (i : ℕ) : (a i).toFinset.card ≤ m := by simpa using Finset.card_le_card (hb i)
  let P := fun k => ∃ i, m - (a i).toFinset.card = k
  have hex : ∃ k, P k := ⟨_, 0, rfl⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i + 3, fun j => ?_⟩
  have hmin := Nat.find_min' hex (show P (m - (a (i + j)).toFinset.card) from ⟨i + j, rfl⟩)
  have hle := ham (Nat.le_add_right i j)
  have hcard : (a (i + j)).toFinset.card ≤ (a i).toFinset.card := by
    have := hc i
    have := hc (i + j)
    omega
  have he := Finset.eq_of_subset_of_card_le hle hcard
  simpa [a, ← Function.iterate_add_apply, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
    he.symm

-- Restore the row of counts from its positive excesses, padding with ones.
private def pack (n : ℕ) (c : Multiset ℕ) : Multiset ℕ :=
  c.map Nat.succ + replicate (n - c.card) 1

private theorem freq_keys (r : Finset ℕ) (a : Multiset ℕ) (ha : a.toFinset ⊆ r) :
    freq (r.val + a) = pack r.card (freq a) := by
  have has : a ⊆ r.val := fun _ hx => ha (mem_toFinset.mpr hx)
  simp only [freq, has.dedup_add_left, dedup_eq_self.mpr r.nodup]
  let b := r \ a.toFinset
  have hr : a.dedup + b.val = r.val := by
    change a.toFinset.val + (r \ a.toFinset).val = _
    rw [Finset.sdiff_val, add_tsub_cancel_of_le (Finset.val_le_iff.mpr ha)]
  have hm : r.val.map (fun x => (r.val + a).count x) = r.val.map (fun x => (a.count x).succ) := by
    apply map_congr rfl
    intro x hx
    have h1 := nodup_iff_count_le_one.mp r.nodup x
    have h2 := count_pos.mpr hx
    simp only [count_add]
    omega
  rw [hm, ← hr, map_add]
  simp only [pack, map_map, card_map]
  congr 1
  have hz (x : ℕ) (hx : x ∈ b.val) : a.count x = 0 := by
    exact count_eq_zero.mpr (fun h => (Finset.mem_sdiff.mp hx).2 (mem_toFinset.mpr h))
  rw [show b.val.map (fun x => (a.count x).succ) = b.val.map (fun _ => 1) from
    map_congr rfl (fun x hx => by simp [hz x hx]), map_const']
  exact congrArg (replicate · 1) (Finset.card_sdiff_of_subset ha)

private theorem freq_disjoint (a b : Multiset ℕ) (h : Disjoint a b) :
    freq (a + b) = freq a + freq b := by
  simp only [freq, h.dedup_add, map_add, count_add]
  congr 1
  · apply map_congr rfl
    intro x hx
    simp [count_eq_zero.mpr (Multiset.disjoint_left.mp h (mem_dedup.mp hx))]
  · apply map_congr rfl
    intro x hx
    simp [count_eq_zero.mpr (Multiset.disjoint_left.mp h.symm (mem_dedup.mp hx))]

private theorem freq_pack (n : ℕ) (c : Multiset ℕ) (hc : ∀ x ∈ c, 0 < x) :
    freq (pack n c) = hist n c := by
  have hd : Disjoint (c.map Nat.succ) (replicate (n - c.card) 1) := by
    apply Multiset.disjoint_left.mpr
    intro x hx hm
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    have := eq_of_mem_replicate hm
    have := hc y hy
    omega
  rw [pack, freq_disjoint _ _ hd, hist]
  congr 1
  · simp [freq, dedup_map_of_injective Nat.succ_injective, map_map,
      count_map_eq_count' _ _ Nat.succ_injective]
  · generalize n - c.card = k
    by_cases h : k = 0
    · simp [h, freq, extra]
    have he : (replicate k 1).dedup = {1} := by
      apply (Nodup.ext (nodup_dedup _) (nodup_singleton _)).mpr
      simp [mem_replicate, h]
    simp [freq, extra, he, h]

-- Once the support stabilizes, two further inventory steps are determined by the
-- histogram alone. In particular, a repeated histogram gives a repeated inventory.
private theorem short_next (s : Multiset ℕ) (hs : ∀ x ∈ s, 0 < x) : Short next s := by
  obtain ⟨t, ht⟩ := stable_support s hs
  apply short_of_iterate (i := t)
  let a (j : ℕ) := next^[j] (next^[t] s)
  let r := (next^[t] s).toFinset
  have hkeys (j : ℕ) : (a j).dedup = r.val := congrArg Finset.val (ht j)
  have hadd (j : ℕ) : a (j + 1) = r.val + freq (a j) := by
    change next^[j + 1] (next^[t] s) = _
    rw [Function.iterate_succ_apply']
    exact congrArg (· + freq (a j)) (hkeys j)
  have hsub (j : ℕ) : (freq (a j)).toFinset ⊆ r := by
    intro x hx
    have h : x ∈ (a (j + 1)).toFinset := by
      rw [mem_toFinset, hadd, mem_add]
      exact Or.inr (mem_toFinset.mp hx)
    rwa [show (a (j + 1)).toFinset = r from ht _] at h
  let c (j : ℕ) := freq (freq (a j))
  have hpack (j : ℕ) : freq (a (j + 1)) = pack r.card (c j) := by
    rw [hadd, freq_keys _ _ (hsub _)]
  have hh (j : ℕ) : c j = (hist r.card)^[j] (c 0) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change freq (freq (a (j + 1))) = _
      rw [hpack, freq_pack, Function.iterate_succ_apply', ih]
      exact fun _ hx => pos_freq hx
  obtain ⟨j, p, hp, hp', he⟩ := short_hist r.card (c 0)
  have heq : c (j + p) = c j := by rw [hh, hh j, he]
  refine ⟨j + 2, p, hp, hp', ?_⟩
  change a (j + 2 + p) = a (j + 2)
  rw [show j + 2 + p = (j + p) + 1 + 1 by omega, hadd, hpack, heq, hadd (j + 1), hpack]

private def rows (s : Multiset ℕ) : List ℕ × List ℕ :=
  let keys := s.toFinset.sort (· ≤ ·)
  (keys, keys.map (fun v => s.count v))

private def entries (x : List ℕ × List ℕ) : Multiset ℕ := ↑(x.1 ++ x.2)

private theorem step_rows (x : List ℕ × List ℕ) : step x = rows (entries x) := by
  rcases x with ⟨l, m⟩
  simp only [step, rows, entries, List.toFinset_coe, coe_count]

private theorem entries_rows (s : Multiset ℕ) : entries (rows s) = next s := by
  simp only [entries, rows, ← coe_add, ← map_coe, Finset.sort_eq]
  rfl

/-- **Inventory sequences end in short loops.** Let $a_1 < \dots < a_n$ and $b_1, \dots, b_n$ be
positive integers, and iterate the inventory step starting from the pair of rows
$(a_1, \dots, a_n)$ and $(b_1, \dots, b_n)$, where the inventory step replaces a pair of rows by the
increasing list of the distinct integers occurring in either row together with the list of the
number of times each of them occurs in the two rows combined. Then there are a natural number
$t$ and a $p \in \{1, 2, 3\}$ such that the $(t + p)$-th iterate equals the $t$-th iterate.

Resolved in the affirmative: the process is the counting (inventory) map on multisets. Bronstein
and Fraenkel proved that every start is ultimately periodic, and the enumeration of all cycles
(Sauerberg and Shu, re-derived by Cain and Enin) shows that every cycle has length 1, 2 or 3.

Source:
V. Bronstein and A. S. Fraenkel, On a curious property of counting sequences, Amer. Math.
Monthly 101 (1994), https://doi.org/10.1080/00029890.1994.11996991; J. Sauerberg and L. Shu, The
long and the short on counting sequences, Amer. Math. Monthly 104 (1997),
https://doi.org/10.1080/00029890.1997.11990642; O. M. Cain and S. T. Enin, Inventory loops (i.e.
counting sequences) have pre-period 2 max S_1 + 60, arXiv:2004.00209 (2020),
https://arxiv.org/abs/2004.00209. Moved from
`OpenConjectures/Combinatorics/MultisetSequenceLoop`.
-/
theorem conjecture_holds : conjecture := by
  intro keys mults _ hkeys hmults _
  let s := entries (keys, mults)
  have hpos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rcases List.mem_append.mp (mem_coe.mp hx) with h | h
    · exact hkeys _ h
    · exact hmults _ h
  have he (j : ℕ) : step^[j + 1] (keys, mults) = rows (next^[j] s) := by
    induction j with
    | zero => exact step_rows (keys, mults)
    | succ j ih => rw [Function.iterate_succ_apply', ih, step_rows, entries_rows,
        Function.iterate_succ_apply']
  obtain ⟨t, p, hp, hp', ht⟩ := short_next s hpos
  refine ⟨t + 1, p, hp, hp', ?_⟩
  rw [show t + 1 + p = (t + p) + 1 by omega, he, he t, ht]

end MathlibExt.Combinatorics.MultisetSequenceLoopWanted
