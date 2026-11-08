/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

/-!
# Counting sort

This module implements the stable counting-sort algorithm from Cormen, Leiserson, Rivest, and
Stein, *Introduction to Algorithms*, 4th ed., Section 8.2. Keys inhabit `Fin k`, so every key is a
valid counter index. The implementation counts keys, forms cumulative ending positions, then scans
the input from right to left and writes each record into its final output slot.

The output array is seeded with the input, avoiding an `Inhabited` assumption on record payloads.
The cost model charges one unit for every counter initialization, key evaluation, counter read,
counter write, and output write. Loop control, arithmetic, and proof terms are free.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

/-- Stable counting sort for records whose keys lie in `Fin k`. -/
def countingSort {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) : TimeM Nat (Array α) :=
  let rec initCounters : (n : Nat) → TimeM Nat {a : Array Nat // a.size = n}
    | 0 => pure ⟨#[], rfl⟩
    | n + 1 => do
        let counters ← initCounters n
        ✓
        return ⟨counters.val.push 0, by simp [counters.property]⟩
  let rec countKeys :
      List α → {a : Array Nat // a.size = k} → TimeM Nat {a : Array Nat // a.size = k}
    | [], counters => pure counters
    | x :: xs, counters => do
        ✓
        let q := key x
        let hq : q.val < counters.val.size := counters.property.symm ▸ q.isLt
        ✓
        let count := counters.val[q.val]'hq
        ✓
        let next := counters.val.set q.val (count + 1) hq
        countKeys xs ⟨next, by simp [next, counters.property]⟩
  let rec cumulativeCounts :
      (remaining start : Nat) → start + remaining = k →
        {a : Array Nat // a.size = k} → Nat → TimeM Nat {a : Array Nat // a.size = k}
    | 0, _, _, counters, _ => pure counters
    | remaining + 1, start, hsize, counters, total => do
        let q : Fin k := ⟨start, by omega⟩
        let hq : q.val < counters.val.size := counters.property.symm ▸ q.isLt
        ✓
        let nextTotal := total + counters.val[q.val]'hq
        ✓
        let next := counters.val.set q.val nextTotal hq
        cumulativeCounts remaining (start + 1) (by omega)
          ⟨next, by simp [next, counters.property]⟩ nextTotal
  let rec placeRecords :
      List α → ({a : Array Nat // a.size = k} × Array α) →
        TimeM Nat ({a : Array Nat // a.size = k} × Array α)
    | [], state => pure state
    | x :: xs, state => do
        let state ← placeRecords xs state
        ✓
        let q := key x
        let hq : q.val < state.1.val.size := state.1.property.symm ▸ q.isLt
        ✓
        let ending := state.1.val[q.val]'hq
        ✓
        let position := ending - 1
        let nextCounters := state.1.val.set q.val position hq
        ✓
        return (⟨nextCounters, by simp [nextCounters, state.1.property]⟩,
          state.2.setIfInBounds position x)
  let initialized := initCounters k
  let counted := countKeys input.toList initialized.ret
  let cumulative := cumulativeCounts k 0 (by omega) counted.ret 0
  let placed := placeRecords input.toList (cumulative.ret, input)
  ⟨placed.ret.2, initialized.time + counted.time + cumulative.time + placed.time⟩

private theorem initCounters_ret (k : Nat) :
    (countingSort.initCounters k).ret.val = Array.replicate k 0 := by
  induction k with
  | zero => simp [countingSort.initCounters]
  | succ k ih =>
      simp [countingSort.initCounters, ih, Array.replicate_succ]

private def counterAt {k : Nat} (counters : {a : Array Nat // a.size = k})
    (q : Fin k) : Nat :=
  counters.val[q.val]'(counters.property.symm ▸ q.isLt)

private def keyCount {α : Type u} {k : Nat} (key : α → Fin k)
    (q : Fin k) (xs : List α) : Nat :=
  (xs.filter fun x => key x == q).length

private def keyLessCount {α : Type u} {k : Nat} (key : α → Fin k)
    (bound : Nat) (xs : List α) : Nat :=
  (xs.filter fun x => decide ((key x).val < bound)).length

private theorem keyLessCount_succ {α : Type u} {k : Nat} (key : α → Fin k)
    (q : Fin k) (xs : List α) :
    keyLessCount key (q.val + 1) xs = keyLessCount key q.val xs + keyCount key q xs := by
  induction xs with
  | nil => simp [keyLessCount, keyCount]
  | cons x xs ih =>
      simp only [keyLessCount, keyCount] at ih ⊢
      by_cases h : key x = q
      · subst q
        simp at ih ⊢
        omega
      · have hval : (key x).val ≠ q.val := fun heq => h (Fin.ext heq)
        rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
        · have hsucc : (key x).val < q.val + 1 := by omega
          simp [h, hlt, hsucc] at ih ⊢
          omega
        · have hnot : ¬(key x).val < q.val + 1 := by omega
          have hnotlt : ¬(key x).val < q.val := by omega
          simp [h, hnot, hnotlt] at ih ⊢
          omega

private theorem keyCount_append {α : Type u} {k : Nat} (key : α → Fin k)
    (q : Fin k) (xs ys : List α) :
    keyCount key q (xs ++ ys) = keyCount key q xs + keyCount key q ys := by
  simp [keyCount, List.filter_append]

private theorem keyLessCount_mono {α : Type u} {k : Nat} (key : α → Fin k)
    {a b : Nat} (hab : a ≤ b) (xs : List α) :
    keyLessCount key a xs ≤ keyLessCount key b xs := by
  induction xs with
  | nil => simp [keyLessCount]
  | cons x xs ih =>
      simp only [keyLessCount] at ih
      by_cases ha : (key x).val < a
      · have hb : (key x).val < b := by omega
        simpa [keyLessCount, ha, hb] using Nat.succ_le_succ ih
      · by_cases hb : (key x).val < b
        · simp [keyLessCount, ha, hb]
          omega
        · simpa [keyLessCount, ha, hb] using ih

private theorem keyBlock_end_le_start {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) {q r : Fin k} (hqr : q < r) :
    keyLessCount key q.val xs + keyCount key q xs ≤ keyLessCount key r.val xs := by
  rw [← keyLessCount_succ key q xs]
  apply keyLessCount_mono key (by omega)

private theorem keyLessCount_le_length {α : Type u} {k : Nat} (key : α → Fin k)
    (bound : Nat) (xs : List α) : keyLessCount key bound xs ≤ xs.length := by
  exact List.Sublist.length_le List.filter_sublist

private theorem keyIndex_lt_length {α : Type u} {k : Nat} (key : α → Fin k)
    (full pre suffix : List α) (hfull : full = pre ++ suffix) (q : Fin k)
    (j : Nat) (hj : j < keyCount key q suffix) :
    keyLessCount key q.val full + keyCount key q pre + j < full.length := by
  have hcount : keyCount key q full = keyCount key q pre + keyCount key q suffix := by
    rw [hfull, keyCount_append]
  have hend := keyLessCount_le_length key (q.val + 1) full
  rw [keyLessCount_succ] at hend
  omega

private theorem countKeys_ret_get {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (counters : {a : Array Nat // a.size = k}) (q : Fin k) :
    counterAt (countingSort.countKeys key xs counters).ret q =
      counterAt counters q + keyCount key q xs := by
  induction xs generalizing counters with
  | nil => simp [countingSort.countKeys, counterAt, keyCount]
  | cons x xs ih =>
      simp only [countingSort.countKeys, ret_bind]
      rw [ih]
      by_cases h : key x = q
      · subst q
        simp [counterAt, keyCount]
        omega
      · have hval : (key x).val ≠ q.val := by
          intro heq
          exact h (Fin.ext heq)
        simp only [counterAt, keyCount, List.filter_cons]
        rw [Array.getElem_set]
        simp [h, hval]

private theorem counted_get {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (q : Fin k) :
    counterAt (countingSort.countKeys key xs (countingSort.initCounters k).ret).ret q =
      keyCount key q xs := by
  rw [countKeys_ret_get]
  simp [counterAt, initCounters_ret]

private theorem cumulativeCounts_correct {α : Type u} {k : Nat}
    (key : α → Fin k) (xs : List α) (remaining start : Nat)
    (hsize : start + remaining = k) (counters : {a : Array Nat // a.size = k})
    (total : Nat)
    (hbelow : ∀ q : Fin k, q.val < start →
      counterAt counters q = keyLessCount key (q.val + 1) xs)
    (hat : ∀ q : Fin k, start ≤ q.val → counterAt counters q = keyCount key q xs)
    (htotal : total = keyLessCount key start xs) (q : Fin k) :
    counterAt
        (countingSort.cumulativeCounts remaining start hsize counters total).ret q =
      keyLessCount key (q.val + 1) xs := by
  induction remaining generalizing start counters total with
  | zero =>
      have hq : q.val < start := by omega
      simpa [countingSort.cumulativeCounts] using hbelow q hq
  | succ remaining ih =>
      let current : Fin k := ⟨start, by omega⟩
      let nextTotal := total + counterAt counters current
      let hcounter : current.val < counters.val.size := counters.property.symm ▸ current.isLt
      let nextData := counters.val.set current.val nextTotal hcounter
      let next : {a : Array Nat // a.size = k} :=
        ⟨nextData, by simp [nextData, counters.property]⟩
      have hnextTotal : nextTotal = keyLessCount key (start + 1) xs := by
        rw [show nextTotal = total + counterAt counters current from rfl, htotal,
          hat current (by simp [current])]
        simpa [current] using (keyLessCount_succ key current xs).symm
      have hnextBelow : ∀ r : Fin k, r.val < start + 1 →
          counterAt next r = keyLessCount key (r.val + 1) xs := by
        intro r hr
        by_cases hre : r.val = start
        · have hrcurrent : r = current := Fin.ext hre
          subst r
          simp [counterAt, next, nextData, nextTotal, hnextTotal, current]
        · have hrlt : r.val < start := by omega
          rw [show counterAt next r = counterAt counters r by
            unfold counterAt
            rw [Array.getElem_set]
            simp [current, Ne.symm hre]]
          exact hbelow r hrlt
      have hnextAt : ∀ r : Fin k, start + 1 ≤ r.val →
          counterAt next r = keyCount key r xs := by
        intro r hr
        have hre : current.val ≠ r.val := by simp [current]; omega
        rw [show counterAt next r = counterAt counters r by
          unfold counterAt
          rw [Array.getElem_set]
          simp [hre]]
        exact hat r (by omega)
      have hrec := ih (start := start + 1) (counters := next) (total := nextTotal)
        (by omega) hnextBelow hnextAt hnextTotal
      simpa only [countingSort.cumulativeCounts, ret_bind, next, nextData, nextTotal,
        current, counterAt] using hrec

private theorem cumulative_get {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (q : Fin k) :
    counterAt
        (countingSort.cumulativeCounts k 0 (by omega)
          (countingSort.countKeys key xs (countingSort.initCounters k).ret).ret 0).ret q =
      keyLessCount key (q.val + 1) xs := by
  apply cumulativeCounts_correct key xs k 0 (by omega) _ 0
  · intro r hr
    omega
  · intro r hr
    exact counted_get key xs r
  · change 0 = (List.filter (fun _ : α => false) xs).length
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]
        exact ih

private theorem placeRecords_counter {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (state : {a : Array Nat // a.size = k} × Array α) (q : Fin k) :
    counterAt (countingSort.placeRecords key xs state).ret.1 q =
      counterAt state.1 q - keyCount key q xs := by
  induction xs generalizing state with
  | nil => simp [countingSort.placeRecords, keyCount]
  | cons x xs ih =>
      generalize htail : (countingSort.placeRecords key xs state).ret = tail
      rcases tail with ⟨tailCounters, tailOutput⟩
      have iht := ih state
      rw [htail] at iht
      simp only [countingSort.placeRecords, ret_bind, htail, ret_pure]
      by_cases h : key x = q
      · subst q
        rw [show counterAt
            ⟨tailCounters.val.set (key x).val
                (tailCounters.val[(key x).val]'(tailCounters.property.symm ▸ (key x).isLt) - 1)
                (tailCounters.property.symm ▸ (key x).isLt), by simp [tailCounters.property]⟩
              (key x) = counterAt tailCounters (key x) - 1 by
          simp [counterAt]]
        rw [iht]
        simp [keyCount]
        omega
      · have hval : (key x).val ≠ q.val := fun heq => h (Fin.ext heq)
        rw [show counterAt
            ⟨tailCounters.val.set (key x).val
                (tailCounters.val[(key x).val]'(tailCounters.property.symm ▸ (key x).isLt) - 1)
                (tailCounters.property.symm ▸ (key x).isLt), by simp [tailCounters.property]⟩
              q = counterAt tailCounters q by
          unfold counterAt
          rw [Array.getElem_set]
          simp [hval]]
        rw [iht]
        simp [keyCount, h]

private theorem placeRecords_output_size {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (state : {a : Array Nat // a.size = k} × Array α) :
    (countingSort.placeRecords key xs state).ret.2.size = state.2.size := by
  induction xs generalizing state with
  | nil => simp [countingSort.placeRecords]
  | cons x xs ih =>
      simp [countingSort.placeRecords, ih, Array.size_setIfInBounds]

private theorem placement_position {α : Type u} {k : Nat} (key : α → Fin k)
    (full pre tail : List α) (x : α) (hfull : full = pre ++ x :: tail)
    (state : {a : Array Nat // a.size = k} × Array α)
    (hcounters : ∀ q : Fin k,
      counterAt state.1 q = keyLessCount key (q.val + 1) full) :
    counterAt (countingSort.placeRecords key tail state).ret.1 (key x) - 1 =
      keyLessCount key (key x).val full + keyCount key (key x) pre := by
  rw [placeRecords_counter, hcounters, keyLessCount_succ]
  have hcount : keyCount key (key x) full =
      keyCount key (key x) pre + 1 + keyCount key (key x) tail := by
    rw [hfull, keyCount_append]
    simp [keyCount]
    omega
  omega

private theorem keyBlock_indices_ne {α : Type u} {k : Nat} (key : α → Fin k)
    (full pre suffix : List α) (hfull : full = pre ++ suffix) {q r : Fin k}
    (hqr : q ≠ r) {i j : Nat} (hi : i < keyCount key q suffix)
    (hj : j < keyCount key r suffix) :
    keyLessCount key q.val full + keyCount key q pre + i ≠
      keyLessCount key r.val full + keyCount key r pre + j := by
  have hqcount : keyCount key q full =
      keyCount key q pre + keyCount key q suffix := by
    rw [hfull, keyCount_append]
  have hrcount : keyCount key r full =
      keyCount key r pre + keyCount key r suffix := by
    rw [hfull, keyCount_append]
  have hval : q.val ≠ r.val := fun h => hqr (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · have hblocks := keyBlock_end_le_start key full hlt
    omega
  · have hblocks := keyBlock_end_le_start key full hgt
    omega

private theorem placeRecords_output_get? {α : Type u} {k : Nat} (key : α → Fin k)
    (full pre suffix : List α) (hfull : full = pre ++ suffix)
    (state : {a : Array Nat // a.size = k} × Array α)
    (hcounters : ∀ q : Fin k,
      counterAt state.1 q = keyLessCount key (q.val + 1) full)
    (hout : state.2.size = full.length) (q : Fin k) (j : Nat)
    (hj : j < keyCount key q suffix) :
    (countingSort.placeRecords key suffix state).ret.2[
        keyLessCount key q.val full + keyCount key q pre + j]? =
      (suffix.filter fun x => key x == q)[j]? := by
  induction suffix generalizing pre state q j with
  | nil => simp [keyCount] at hj
  | cons x xs ih =>
      have hfullTail : full = (pre ++ [x]) ++ xs := by
        simpa [List.append_assoc] using hfull
      generalize htail : (countingSort.placeRecords key xs state).ret = tailState
      rcases tailState with ⟨tailCounters, tailOutput⟩
      have htailSize : tailOutput.size = full.length := by
        have hs := placeRecords_output_size key xs state
        rw [htail] at hs
        exact hs.trans hout
      have hposition := placement_position key full pre xs x hfull state hcounters
      rw [htail] at hposition
      change tailCounters.val[(key x).val]'_ - 1 =
        keyLessCount key (key x).val full + keyCount key (key x) pre at hposition
      have houtput :
          (countingSort.placeRecords key (x :: xs) state).ret.2 =
            tailOutput.setIfInBounds
              (keyLessCount key (key x).val full + keyCount key (key x) pre) x := by
        simp only [countingSort.placeRecords, ret_bind, htail, ret_pure]
        rw [hposition]
      rw [houtput]
      by_cases hx : key x = q
      · subst q
        cases j with
        | zero =>
            have hbound := keyIndex_lt_length key full pre (x :: xs) hfull
              (key x) 0 hj
            simp only [Nat.add_zero] at hbound ⊢
            rw [Array.getElem?_setIfInBounds_self]
            simp [htailSize, hbound]
        | succ j =>
            have hjTail : j < keyCount key (key x) xs := by
              simpa [keyCount] using hj
            have iht := ih (pre := pre ++ [x]) (state := state) (q := key x)
              (j := j) hfullTail hcounters hout hjTail
            rw [htail] at iht
            have hne :
                keyLessCount key (key x).val full + keyCount key (key x) pre ≠
                  keyLessCount key (key x).val full + keyCount key (key x) pre + (j + 1) := by
              omega
            rw [Array.getElem?_setIfInBounds_ne hne]
            have hidx :
                keyLessCount key (key x).val full + keyCount key (key x) pre + (j + 1) =
                  keyLessCount key (key x).val full +
                    keyCount key (key x) (pre ++ [x]) + j := by
              simp [keyCount]
              omega
            rw [hidx]
            simpa [keyCount] using iht
      · have hjTail : j < keyCount key q xs := by
          simpa [keyCount, hx] using hj
        have iht := ih (pre := pre ++ [x]) (state := state) (q := q)
          (j := j) hfullTail hcounters hout hjTail
        rw [htail] at iht
        have hxCount : 0 < keyCount key (key x) (x :: xs) := by
          simp [keyCount]
        have hne := keyBlock_indices_ne key full pre (x :: xs) hfull hx
          hxCount hj
        simp only [Nat.add_zero] at hne
        rw [Array.getElem?_setIfInBounds_ne hne]
        simpa [keyCount_append, keyCount, hx] using iht

private theorem placeRecords_output_block {α : Type u} {k : Nat} (key : α → Fin k)
    (full : List α) (state : {a : Array Nat // a.size = k} × Array α)
    (hcounters : ∀ q : Fin k,
      counterAt state.1 q = keyLessCount key (q.val + 1) full)
    (hout : state.2.size = full.length) (q : Fin k) :
    List.take (keyCount key q full)
        (List.drop (keyLessCount key q.val full)
          (countingSort.placeRecords key full state).ret.2.toList) =
      full.filter fun x => key x == q := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases hi : i < keyCount key q full
  · simp only [hi, ↓reduceIte, List.getElem?_drop, Array.getElem?_toList]
    simpa only [keyCount, List.filter_nil, List.length_nil, Nat.add_zero] using
      placeRecords_output_get? key full [] full (by simp) state hcounters hout q i hi
  · simp only [hi, ↓reduceIte]
    exact (List.getElem?_eq_none (by simpa [keyCount] using Nat.le_of_not_gt hi)).symm

private theorem countingSort_output_block {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) (q : Fin k) :
    List.take (keyCount key q input.toList)
        (List.drop (keyLessCount key q.val input.toList)
          (countingSort key input).ret.toList) =
      input.toList.filter fun x => key x == q := by
  unfold countingSort
  apply placeRecords_output_block
  · intro r
    exact cumulative_get key input.toList r
  · exact Array.length_toList

private theorem countingSort_size {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) : (countingSort key input).ret.size = input.size := by
  unfold countingSort
  exact placeRecords_output_size key input.toList _

private theorem keyLessCount_top {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) : keyLessCount key k xs = xs.length := by
  induction xs with
  | nil => simp [keyLessCount]
  | cons x xs ih =>
      simp only [keyLessCount] at ih ⊢
      simp

private def bucketedList {α : Type u} {k : Nat} (key : α → Fin k)
    (bound : Nat) (xs : List α) : List α :=
  (List.range bound).flatMap fun q => xs.filter fun x => decide ((key x).val = q)

private theorem countingSort_take_prefix {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) (bound : Nat) (hbound : bound ≤ k) :
    List.take (keyLessCount key bound input.toList) (countingSort key input).ret.toList =
      bucketedList key bound input.toList := by
  induction bound with
  | zero => simp [keyLessCount, bucketedList]
  | succ bound ih =>
      let q : Fin k := ⟨bound, by omega⟩
      rw [show bound + 1 = q.val + 1 by rfl, keyLessCount_succ key q]
      rw [List.take_add, ih (by omega), countingSort_output_block key input q]
      simp [bucketedList, List.range_succ, q]
      apply List.filter_congr
      intro x hx
      rw [Bool.beq_eq_decide_eq]
      simp only [Fin.ext_iff]

private theorem countingSort_ret_eq_bucketedList {α : Type u} {k : Nat}
    (key : α → Fin k) (input : Array α) :
    (countingSort key input).ret.toList = bucketedList key k input.toList := by
  have hprefix := countingSort_take_prefix key input k (by omega)
  rw [keyLessCount_top] at hprefix
  rw [Array.length_toList] at hprefix
  rw [← countingSort_size key input] at hprefix
  have hsizeLength : (countingSort key input).ret.size =
      (countingSort key input).ret.toList.length := Array.length_toList.symm
  rw [hsizeLength, List.take_length] at hprefix
  exact hprefix

private theorem range_flatMap_if_eq_nil {α : Type u} (xs : List α) (bound q : Nat)
    (hq : bound ≤ q) :
    (List.range bound).flatMap (fun i => if i = q then xs else []) = [] := by
  induction bound with
  | zero => simp
  | succ bound ih =>
      rw [List.range_succ, List.flatMap_append]
      have hne : bound ≠ q := by omega
      simp [ih (by omega), hne]

private theorem range_flatMap_if_eq {α : Type u} (xs : List α) (bound q : Nat)
    (hq : q < bound) :
    (List.range bound).flatMap (fun i => if i = q then xs else []) = xs := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      rw [List.range_succ, List.flatMap_append]
      by_cases hlt : q < bound
      · have hne : bound ≠ q := by omega
        simp [ih hlt, hne]
      · have heq : q = bound := by omega
        subst q
        rw [range_flatMap_if_eq_nil xs bound bound (by omega)]
        simp

private theorem filter_key_bucket {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (i : Nat) (q : Fin k) :
    (xs.filter fun x => decide ((key x).val = i)).filter (fun x => key x == q) =
      if i = q.val then xs.filter (fun x => key x == q) else [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hi : (key x).val = i
      · by_cases hq : key x = q
        · subst q
          simp [hi, ih]
        · have hne : i ≠ q.val := by
            intro h
            exact hq (Fin.ext (hi.trans h))
          simp [hi, hq, hne, ih]
      · by_cases hq : key x = q
        · subst q
          have hne : i ≠ (key x).val := by omega
          simp [hi, hne, ih]
        · simp [hi, hq, ih]

private theorem bucketedList_filter {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (q : Fin k) :
    (bucketedList key k xs).filter (fun x => key x == q) =
      xs.filter fun x => key x == q := by
  rw [bucketedList, List.filter_flatMap]
  simp_rw [filter_key_bucket key xs]
  exact range_flatMap_if_eq _ k q.val q.isLt

private theorem append_cons_perm_cons_append {α : Type u} (pre post : List α) (x : α) :
    List.Perm (pre ++ x :: post) (x :: pre ++ post) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      exact (ih.cons a).trans (List.Perm.swap x a (pre ++ post))

private theorem bucketedList_succ {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (bound : Nat) :
    bucketedList key (bound + 1) xs =
      bucketedList key bound xs ++ xs.filter (fun x => decide ((key x).val = bound)) := by
  simp [bucketedList, List.range_succ]

private theorem bucketedList_cons_of_le {α : Type u} {k : Nat} (key : α → Fin k)
    (x : α) (xs : List α) (bound : Nat) (hbound : bound ≤ (key x).val) :
    bucketedList key bound (x :: xs) = bucketedList key bound xs := by
  induction bound with
  | zero => simp [bucketedList]
  | succ bound ih =>
      have hne : (key x).val ≠ bound := by omega
      rw [bucketedList_succ, bucketedList_succ, ih (by omega)]
      simp [hne]

private theorem bucketedList_cons_perm {α : Type u} {k : Nat} (key : α → Fin k)
    (x : α) (xs : List α) (bound : Nat) (hbound : (key x).val < bound) :
    List.Perm (bucketedList key bound (x :: xs))
      (x :: bucketedList key bound xs) := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      by_cases hlt : (key x).val < bound
      · have hne : (key x).val ≠ bound := by omega
        have hp := List.Perm.append_right
          (xs.filter fun y => decide ((key y).val = bound)) (ih hlt)
        rw [bucketedList_succ, bucketedList_succ]
        simpa [hne] using hp
      · have heq : (key x).val = bound := by omega
        have hprefix := bucketedList_cons_of_le key x xs bound (by omega)
        have hp := append_cons_perm_cons_append (bucketedList key bound xs)
          (xs.filter fun y => decide ((key y).val = bound)) x
        rw [bucketedList_succ, bucketedList_succ, hprefix]
        simp [heq]

private theorem bucketedList_perm {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) : List.Perm (bucketedList key k xs) xs := by
  induction xs with
  | nil => simp [bucketedList]
  | cons x xs ih =>
      exact (bucketedList_cons_perm key x xs k (key x).isLt).trans (ih.cons x)

private theorem mem_key_bucket {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (i : Nat) {x : α}
    (hx : x ∈ xs.filter fun y => decide ((key y).val = i)) : (key x).val = i := by
  have hp := (List.mem_filter.mp hx).2
  exact of_decide_eq_true hp

private theorem key_bucket_pairwise {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) (i : Nat) :
    List.Pairwise (fun x y => key x ≤ key y)
      (xs.filter fun x => decide ((key x).val = i)) := by
  rw [List.pairwise_iff_getElem]
  intro m n hm hn hmn
  have hmKey := List.getElem_filter hm
  have hnKey := List.getElem_filter hn
  apply Fin.mk_le_mk.mpr
  have hmVal : (key (xs.filter (fun x => decide ((key x).val = i)))[m]).val = i :=
    of_decide_eq_true hmKey
  have hnVal : (key (xs.filter (fun x => decide ((key x).val = i)))[n]).val = i :=
    of_decide_eq_true hnKey
  omega

private theorem bucketedList_pairwise {α : Type u} {k : Nat} (key : α → Fin k)
    (xs : List α) :
    List.Pairwise (fun x y => key x ≤ key y) (bucketedList key k xs) := by
  rw [bucketedList, List.pairwise_flatMap]
  constructor
  · intro i hi
    exact key_bucket_pairwise key xs i
  · apply List.pairwise_lt_range.imp
    intro i j hij x hx y hy
    have hxi := mem_key_bucket key xs i hx
    have hyj := mem_key_bucket key xs j hy
    apply Fin.mk_le_mk.mpr
    omega

/-- Counting sort returns a sorted, stable permutation of the input records. -/
theorem countingSort_correct {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) :
    List.Pairwise (fun x y => key x ≤ key y) (countingSort key input).ret.toList ∧
      List.Perm (countingSort key input).ret.toList input.toList ∧
      ∀ q : Fin k,
        (countingSort key input).ret.toList.filter (fun x => key x == q) =
          input.toList.filter fun x => key x == q := by
  rw [countingSort_ret_eq_bucketedList]
  exact ⟨bucketedList_pairwise key input.toList, bucketedList_perm key input.toList,
    bucketedList_filter key input.toList⟩

/-- Counting sort uses at most `7 * n + 3 * k` charged operations. -/
theorem countingSort_time {α : Type u} {k : Nat} (key : α → Fin k)
    (input : Array α) :
    (countingSort key input).time ≤ 7 * input.size + 3 * k := by
  unfold countingSort
  have init_time : ∀ n, (countingSort.initCounters n).time = n := by
    intro n
    induction n with
    | zero => simp [countingSort.initCounters]
    | succ n ih => simp [countingSort.initCounters, ih]
  have count_time : ∀ (xs : List α) counters,
      (countingSort.countKeys key xs counters).time = 3 * xs.length := by
    intro xs
    induction xs with
    | nil => intro counters; simp [countingSort.countKeys]
    | cons x xs ih =>
        intro counters
        simp [countingSort.countKeys, ih]
        omega
  have cumulative_time : ∀ (remaining start : Nat) (hsize : start + remaining = k)
      (counters : {a : Array Nat // a.size = k}) (total : Nat),
      (countingSort.cumulativeCounts remaining start hsize counters total).time =
        2 * remaining := by
    intro remaining
    induction remaining with
    | zero => intro start hsize counters total; simp [countingSort.cumulativeCounts]
    | succ remaining ih =>
        intro start hsize counters total
        simp [countingSort.cumulativeCounts, ih]
        omega
  have place_time : ∀ (xs : List α) state,
      (countingSort.placeRecords key xs state).time = 4 * xs.length := by
    intro xs
    induction xs with
    | nil => intro state; simp [countingSort.placeRecords]
    | cons x xs ih =>
        intro state
        simp [countingSort.placeRecords, ih]
        omega
  dsimp only
  rw [init_time, count_time, cumulative_time, place_time]
  simp only [Array.length_toList]
  omega

end Cslib.Algorithms.Lean.TimeM
