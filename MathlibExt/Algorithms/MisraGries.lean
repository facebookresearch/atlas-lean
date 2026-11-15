/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Count

/-!
# Misra-Gries heavy hitters

The Misra-Gries summary with parameter `k` stores at most `k - 1` items, each with a positive
counter. Processing an item increments its counter when the item is stored or a slot is free
(a new item enters with counter `1`); otherwise every stored counter is decremented, the
counters that reach `0` are dropped, and the step counts as a decrement round. The summary is
a list of `(item, counter)` entries, so it is executable for any item type with decidable
equality, and a step reads and rewrites only the stored entries.

For a run over a stream `s`, this module proves that the summary stores each item at most once
and at most `k - 1` items, that counters never exceed true frequencies, that a frequency
exceeds its counter by at most the number of decrement rounds, that `k` times the number of
rounds plus the stored mass equals `s.length`, and hence the deterministic error bound
`(s.count x - counter) * k ≤ s.length - mass`.
-/

@[expose] public section

/-- The counter of `x` in a Misra-Gries summary `c`: the total count stored under `x`, which is
`0` when `x` is not stored. Summaries produced by `mgRun` store each item at most once
(`mgRun_nodup`). -/
def mgCounter {X : Type*} [DecidableEq X] (c : List (X × ℕ)) (x : X) : ℕ :=
  ((c.filter (fun e => e.1 = x)).map Prod.snd).sum

/-- The stored mass of a Misra-Gries summary: the sum of its counters. -/
def mgMass {X : Type*} (c : List (X × ℕ)) : ℕ :=
  (c.map Prod.snd).sum

/-- One Misra-Gries step with parameter `k` (core of ALG-26b). The state is a summary of
stored `(item, counter)` entries plus the number of decrement rounds so far. Processing `x`:
if `x` has a positive counter or fewer than `k - 1` entries are stored, replace the entry of `x`
by one with its counter one higher (a new item enters with counter `1`); otherwise decrement
every stored counter, drop the entries that reach `0`, and record a round. -/
def mgStep {X : Type*} [DecidableEq X] (k : ℕ) (st : List (X × ℕ) × ℕ) (x : X) :
    List (X × ℕ) × ℕ :=
  if 0 < mgCounter st.1 x ∨ st.1.length < k - 1 then
    ((x, mgCounter st.1 x + 1) :: st.1.filter (fun e => e.1 ≠ x), st.2)
  else
    ((st.1.map (fun e => (e.1, e.2 - 1))).filter (fun e => 0 < e.2), st.2 + 1)

/-- Run Misra-Gries over a stream, starting from the empty summary. -/
def mgRun {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) : List (X × ℕ) × ℕ :=
  s.foldl (mgStep k) ([], 0)

section Lemmas

variable {X : Type*} [DecidableEq X]

/-- The increment branch of `mgStep`. -/
private def mgIncr (c : List (X × ℕ)) (x : X) : List (X × ℕ) :=
  (x, mgCounter c x + 1) :: c.filter (fun e => e.1 ≠ x)

/-- The decrement branch of `mgStep`. -/
private def mgDecr (c : List (X × ℕ)) : List (X × ℕ) :=
  (c.map (fun e => (e.1, e.2 - 1))).filter (fun e => 0 < e.2)

private theorem mgStep_eq (k : ℕ) (st : List (X × ℕ) × ℕ) (x : X) :
    mgStep k st x =
      if 0 < mgCounter st.1 x ∨ st.1.length < k - 1 then (mgIncr st.1 x, st.2)
      else (mgDecr st.1, st.2 + 1) :=
  rfl

private theorem mgCounter_cons (e : X × ℕ) (c : List (X × ℕ)) (x : X) :
    mgCounter (e :: c) x = (if e.1 = x then e.2 else 0) + mgCounter c x := by
  unfold mgCounter
  by_cases h : e.1 = x <;> simp [h]

omit [DecidableEq X] in
private theorem mgMass_cons (e : X × ℕ) (c : List (X × ℕ)) :
    mgMass (e :: c) = e.2 + mgMass c := by
  simp [mgMass]

private theorem mgCounter_filter_ne (c : List (X × ℕ)) (x y : X) :
    mgCounter (c.filter (fun e => e.1 ≠ x)) y = if y = x then 0 else mgCounter c y := by
  induction c with
  | nil => simp [mgCounter]
  | cons e c ih =>
    by_cases he : e.1 = x
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, ih, mgCounter_cons]
      by_cases hy : y = x
      · simp [hy]
      · have hey : e.1 ≠ y := fun h => hy (h ▸ he)
        simp [hy, hey]
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = e :: c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, mgCounter_cons, ih, mgCounter_cons]
      by_cases hy : y = x
      · subst hy
        simp [he]
      · simp [hy]

private theorem mgCounter_incr (c : List (X × ℕ)) (x y : X) :
    mgCounter (mgIncr c x) y = if y = x then mgCounter c x + 1 else mgCounter c y := by
  unfold mgIncr
  rw [mgCounter_cons, mgCounter_filter_ne]
  by_cases hy : y = x
  · simp [hy]
  · have hxy : x ≠ y := fun h => hy h.symm
    simp [hy, hxy]

private theorem mgMass_filter_ne_add (c : List (X × ℕ)) (x : X) :
    mgMass (c.filter (fun e => e.1 ≠ x)) + mgCounter c x = mgMass c := by
  induction c with
  | nil => simp [mgMass, mgCounter]
  | cons e c ih =>
    by_cases he : e.1 = x
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, mgCounter_cons, mgMass_cons, ite_eq_left he]
      omega
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = e :: c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, mgCounter_cons, mgMass_cons, mgMass_cons, ite_eq_right he]
      omega

private theorem mgMass_incr (c : List (X × ℕ)) (x : X) :
    mgMass (mgIncr c x) = mgMass c + 1 := by
  unfold mgIncr
  rw [mgMass_cons]
  have h := mgMass_filter_ne_add c x
  dsimp only
  omega

private theorem exists_mem_of_mgCounter_pos {c : List (X × ℕ)} {x : X}
    (h : 0 < mgCounter c x) : ∃ e ∈ c, e.1 = x := by
  induction c with
  | nil => simp [mgCounter] at h
  | cons e c ih =>
    rw [mgCounter_cons] at h
    by_cases he : e.1 = x
    · exact ⟨e, List.mem_cons_self, he⟩
    · rw [ite_eq_right he] at h
      obtain ⟨e', he', hx⟩ := ih (by omega)
      exact ⟨e', List.mem_cons_of_mem _ he', hx⟩

private theorem mgCounter_eq_zero_of_notMem {c : List (X × ℕ)} {x : X}
    (h : x ∉ c.map Prod.fst) : mgCounter c x = 0 := by
  by_contra hne
  obtain ⟨e, he, hx⟩ := exists_mem_of_mgCounter_pos (Nat.pos_of_ne_zero hne)
  exact h (List.mem_map.mpr ⟨e, he, hx⟩)

private theorem length_incr_le (c : List (X × ℕ)) (x : X) :
    (mgIncr c x).length ≤ c.length + 1 := by
  simp only [mgIncr, List.length_cons]
  have := List.length_filter_le (fun e : X × ℕ => decide (e.1 ≠ x)) c
  omega

private theorem length_incr_le_of_pos {c : List (X × ℕ)} {x : X} (h : 0 < mgCounter c x) :
    (mgIncr c x).length ≤ c.length := by
  simp only [mgIncr, List.length_cons]
  obtain ⟨e, he, hx⟩ := exists_mem_of_mgCounter_pos h
  have : (c.filter (fun e => e.1 ≠ x)).length < c.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨e, he, by simp [hx]⟩
  omega

private theorem pos_incr {c : List (X × ℕ)} (hpos : ∀ e ∈ c, 0 < e.2) (x : X) :
    ∀ e ∈ mgIncr c x, 0 < e.2 := by
  intro e he
  simp only [mgIncr, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | ⟨he, -⟩
  · exact Nat.succ_pos _
  · exact hpos e he

private theorem nodup_incr {c : List (X × ℕ)} (hnd : (c.map Prod.fst).Nodup) (x : X) :
    ((mgIncr c x).map Prod.fst).Nodup := by
  simp only [mgIncr, List.map_cons, List.nodup_cons]
  refine ⟨?_, hnd.sublist ((List.filter_sublist).map _)⟩
  simp

private theorem mgCounter_decr_cons (e : X × ℕ) (c : List (X × ℕ)) (y : X) :
    mgCounter (mgDecr (e :: c)) y = (if e.1 = y then e.2 - 1 else 0) + mgCounter (mgDecr c) y := by
  unfold mgDecr
  by_cases hp : 0 < e.2 - 1
  · rw [List.map_cons, List.filter_cons_of_pos (by simpa using hp), mgCounter_cons]
  · rw [List.map_cons, List.filter_cons_of_neg (by simpa using hp)]
    have h0 : e.2 - 1 = 0 := by omega
    split_ifs <;> simp [h0]

omit [DecidableEq X] in
private theorem mgMass_decr_cons (e : X × ℕ) (c : List (X × ℕ)) :
    mgMass (mgDecr (e :: c)) = (e.2 - 1) + mgMass (mgDecr c) := by
  unfold mgDecr
  by_cases hp : 0 < e.2 - 1
  · rw [List.map_cons, List.filter_cons_of_pos (by simpa using hp), mgMass_cons]
  · rw [List.map_cons, List.filter_cons_of_neg (by simpa using hp)]
    omega

private theorem mgCounter_decr_le (c : List (X × ℕ)) (y : X) :
    mgCounter (mgDecr c) y ≤ mgCounter c y := by
  induction c with
  | nil => simp [mgDecr, mgCounter]
  | cons e c ih =>
    rw [mgCounter_decr_cons, mgCounter_cons]
    split_ifs <;> omega

private theorem mgCounter_le_decr_add_one {c : List (X × ℕ)} (hnd : (c.map Prod.fst).Nodup)
    (y : X) : mgCounter c y ≤ mgCounter (mgDecr c) y + 1 := by
  induction c with
  | nil => simp [mgCounter]
  | cons e c ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [mgCounter_decr_cons, mgCounter_cons]
    by_cases he : e.1 = y
    · have h0 : mgCounter c y = 0 := mgCounter_eq_zero_of_notMem (he ▸ hnd.1)
      rw [ite_eq_left he, ite_eq_left he, h0]
      omega
    · rw [ite_eq_right he, ite_eq_right he]
      have := ih hnd.2
      omega

omit [DecidableEq X] in
private theorem mgMass_decr_add_length {c : List (X × ℕ)} (hpos : ∀ e ∈ c, 0 < e.2) :
    mgMass (mgDecr c) + c.length = mgMass c := by
  induction c with
  | nil => simp [mgDecr, mgMass]
  | cons e c ih =>
    rw [mgMass_decr_cons, mgMass_cons, List.length_cons]
    have he := hpos e List.mem_cons_self
    have := ih (fun e' he' => hpos e' (List.mem_cons_of_mem _ he'))
    omega

omit [DecidableEq X] in
private theorem length_decr_le (c : List (X × ℕ)) : (mgDecr c).length ≤ c.length := by
  unfold mgDecr
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_map ..))

omit [DecidableEq X] in
private theorem pos_decr (c : List (X × ℕ)) : ∀ e ∈ mgDecr c, 0 < e.2 := by
  intro e he
  simp only [mgDecr, List.mem_filter, decide_eq_true_eq] at he
  exact he.2

omit [DecidableEq X] in
private theorem nodup_decr {c : List (X × ℕ)} (hnd : (c.map Prod.fst).Nodup) :
    ((mgDecr c).map Prod.fst).Nodup := by
  unfold mgDecr
  have hmap : (c.map (fun e : X × ℕ => (e.1, e.2 - 1))).map Prod.fst = c.map Prod.fst := by
    simp [List.map_map, Function.comp_def]
  exact (hmap ▸ hnd).sublist ((List.filter_sublist).map _)

/-- The invariant of the summaries reached by `mgRun`: distinct items, positive counters, and at
most `k - 1` entries. -/
private def MGInv (k : ℕ) (c : List (X × ℕ)) : Prop :=
  (c.map Prod.fst).Nodup ∧ (∀ e ∈ c, 0 < e.2) ∧ c.length ≤ k - 1

private theorem mgInv_step (k : ℕ) (st : List (X × ℕ) × ℕ) (a : X) (h : MGInv k st.1) :
    MGInv k (mgStep k st a).1 := by
  obtain ⟨hnd, hpos, hlen⟩ := h
  rw [mgStep_eq]
  split_ifs with hc
  · refine ⟨nodup_incr hnd a, pos_incr hpos a, ?_⟩
    rcases hc with hc | hc
    · exact Nat.le_trans (length_incr_le_of_pos hc) hlen
    · have := length_incr_le st.1 a
      dsimp only
      omega
  · exact ⟨nodup_decr hnd, pos_decr _, Nat.le_trans (length_decr_le _) hlen⟩

private theorem mgInv_fold (k : ℕ) (s : List X) (st : List (X × ℕ) × ℕ) (h : MGInv k st.1) :
    MGInv k (s.foldl (mgStep k) st).1 := by
  induction s generalizing st with
  | nil => exact h
  | cons a s ih => exact ih _ (mgInv_step k st a h)

private theorem mgInv_run (k : ℕ) (s : List X) : MGInv k (mgRun k s).1 :=
  mgInv_fold k s ([], 0) ⟨List.nodup_nil, by simp, by simp⟩

end Lemmas

/-- A run stores each item at most once. -/
theorem mgRun_nodup {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) :
    ((mgRun k s).1.map Prod.fst).Nodup :=
  (mgInv_run k s).1

/-- Every counter stored by a run is positive. -/
theorem mgRun_counter_pos {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) :
    ∀ e ∈ (mgRun k s).1, 0 < e.2 :=
  (mgInv_run k s).2.1

/-- A run stores at most `k - 1` entries. -/
theorem mgRun_length_le {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) :
    (mgRun k s).1.length ≤ k - 1 :=
  (mgInv_run k s).2.2

private theorem mgStep_counter_le_self {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a : X) :
    mgCounter (mgStep k st a).1 a ≤ mgCounter st.1 a + 1 := by
  rw [mgStep_eq]
  split_ifs
  · simp [mgCounter_incr]
  · exact Nat.le_trans (mgCounter_decr_le _ _) (Nat.le_succ _)

private theorem mgStep_counter_le_of_ne {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a x : X) (h : x ≠ a) :
    mgCounter (mgStep k st a).1 x ≤ mgCounter st.1 x := by
  rw [mgStep_eq]
  split_ifs
  · simp [mgCounter_incr, h]
  · exact mgCounter_decr_le _ _

private theorem mgFold_counter_le {X : Type*} [DecidableEq X]
    (k : ℕ) (s : List X) (st : List (X × ℕ) × ℕ) (x : X) :
    mgCounter (s.foldl (mgStep k) st).1 x ≤ mgCounter st.1 x + s.count x := by
  induction s generalizing st with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [List.count_cons_self]
      have hstep := mgStep_counter_le_self k st x
      have hih := ih (mgStep k st x)
      omega
    · rw [List.count_cons_of_ne (fun h => hxa h.symm)]
      have hstep := mgStep_counter_le_of_ne k st a x hxa
      have hih := ih (mgStep k st a)
      omega

/-- Counters never exceed true frequencies. -/
theorem mg_le_freq {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) (x : X) :
    mgCounter (mgRun k s).1 x ≤ s.count x := by
  have h := mgFold_counter_le k s ([], 0) x
  simpa [mgRun, mgCounter] using h

private theorem mgStep_ge_self {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a : X) :
    mgCounter st.1 a + 1 + st.2 ≤ mgCounter (mgStep k st a).1 a + (mgStep k st a).2 := by
  rw [mgStep_eq]
  split_ifs with hc
  · simp [mgCounter_incr]
  · have h0 : mgCounter st.1 a = 0 := by omega
    dsimp only
    omega

private theorem mgStep_ge_of_ne {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a x : X) (h : x ≠ a) (hnd : (st.1.map Prod.fst).Nodup) :
    mgCounter st.1 x + st.2 ≤ mgCounter (mgStep k st a).1 x + (mgStep k st a).2 := by
  rw [mgStep_eq]
  split_ifs
  · simp [mgCounter_incr, h]
  · have := mgCounter_le_decr_add_one hnd x
    dsimp only
    omega

private theorem mgFold_ge {X : Type*} [DecidableEq X]
    (k : ℕ) (s : List X) (st : List (X × ℕ) × ℕ) (x : X) (hinv : MGInv k st.1) :
    s.count x + mgCounter st.1 x + st.2
      ≤ mgCounter (s.foldl (mgStep k) st).1 x + (s.foldl (mgStep k) st).2 := by
  induction s generalizing st with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons]
    have hih := ih (mgStep k st a) (mgInv_step k st a hinv)
    by_cases hxa : x = a
    · subst hxa
      rw [List.count_cons_self]
      have hstep := mgStep_ge_self k st x
      omega
    · rw [List.count_cons_of_ne (fun h => hxa h.symm)]
      have hstep := mgStep_ge_of_ne k st a x hxa hinv.1
      omega

/-- A frequency exceeds its counter by at most the number of decrement rounds. -/
theorem freq_le_mg_add_rounds {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) (x : X) :
    s.count x ≤ mgCounter (mgRun k s).1 x + (mgRun k s).2 := by
  have h := mgFold_ge k s ([], 0) x ⟨List.nodup_nil, by simp, by simp⟩
  simpa [mgRun, mgCounter] using h

private theorem mgStep_potential {X : Type*} [DecidableEq X]
    (k : ℕ) (hk : 0 < k) (st : List (X × ℕ) × ℕ) (a : X) (hinv : MGInv k st.1) :
    (mgStep k st a).2 * k + mgMass (mgStep k st a).1 = st.2 * k + mgMass st.1 + 1 := by
  rw [mgStep_eq]
  split_ifs with hc
  · dsimp only
    rw [mgMass_incr]
    omega
  · dsimp only
    have hlen : st.1.length = k - 1 := by
      have := hinv.2.2
      omega
    have hm := mgMass_decr_add_length hinv.2.1
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem mgFold_potential {X : Type*} [DecidableEq X]
    (k : ℕ) (hk : 0 < k) (s : List X) (st : List (X × ℕ) × ℕ) (hinv : MGInv k st.1) :
    (s.foldl (mgStep k) st).2 * k + mgMass (s.foldl (mgStep k) st).1
      = st.2 * k + mgMass st.1 + s.length := by
  induction s generalizing st with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons, List.length_cons, ih _ (mgInv_step k st a hinv),
      mgStep_potential k hk st a hinv]
    omega

/-- Each decrement round consumes `k` units of the stream: one unstored item and `k - 1` stored
counts. So `k` times the number of rounds plus the stored mass is the stream length. -/
theorem mg_rounds_mul_add_mass {X : Type*} [DecidableEq X] (k : ℕ) (hk : 0 < k) (s : List X) :
    (mgRun k s).2 * k + mgMass (mgRun k s).1 = s.length := by
  have h := mgFold_potential k hk s ([], 0) ⟨List.nodup_nil, by simp, by simp⟩
  simpa [mgRun, mgMass] using h

/-- Deterministic Misra-Gries error bound: the frequency error times `k` is at most the stream
mass not held in counters. -/
theorem mg_error_bound {X : Type*} [DecidableEq X]
    (k : ℕ) (hk : 2 ≤ k) (s : List X) (x : X) :
    (s.count x - mgCounter (mgRun k s).1 x) * k ≤ s.length - mgMass (mgRun k s).1 := by
  have h2 := freq_le_mg_add_rounds k s x
  have h3 := mg_rounds_mul_add_mass k (by omega) s
  have herr : s.count x - mgCounter (mgRun k s).1 x ≤ (mgRun k s).2 := by omega
  have hmul := Nat.mul_le_mul_right k herr
  omega

end
