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
exceeds its counter by at most the number of decrement rounds, and that for `0 < k`, `k` times
the number of rounds plus the stored mass equals `s.length`. The deterministic error bound
`(s.count x - counter) * k ≤ s.length - mass` follows, and holds for every `k`.

The summary is the one of Misra and Gries, which for parameter `k` keeps at most `k - 1`
counters. For `0 < k`, a decrement round discards `k` distinct occurrences, the unstored item
and one occurrence of each of the `k - 1` stored items, which is where the factor `k` in the
bound comes from.

## References

* J. Misra and D. Gries, *Finding repeated elements*, Sci. Comput. Programming 2 (1982),
  143–152.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

namespace MisraGries

/-- The counter of `x` in a Misra-Gries summary `c`: the total count stored under `x`, which is
`0` when `x` is not stored. Summaries produced by `run` store each item at most once
(`run_nodup`). -/
def counter {X : Type*} [DecidableEq X] (c : List (X × ℕ)) (x : X) : ℕ :=
  ((c.filter (fun e => e.1 = x)).map Prod.snd).sum

/-- The stored mass of a Misra-Gries summary: the sum of its counters. -/
def mass {X : Type*} (c : List (X × ℕ)) : ℕ :=
  (c.map Prod.snd).sum

/-- One Misra-Gries step with parameter `k` (core of ALG-26b). The state is a summary of
stored `(item, counter)` entries plus the number of decrement rounds so far. Processing `x`:
if `x` has a positive counter or fewer than `k - 1` entries are stored, replace the entry of `x`
by one with its counter one higher (a new item enters with counter `1`); otherwise decrement
every stored counter, drop the entries that reach `0`, and record a round. -/
def step {X : Type*} [DecidableEq X] (k : ℕ) (st : List (X × ℕ) × ℕ) (x : X) :
    List (X × ℕ) × ℕ :=
  if 0 < counter st.1 x ∨ st.1.length < k - 1 then
    ((x, counter st.1 x + 1) :: st.1.filter (fun e => e.1 ≠ x), st.2)
  else
    ((st.1.map (fun e => (e.1, e.2 - 1))).filter (fun e => 0 < e.2), st.2 + 1)

/-- Run Misra-Gries over a stream, starting from the empty summary. -/
def run {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) : List (X × ℕ) × ℕ :=
  s.foldl (step k) ([], 0)

section Lemmas

variable {X : Type*} [DecidableEq X]

/-- The increment branch of `step`. -/
private def incr (c : List (X × ℕ)) (x : X) : List (X × ℕ) :=
  (x, counter c x + 1) :: c.filter (fun e => e.1 ≠ x)

/-- The decrement branch of `step`. -/
private def decr (c : List (X × ℕ)) : List (X × ℕ) :=
  (c.map (fun e => (e.1, e.2 - 1))).filter (fun e => 0 < e.2)

private theorem step_eq (k : ℕ) (st : List (X × ℕ) × ℕ) (x : X) :
    step k st x =
      if 0 < counter st.1 x ∨ st.1.length < k - 1 then (incr st.1 x, st.2)
      else (decr st.1, st.2 + 1) :=
  rfl

private theorem counter_cons (e : X × ℕ) (c : List (X × ℕ)) (x : X) :
    counter (e :: c) x = (if e.1 = x then e.2 else 0) + counter c x := by
  unfold counter
  by_cases h : e.1 = x <;> simp [h]

omit [DecidableEq X] in
private theorem mass_cons (e : X × ℕ) (c : List (X × ℕ)) :
    mass (e :: c) = e.2 + mass c := by
  simp [mass]

private theorem counter_filter_ne (c : List (X × ℕ)) (x y : X) :
    counter (c.filter (fun e => e.1 ≠ x)) y = if y = x then 0 else counter c y := by
  induction c with
  | nil => simp [counter]
  | cons e c ih =>
    by_cases he : e.1 = x
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, ih, counter_cons]
      by_cases hy : y = x
      · simp [hy]
      · have hey : e.1 ≠ y := fun h => hy (h ▸ he)
        simp [hy, hey]
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = e :: c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, counter_cons, ih, counter_cons]
      by_cases hy : y = x
      · subst hy
        simp [he]
      · simp [hy]

private theorem counter_incr (c : List (X × ℕ)) (x y : X) :
    counter (incr c x) y = if y = x then counter c x + 1 else counter c y := by
  unfold incr
  rw [counter_cons, counter_filter_ne]
  by_cases hy : y = x
  · simp [hy]
  · have hxy : x ≠ y := fun h => hy h.symm
    simp [hy, hxy]

private theorem mass_filter_ne_add (c : List (X × ℕ)) (x : X) :
    mass (c.filter (fun e => e.1 ≠ x)) + counter c x = mass c := by
  induction c with
  | nil => simp [mass, counter]
  | cons e c ih =>
    by_cases he : e.1 = x
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, counter_cons, mass_cons, ite_eq_left he]
      omega
    · have hf : (e :: c).filter (fun e => e.1 ≠ x) = e :: c.filter (fun e => e.1 ≠ x) := by
        simp [he]
      rw [hf, counter_cons, mass_cons, mass_cons, ite_eq_right he]
      omega

private theorem mass_incr (c : List (X × ℕ)) (x : X) :
    mass (incr c x) = mass c + 1 := by
  unfold incr
  rw [mass_cons]
  have h := mass_filter_ne_add c x
  dsimp only
  omega

private theorem exists_mem_of_counter_pos {c : List (X × ℕ)} {x : X}
    (h : 0 < counter c x) : ∃ e ∈ c, e.1 = x := by
  induction c with
  | nil => simp [counter] at h
  | cons e c ih =>
    rw [counter_cons] at h
    by_cases he : e.1 = x
    · exact ⟨e, List.mem_cons_self, he⟩
    · rw [ite_eq_right he] at h
      obtain ⟨e', he', hx⟩ := ih (by omega)
      exact ⟨e', List.mem_cons_of_mem _ he', hx⟩

private theorem counter_eq_zero_of_notMem {c : List (X × ℕ)} {x : X}
    (h : x ∉ c.map Prod.fst) : counter c x = 0 := by
  by_contra hne
  obtain ⟨e, he, hx⟩ := exists_mem_of_counter_pos (Nat.pos_of_ne_zero hne)
  exact h (List.mem_map.mpr ⟨e, he, hx⟩)

private theorem length_incr_le (c : List (X × ℕ)) (x : X) :
    (incr c x).length ≤ c.length + 1 := by
  simp only [incr, List.length_cons]
  have := List.length_filter_le (fun e : X × ℕ => decide (e.1 ≠ x)) c
  omega

private theorem length_incr_le_of_pos {c : List (X × ℕ)} {x : X} (h : 0 < counter c x) :
    (incr c x).length ≤ c.length := by
  simp only [incr, List.length_cons]
  obtain ⟨e, he, hx⟩ := exists_mem_of_counter_pos h
  have : (c.filter (fun e => e.1 ≠ x)).length < c.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨e, he, by simp [hx]⟩
  omega

private theorem pos_incr {c : List (X × ℕ)} (hpos : ∀ e ∈ c, 0 < e.2) (x : X) :
    ∀ e ∈ incr c x, 0 < e.2 := by
  intro e he
  simp only [incr, List.mem_cons, List.mem_filter] at he
  rcases he with rfl | ⟨he, -⟩
  · exact Nat.succ_pos _
  · exact hpos e he

private theorem nodup_incr {c : List (X × ℕ)} (hnd : (c.map Prod.fst).Nodup) (x : X) :
    ((incr c x).map Prod.fst).Nodup := by
  simp only [incr, List.map_cons, List.nodup_cons]
  refine ⟨?_, hnd.sublist ((List.filter_sublist).map _)⟩
  simp

private theorem counter_decr_cons (e : X × ℕ) (c : List (X × ℕ)) (y : X) :
    counter (decr (e :: c)) y = (if e.1 = y then e.2 - 1 else 0) + counter (decr c) y := by
  unfold decr
  by_cases hp : 0 < e.2 - 1
  · rw [List.map_cons, List.filter_cons_of_pos (by simpa using hp), counter_cons]
  · rw [List.map_cons, List.filter_cons_of_neg (by simpa using hp)]
    have h0 : e.2 - 1 = 0 := by omega
    split_ifs <;> simp [h0]

omit [DecidableEq X] in
private theorem mass_decr_cons (e : X × ℕ) (c : List (X × ℕ)) :
    mass (decr (e :: c)) = (e.2 - 1) + mass (decr c) := by
  unfold decr
  by_cases hp : 0 < e.2 - 1
  · rw [List.map_cons, List.filter_cons_of_pos (by simpa using hp), mass_cons]
  · rw [List.map_cons, List.filter_cons_of_neg (by simpa using hp)]
    omega

private theorem counter_decr_le (c : List (X × ℕ)) (y : X) :
    counter (decr c) y ≤ counter c y := by
  induction c with
  | nil => simp [decr, counter]
  | cons e c ih =>
    rw [counter_decr_cons, counter_cons]
    split_ifs <;> omega

private theorem counter_le_decr_add_one {c : List (X × ℕ)} (hnd : (c.map Prod.fst).Nodup)
    (y : X) : counter c y ≤ counter (decr c) y + 1 := by
  induction c with
  | nil => simp [counter]
  | cons e c ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [counter_decr_cons, counter_cons]
    by_cases he : e.1 = y
    · have h0 : counter c y = 0 := counter_eq_zero_of_notMem (he ▸ hnd.1)
      rw [ite_eq_left he, ite_eq_left he, h0]
      omega
    · rw [ite_eq_right he, ite_eq_right he]
      have := ih hnd.2
      omega

omit [DecidableEq X] in
private theorem mass_decr_add_length {c : List (X × ℕ)} (hpos : ∀ e ∈ c, 0 < e.2) :
    mass (decr c) + c.length = mass c := by
  induction c with
  | nil => simp [decr, mass]
  | cons e c ih =>
    rw [mass_decr_cons, mass_cons, List.length_cons]
    have he := hpos e List.mem_cons_self
    have := ih (fun e' he' => hpos e' (List.mem_cons_of_mem _ he'))
    omega

omit [DecidableEq X] in
private theorem length_decr_le (c : List (X × ℕ)) : (decr c).length ≤ c.length := by
  unfold decr
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_map ..))

omit [DecidableEq X] in
private theorem pos_decr (c : List (X × ℕ)) : ∀ e ∈ decr c, 0 < e.2 := by
  intro e he
  simp only [decr, List.mem_filter, decide_eq_true_eq] at he
  exact he.2

omit [DecidableEq X] in
private theorem nodup_decr {c : List (X × ℕ)} (hnd : (c.map Prod.fst).Nodup) :
    ((decr c).map Prod.fst).Nodup := by
  unfold decr
  have hmap : (c.map (fun e : X × ℕ => (e.1, e.2 - 1))).map Prod.fst = c.map Prod.fst := by
    simp [List.map_map, Function.comp_def]
  exact (hmap ▸ hnd).sublist ((List.filter_sublist).map _)

/-- The invariant of the summaries reached by `run`: distinct items, positive counters, and at
most `k - 1` entries. -/
private def Wf (k : ℕ) (c : List (X × ℕ)) : Prop :=
  (c.map Prod.fst).Nodup ∧ (∀ e ∈ c, 0 < e.2) ∧ c.length ≤ k - 1

private theorem wf_step (k : ℕ) (st : List (X × ℕ) × ℕ) (a : X) (h : Wf k st.1) :
    Wf k (step k st a).1 := by
  obtain ⟨hnd, hpos, hlen⟩ := h
  rw [step_eq]
  split_ifs with hc
  · refine ⟨nodup_incr hnd a, pos_incr hpos a, ?_⟩
    rcases hc with hc | hc
    · exact Nat.le_trans (length_incr_le_of_pos hc) hlen
    · have := length_incr_le st.1 a
      dsimp only
      omega
  · exact ⟨nodup_decr hnd, pos_decr _, Nat.le_trans (length_decr_le _) hlen⟩

private theorem wf_fold (k : ℕ) (s : List X) (st : List (X × ℕ) × ℕ) (h : Wf k st.1) :
    Wf k (s.foldl (step k) st).1 := by
  induction s generalizing st with
  | nil => exact h
  | cons a s ih => exact ih _ (wf_step k st a h)

private theorem wf_run (k : ℕ) (s : List X) : Wf k (run k s).1 :=
  wf_fold k s ([], 0) ⟨List.nodup_nil, by simp, by simp⟩

end Lemmas

/-- A run stores each item at most once. -/
theorem run_nodup {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) :
    ((run k s).1.map Prod.fst).Nodup :=
  (wf_run k s).1

/-- Every counter stored by a run is positive. -/
theorem run_counter_pos {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) :
    ∀ e ∈ (run k s).1, 0 < e.2 :=
  (wf_run k s).2.1

/-- A run stores at most `k - 1` entries. -/
theorem run_length_le {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) :
    (run k s).1.length ≤ k - 1 :=
  (wf_run k s).2.2

private theorem step_counter_le_self {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a : X) :
    counter (step k st a).1 a ≤ counter st.1 a + 1 := by
  rw [step_eq]
  split_ifs
  · simp [counter_incr]
  · exact Nat.le_trans (counter_decr_le _ _) (Nat.le_succ _)

private theorem step_counter_le_of_ne {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a x : X) (h : x ≠ a) :
    counter (step k st a).1 x ≤ counter st.1 x := by
  rw [step_eq]
  split_ifs
  · simp [counter_incr, h]
  · exact counter_decr_le _ _

private theorem fold_counter_le {X : Type*} [DecidableEq X]
    (k : ℕ) (s : List X) (st : List (X × ℕ) × ℕ) (x : X) :
    counter (s.foldl (step k) st).1 x ≤ counter st.1 x + s.count x := by
  induction s generalizing st with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [List.count_cons_self]
      have hstep := step_counter_le_self k st x
      have hih := ih (step k st x)
      omega
    · rw [List.count_cons_of_ne (fun h => hxa h.symm)]
      have hstep := step_counter_le_of_ne k st a x hxa
      have hih := ih (step k st a)
      omega

/-- Counters never exceed true frequencies. -/
theorem counter_le_freq {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) (x : X) :
    counter (run k s).1 x ≤ s.count x := by
  have h := fold_counter_le k s ([], 0) x
  simpa [run, counter] using h

private theorem step_ge_self {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a : X) :
    counter st.1 a + 1 + st.2 ≤ counter (step k st a).1 a + (step k st a).2 := by
  rw [step_eq]
  split_ifs with hc
  · simp [counter_incr]
  · have h0 : counter st.1 a = 0 := by omega
    dsimp only
    omega

private theorem step_ge_of_ne {X : Type*} [DecidableEq X]
    (k : ℕ) (st : List (X × ℕ) × ℕ) (a x : X) (h : x ≠ a) (hnd : (st.1.map Prod.fst).Nodup) :
    counter st.1 x + st.2 ≤ counter (step k st a).1 x + (step k st a).2 := by
  rw [step_eq]
  split_ifs
  · simp [counter_incr, h]
  · have := counter_le_decr_add_one hnd x
    dsimp only
    omega

private theorem fold_ge {X : Type*} [DecidableEq X]
    (k : ℕ) (s : List X) (st : List (X × ℕ) × ℕ) (x : X) (hinv : Wf k st.1) :
    s.count x + counter st.1 x + st.2
      ≤ counter (s.foldl (step k) st).1 x + (s.foldl (step k) st).2 := by
  induction s generalizing st with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons]
    have hih := ih (step k st a) (wf_step k st a hinv)
    by_cases hxa : x = a
    · subst hxa
      rw [List.count_cons_self]
      have hstep := step_ge_self k st x
      omega
    · rw [List.count_cons_of_ne (fun h => hxa h.symm)]
      have hstep := step_ge_of_ne k st a x hxa hinv.1
      omega

/-- A frequency exceeds its counter by at most the number of decrement rounds. -/
theorem freq_le_counter_add_rounds {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) (x : X) :
    s.count x ≤ counter (run k s).1 x + (run k s).2 := by
  have h := fold_ge k s ([], 0) x ⟨List.nodup_nil, by simp, by simp⟩
  simpa [run, counter] using h

private theorem step_potential {X : Type*} [DecidableEq X]
    (k : ℕ) (hk : 0 < k) (st : List (X × ℕ) × ℕ) (a : X) (hinv : Wf k st.1) :
    (step k st a).2 * k + mass (step k st a).1 = st.2 * k + mass st.1 + 1 := by
  rw [step_eq]
  split_ifs with hc
  · dsimp only
    rw [mass_incr]
    omega
  · dsimp only
    have hlen : st.1.length = k - 1 := by
      have := hinv.2.2
      omega
    have hm := mass_decr_add_length hinv.2.1
    rw [Nat.add_mul, Nat.one_mul]
    omega

private theorem fold_potential {X : Type*} [DecidableEq X]
    (k : ℕ) (hk : 0 < k) (s : List X) (st : List (X × ℕ) × ℕ) (hinv : Wf k st.1) :
    (s.foldl (step k) st).2 * k + mass (s.foldl (step k) st).1
      = st.2 * k + mass st.1 + s.length := by
  induction s generalizing st with
  | nil => simp
  | cons a s ih =>
    rw [List.foldl_cons, List.length_cons, ih _ (wf_step k st a hinv),
      step_potential k hk st a hinv]
    omega

/-- Each decrement round consumes `k` units of the stream: one unstored item and `k - 1` stored
counts. So `k` times the number of rounds plus the stored mass is the stream length. -/
theorem rounds_mul_add_mass {X : Type*} [DecidableEq X] (k : ℕ) (hk : 0 < k) (s : List X) :
    (run k s).2 * k + mass (run k s).1 = s.length := by
  have h := fold_potential k hk s ([], 0) ⟨List.nodup_nil, by simp, by simp⟩
  simpa [run, mass] using h

/-- Deterministic Misra-Gries error bound: the frequency error times `k` is at most the stream
mass not held in counters. It holds for every `k`, trivially for `k = 0`. -/
theorem error_bound {X : Type*} [DecidableEq X] (k : ℕ) (s : List X) (x : X) :
    (s.count x - counter (run k s).1 x) * k ≤ s.length - mass (run k s).1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h2 := freq_le_counter_add_rounds k s x
  have h3 := rounds_mul_add_mass k hk s
  have herr : s.count x - counter (run k s).1 x ≤ (run k s).2 := by omega
  have hmul := Nat.mul_le_mul_right k herr
  omega

end MisraGries

end Cslib.Algorithms.Lean

end
