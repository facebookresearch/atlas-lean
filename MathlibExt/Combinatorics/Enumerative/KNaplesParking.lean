/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Equiv.Basic

/-!
# Moving a parked car under the Naples rule

Moving a parked car to an earlier vacant spot preserves the success of the remaining cars.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The $k$-Naples rule.** On the spots $1, \dots, n$, when the spots in a list $O$ of natural
numbers are occupied, a car preferring $a$ parks in $a$ if $a$ is free; otherwise in the first
free spot among those of $a - 1, \dots, a - k$ that are at least $1$, checked in decreasing
order; otherwise in the first free spot among $a + 1, \dots, n$, checked in increasing order.
The car cannot park if none of these is free, or if $a$ is not one of the spots $1, \dots, n$.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public def naplesSpot (n k : ℕ) (occ : List ℕ) (a : ℕ) : Option ℕ :=
  if ¬ (1 ≤ a ∧ a ≤ n) then none else
  if a ∉ occ then some a else
    match ((List.range k).map fun j => a - (j + 1)).find? (fun s => decide (1 ≤ s ∧ s ∉ occ)) with
    | some s => some s
    | none => (List.range' (a + 1) (n - a)).find? (fun s => decide (s ∉ occ))

/-- **Naples parking.** Starting from a list of occupied spots, cars with preferences
$a_1, \dots, a_m \in \mathbb{N}$ arrive in order, and each takes the spot given by the $k$-Naples
rule on the spots $1, \dots, n$ for the spots occupied when it arrives. If every car parks, the
result is the final list of occupied spots: the spots of the cars, most recent first, followed by
the initially occupied spots. If some car cannot park, there is no result.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 1. -/
public def naplesPark (n k : ℕ) : List ℕ → List ℕ → Option (List ℕ)
  | occ, [] => some occ
  | occ, a :: as => (naplesSpot n k occ a).bind fun s => naplesPark n k (s :: occ) as

end

namespace naplesPark_drop_set_isSome

private def Free (n : ℕ) (occ : List ℕ) (s : ℕ) : Prop :=
  1 ≤ s ∧ s ≤ n ∧ s ∉ occ

private structure Choice (n k : ℕ) (occ : List ℕ) (a s : ℕ) : Prop where
  free : Free n occ s
  reach : a - k ≤ s
  back : ∀ t, Free n occ t → a - k ≤ t → t ≤ a → t ≤ s ∧ s ≤ a
  forward : ∀ t, Free n occ t → a < t → s ≤ t

/-- A successful search respects the priority in each direction. A failed search means
every free spot lies below the backward limit. -/
private theorem spot_spec {n k a : ℕ} (occ : List ℕ) (ha : 1 ≤ a ∧ a ≤ n) :
    match naplesSpot n k occ a with
    | some s => Choice n k occ a s
    | none => ∀ t, Free n occ t → t < a - k := by
  unfold naplesSpot
  rw [ite_eq_right (not_not_intro ha)]
  by_cases haocc : a ∈ occ
  · rw [ite_eq_right (not_not_intro haocc)]
    let b (j : ℕ) := a - (j + 1)
    cases hb : ((List.range k).map b).find? (fun s => decide (1 ≤ s ∧ s ∉ occ)) with
    | some s =>
      have hfirst : (1 ≤ s ∧ s ∉ occ) ∧ ∃ i, a - (i + 1) = s ∧ i < k ∧
          ∀ j < i, a - (j + 1) = 0 ∨ a - (j + 1) ∈ occ := by
        simpa [b] using List.find?_eq_some_iff_getElem.mp hb
      obtain ⟨⟨hs, hfree⟩, i, heq, hi, hprev⟩ := hfirst
      refine ⟨⟨hs, by omega, hfree⟩, by omega, ?_, fun _ _ ht => by omega⟩
      intro t ht hlo hhi
      obtain ⟨htpos, _, htfree⟩ := ht
      have hne : t ≠ a := fun h => htfree (h ▸ haocc)
      refine ⟨?_, by omega⟩
      by_contra! hlt
      have heq' : a - (a - t - 1 + 1) = t := by omega
      have := hprev (a - t - 1) (by omega)
      simp [heq', htfree, show t ≠ 0 by omega] at this
    | none =>
      have back_full (t : ℕ) (ht : Free n occ t) (hlo : a - k ≤ t) : a < t := by
        obtain ⟨htpos, _, htfree⟩ := ht
        by_contra! hle
        have hne : t ≠ a := fun h => htfree (h ▸ haocc)
        have heq : b (a - t - 1) = t := by dsimp [b]; omega
        have hmem : t ∈ (List.range k).map b :=
          List.mem_map.mpr ⟨_, List.mem_range.mpr (by omega), heq⟩
        simpa [htpos, htfree] using List.find?_eq_none.mp hb t hmem
      cases hfwd : (List.range' (a + 1) (n - a)).find? (fun s => decide (s ∉ occ)) with
      | none =>
        intro t ht
        by_contra! hlo
        have hlt := back_full t ht hlo
        obtain ⟨_, htn, htfree⟩ := ht
        have hmem : t ∈ List.range' (a + 1) (n - a) :=
          List.mem_range'.mpr ⟨t - (a + 1), by omega, by simp; omega⟩
        simpa [htfree] using List.find?_eq_none.mp hfwd t hmem
      | some s =>
        have hfirst : s ∉ occ ∧ ∃ i, a + 1 + i = s ∧ i < n - a ∧
            ∀ j < i, a + 1 + j ∈ occ := by
          simpa using List.find?_eq_some_iff_getElem.mp hfwd
        obtain ⟨hs, i, heq, hi, hprev⟩ := hfirst
        refine ⟨⟨by omega, by omega, hs⟩, by omega, ?_, ?_⟩
        · intro t ht hlo hhi
          exact (not_lt_of_ge hhi (back_full t ht hlo)).elim
        · intro t ht hlt
          by_contra! hgt
          have heq' : a + 1 + (t - (a + 1)) = t := by omega
          exact ht.2.2 (heq' ▸ hprev _ (by omega))
  · rw [ite_eq_left haocc]
    exact ⟨⟨ha.1, ha.2, haocc⟩, by omega, fun _ _ _ ht => ⟨ht, le_rfl⟩,
      fun _ _ ht => ht.le⟩

/-- The permutation matches each free spot to a free spot at least as far right. -/
private def Matches (n : ℕ) (old new : List ℕ) (e : Equiv.Perm ℕ) : Prop :=
  ∀ t, Free n old t → t ≤ e t ∧ Free n new (e t)

private theorem matches_cons {n k a x y : ℕ} {old new : List ℕ} {e : Equiv.Perm ℕ}
    (h : Matches n old new e) (hx : Choice n k old a x) (hy : Choice n k new a y) :
    Matches n (x :: old) (y :: new) (e.trans (Equiv.swap y (e x))) := by
  intro t ⟨htpos, htn, htfree⟩
  simp only [List.mem_cons, not_or] at htfree
  obtain ⟨htx, htold⟩ := htfree
  have ht : Free n old t := ⟨htpos, htn, htold⟩
  obtain ⟨htle, htnew⟩ := h t ht
  obtain ⟨hxle, hxnew⟩ := h x hx.free
  have hne := e.injective.ne htx
  by_cases hty : e t = y
  · -- The new car took t's match. Give t the old car's unused match.
    rw [Equiv.trans_apply, hty, Equiv.swap_apply_left]
    refine ⟨?_, hxnew.1, hxnew.2.1, List.not_mem_cons_of_ne_of_not_mem (by grind) hxnew.2.2⟩
    by_contra! hlt
    have hlower := hx.reach
    have hat : a < t := by
      by_contra! hta
      have := (hx.back t ht (by omega) hta).1
      omega
    by_cases hleft : e x ≤ a
    · have := (hy.back (e x) hxnew (by omega) hleft).2
      omega
    · have := hy.forward (e x) hxnew (by omega)
      omega
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hty hne]
    exact ⟨htle, htnew.1, htnew.2.1, List.not_mem_cons_of_ne_of_not_mem hty htnew.2.2⟩

private theorem park_of_matches {n k : ℕ} (prefs : List ℕ) {old new : List ℕ}
    {e : Equiv.Perm ℕ} (hm : Matches n old new e)
    (ha : ∀ a ∈ prefs, 1 ≤ a ∧ a ≤ n) (hrun : (naplesPark n k old prefs).isSome) :
    (naplesPark n k new prefs).isSome := by
  induction prefs generalizing old new e with
  | nil => rfl
  | cons a prefs ih =>
    have hvalid := ha a List.mem_cons_self
    have hx := spot_spec (k := k) old hvalid
    have hy := spot_spec (k := k) new hvalid
    cases hs : naplesSpot n k old a with
    | none => simp [naplesPark, hs] at hrun
    | some x =>
      rw [hs] at hx
      obtain ⟨hle, hfree⟩ := hm x hx.free
      cases hs' : naplesSpot n k new a with
      | none =>
        rw [hs'] at hy
        exact (not_lt_of_ge (hx.reach.trans hle) (hy _ hfree)).elim
      | some y =>
        rw [hs'] at hy
        simp only [naplesPark, hs, Option.bind_some] at hrun
        simpa only [naplesPark, hs', Option.bind_some] using
          ih (matches_cons hm hx hy) (fun t ht => ha t (List.mem_cons_of_mem _ ht)) hrun

private theorem park_append (n k : ℕ) (old as bs : List ℕ) :
    naplesPark n k old (as ++ bs) =
      (naplesPark n k old as).bind (fun occ => naplesPark n k occ bs) := by
  induction as generalizing old with
  | nil => rfl
  | cons a as ih => simp [naplesPark, Option.bind_assoc, ih]

/-- Read the occupied list of a successful run as its initial list preceded by one
new spot per preference, in reverse arrival order. -/
private theorem park_result {n k : ℕ} (prefs : List ℕ) {old final : List ℕ}
    (ha : ∀ a ∈ prefs, 1 ≤ a ∧ a ≤ n) (hd : naplesPark n k old prefs = some final)
    (hn : old.Nodup) (hb : ∀ s ∈ old, s ≤ n) :
    ∃ ds : List ℕ, ds.length = prefs.length ∧ final = ds.reverse ++ old ∧
      final.Nodup ∧ ∀ s ∈ final, s ≤ n := by
  induction prefs generalizing old with
  | nil =>
    obtain rfl : old = final := Option.some.inj hd
    exact ⟨[], rfl, rfl, hn, hb⟩
  | cons a prefs ih =>
    obtain ⟨s, hs, hrun⟩ := Option.bind_eq_some_iff.mp hd
    have hc := spot_spec (k := k) old (ha a List.mem_cons_self)
    rw [hs] at hc
    obtain ⟨ds, hlen, heq, hnd, hbound⟩ := ih
      (fun t ht => ha t (List.mem_cons_of_mem _ ht)) hrun (hn.cons hc.free.2.2)
      (fun t ht => (List.mem_cons.mp ht).elim (fun h => h ▸ hc.free.2.1) (hb t))
    exact ⟨s :: ds, by simp [hlen], by simpa using heq, hnd, hbound⟩

private theorem matches_set {n l q : ℕ} {ds : List ℕ} (hl : l < ds.length)
    (hn : ds.Nodup) (hb : ds[l] ≤ n) (hq : Free n ds q) (hlt : q < ds[l]) :
    Matches n ds.reverse (ds.set l q) (Equiv.swap q ds[l]) := by
  let e := Equiv.swap q ds[l]
  have hset : ds.set l q = ds.map e := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    have hjlen : j < ds.length := by simpa using hj
    rw [List.getElem_set, List.getElem_map]
    by_cases heq : l = j
    · subst j
      simp [e]
    · have hjq : ds[j] ≠ q := fun h => hq.2.2 (h ▸ List.getElem_mem hjlen)
      have hjp : ds[j] ≠ ds[l] := hn.getElem_inj_iff.ne.mpr (Ne.symm heq)
      simp [heq, e, Equiv.swap_apply_of_ne_of_ne hjq hjp]
  intro t ⟨htpos, htn, hfree⟩
  replace hfree : t ∉ ds := by simpa using hfree
  have htp : t ≠ ds[l] := fun h => hfree (h ▸ List.getElem_mem hl)
  have hbounds : t ≤ e t ∧ e t ≤ n := by
    by_cases htq : t = q
    · simpa [htq, e] using And.intro hlt.le hb
    · simp [e, Equiv.swap_apply_of_ne_of_ne htq htp, htn]
  refine ⟨hbounds.1, htpos.trans hbounds.1, hbounds.2, ?_⟩
  rw [hset]
  intro hmem
  obtain ⟨u, hu, heq⟩ := List.mem_map.mp hmem
  exact hfree (e.injective heq ▸ hu)

end naplesPark_drop_set_isSome

open naplesPark_drop_set_isSome in
/-- **Remaining cars still park after moving a car to an earlier spot.** Let $(a_1, \dots, a_n)$
be a parking preference with $1 \le a_j \le n$ for every $j$, with which all $n$ cars, arriving in
order into an empty lot, park under the $k$-Naples rule on the spots $1, \dots, n$, car $j$ in
spot $d_j$. Let $1 \le l \le i \le n$, and let $q$ be a spot with $1 \le q < d_l$ and $q \ne d_j$
for every $j \le i$ with $j \ne l$. If exactly the spots $d_1, \dots, d_i$, with $d_l$ replaced
by $q$, are occupied, then the remaining cars $a_{i+1}, \dots, a_n$, arriving in order, all park
under the $k$-Naples rule.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Lemma 2.3. -/
public theorem naplesPark_drop_set_isSome {n k i l q : ℕ} {α : Fin n → ℕ}
    {d : List ℕ} (hα : ∀ j, 1 ≤ α j ∧ α j ≤ n)
    (hd : naplesPark n k [] (List.ofFn α) = some d.reverse) (hl : l < i) (hi : i ≤ n)
    (hq : 1 ≤ q) (hql : q < d.getD l 0) (hqd : ∀ j < i, j ≠ l → d.getD j 0 ≠ q) :
    (naplesPark n k ((d.take i).set l q) ((List.ofFn α).drop i)).isSome := by
  let prefs := List.ofFn α
  have hvalid (a) (ha : a ∈ prefs) : 1 ≤ a ∧ a ≤ n := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact hα j
  change naplesPark n k [] prefs = some d.reverse at hd
  rw [← List.take_append_drop i prefs, park_append] at hd
  obtain ⟨occ, hstart, htail⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨ds, hlen, hocc, hn, hb⟩ := park_result (prefs.take i)
    (fun a ha => hvalid a (List.mem_of_mem_take ha)) hstart (by simp) (by simp)
  simp only [List.append_nil] at hocc
  subst occ
  have hav (a) (ha : a ∈ prefs.drop i) := hvalid a (List.mem_of_mem_drop ha)
  obtain ⟨rest, _, hfinal, _, _⟩ := park_result _ hav htail hn hb
  have hd' : d = ds ++ rest := by simpa using congrArg List.reverse hfinal
  have hlen' : ds.length = i := by simpa [prefs, List.length_take, Nat.min_eq_left hi] using hlen
  have htake : d.take i = ds := by rw [hd', ← hlen', List.take_left]
  have hget (j) (hj : j < ds.length) : d.getD j 0 = ds[j] := by
    rw [hd', List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj]
  have hld : l < ds.length := by omega
  have hlt := (hget l hld) ▸ hql
  have hfree : Free n ds q := by
    refine ⟨hq, hlt.le.trans (hb _ (List.mem_reverse.mpr (List.getElem_mem hld))), ?_⟩
    intro hmem
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
    by_cases hjl : j = l
    · subst j
      omega
    · exact hqd j (by omega) hjl ((hget j hj).trans heq)
  rw [htake]
  exact park_of_matches (prefs.drop i)
    (matches_set hld (List.nodup_reverse.mp hn) (hb _ (by simp)) hfree hlt)
    hav (by simp [htail])

end MetaMathlibExt
