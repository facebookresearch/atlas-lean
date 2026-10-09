/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM

import Batteries.Data.Vector.Lemmas

/-!
# Z algorithm

Gusfield's linear Z-box algorithm computes the maximal common-prefix length at every suffix.
The source leaves its first entry undefined; this module completes it with `Z[0] = n`.
Boxes use zero-based half-open endpoints, and exhaustion performs no symbol comparison.

## Main definitions and statements

`computeZ` returns every Z value. `computeZ_prefix_iff` characterizes all bounded matching
prefixes, and `computeZ_getElem_le` bounds each suffix value. `computeZ_time_le` and
`computeZ_time_ge` give the linear event bounds. The separate repeated-input vector and time
theorems, and `computeZ_replicate_push_time`, give exact witness-family behavior.

## Implementation notes

Private proofs maintain correct earlier entries and a rightmost positive matching box.
Short copies transfer a known mismatch; extension transfers its seed and then compares directly.
The frontier potential bounds successes, while each extension has at most one actual failure.
The cost counts executed positive-index visits and actual symbol comparisons. Allocation,
indexing, updates, arithmetic and other control operations are free in this event model.

Retained Lean is authored by Codex at Adam Kiezun's explicit selection.

## References

Dan Gusfield, *Algorithms on Strings, Trees, and Sequences*, Cambridge University Press, 1997,
Sections 1.3-1.4, pages 7-10. The printed final strict endpoint bound on page 10 is corrected
to a non-strict bound; an actual box can end at the last character.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StringMatching

universe u

@[no_expose] private def extendPrefix {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (q : Fin (n - i.val + 1)) :
    TimeM Nat (Fin (n - i.val + 1)) :=
  if h : i.val + q.val < n then do
    TimeM.tick 1
    if input[q.val]'(by omega) == input[i.val + q.val]'h then
      extendPrefix input i ⟨q.val + 1, by omega⟩
    else
      pure q
  else
    pure q
termination_by n - (i.val + q.val)

private theorem extendPrefix_ge {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (q : Fin (n - i.val + 1)) :
    q.val ≤ (extendPrefix input i q).ret.val := by
  rw [extendPrefix]
  split
  · simp only [TimeM.ret_bind]
    split
    · exact Nat.le_trans (Nat.le_succ q.val)
        (extendPrefix_ge input i ⟨q.val + 1, by omega⟩)
    · simp
  · simp
termination_by n - (i.val + q.val)

private theorem extendPrefix_time {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (q : Fin (n - i.val + 1)) :
    (extendPrefix input i q).time = (extendPrefix input i q).ret.val - q.val +
      if i.val + (extendPrefix input i q).ret.val < n then 1 else 0 := by
  rw [extendPrefix]
  split
  · rename_i h
    simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick]
    split
    · have ih := extendPrefix_time input i ⟨q.val + 1, by omega⟩
      have hg := extendPrefix_ge input i ⟨q.val + 1, by omega⟩
      simp only at ih hg ⊢
      omega
    · simp [h]
  · rename_i h
    simp [h]
termination_by n - (i.val + q.val)

@[no_expose] private def Agrees {α : Type u} {n : Nat}
    (input : Vector α n) (i q : Nat) : Prop :=
  ∀ k < q, input[k]? = input[i + k]?

private theorem agrees_succ {α : Type u} {n : Nat} (input : Vector α n)
    (i q : Nat) (h : Agrees input i q) (he : input[q]? = input[i + q]?) :
    Agrees input i (q + 1) := by
  intro k hk
  by_cases hq : k < q
  · exact h k hq
  · have heq : k = q := by omega
    simpa [heq] using he

private theorem extendPrefix_spec {α : Type u} [BEq α] [LawfulBEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (q : Fin (n - i.val + 1))
    (hq : Agrees input i.val q.val) :
    Agrees input i.val (extendPrefix input i q).ret.val ∧
      (i.val + (extendPrefix input i q).ret.val = n ∨
        input[(extendPrefix input i q).ret.val]? ≠
          input[i.val + (extendPrefix input i q).ret.val]?) := by
  rw [extendPrefix]
  split
  · rename_i h
    simp only [TimeM.ret_bind]
    split
    · rename_i he
      have hqn : q.val < n := by omega
      have heq : input[q.val]? = input[i.val + q.val]? := by
        simpa only [Vector.getElem?_eq_getElem hqn, Vector.getElem?_eq_getElem h]
          using congrArg some (beq_iff_eq.mp he)
      exact extendPrefix_spec input i ⟨q.val + 1, by omega⟩
        (agrees_succ input i.val q.val hq heq)
    · rename_i he
      simp only [TimeM.ret_pure]
      refine ⟨hq, Or.inr ?_⟩
      have hqn : q.val < n := by omega
      simpa only [Vector.getElem?_eq_getElem hqn, Vector.getElem?_eq_getElem h,
        ne_eq, Option.some.injEq, beq_iff_eq] using he
  · simp only [TimeM.ret_pure]
    exact ⟨hq, Or.inl (by have := q.isLt; omega)⟩
termination_by n - (i.val + q.val)

private theorem agrees_iff_take {α : Type u} {n : Nat} (input : Vector α n)
    (i q : Nat) :
    Agrees input i q ↔ input.toList.take q = (input.toList.drop i).take q := by
  constructor
  · intro h
    apply List.ext_getElem?
    intro k
    by_cases hk : k < q
    · simpa only [List.getElem?_take, ite_eq_left hk, List.getElem?_drop,
        Vector.getElem?_toList] using h k hk
    · simp only [List.getElem?_take, ite_eq_right hk]
  · intro h k hk
    have he := congrArg (fun xs : List α => xs[k]?) h
    simpa only [List.getElem?_take, ite_eq_left hk, List.getElem?_drop,
      Vector.getElem?_toList] using he

@[no_expose] private def IsZ {α : Type u} {n : Nat}
    (input : Vector α n) (i z : Nat) : Prop :=
  i + z ≤ n ∧ Agrees input i z ∧ (i + z = n ∨ input[z]? ≠ input[i + z]?)

private theorem isZ_prefix_iff {α : Type u} {n : Nat} (input : Vector α n)
    (i z : Nat) (hz : IsZ input i z) (q : Nat) :
    q ≤ z ↔ q ≤ n - i ∧ input.toList.take q = (input.toList.drop i).take q := by
  constructor
  · intro hq
    refine ⟨by have := hz.1; omega, (agrees_iff_take input i q).mp ?_⟩
    intro k hk
    exact hz.2.1 k (Nat.lt_of_lt_of_le hk hq)
  · rintro ⟨hq, hm⟩
    have ha := (agrees_iff_take input i q).mpr hm
    by_cases h : q ≤ z
    · exact h
    · have hqz : z < q := by omega
      rcases hz.2.2 with he | he
      · omega
      · exact False.elim (he (ha z hqz))

private theorem box_transfer {α : Type u} {n : Nat} (input : Vector α n)
    (L R i q : Nat) (hL : L ≤ i) (hbox : Agrees input L (R - L))
    (hq : i + q < R) : input[i - L + q]? = input[i + q]? := by
  have ht : i - L + q < R - L := by omega
  have he : L + (i - L + q) = i + q := by omega
  simpa only [he] using hbox (i - L + q) ht

private theorem isZ_copy {α : Type u} {n : Nat} (input : Vector α n)
    (L R i z : Nat) (hL : L ≤ i) (hR : R ≤ n)
    (hbox : Agrees input L (R - L)) (hz : IsZ input (i - L) z)
    (hzlt : z < R - i) : IsZ input i z := by
  refine ⟨by omega, ?_, ?_⟩
  · intro k hk
    exact (hz.2.1 k hk).trans (box_transfer input L R i k hL hbox (by omega))
  · rcases hz.2.2 with he | he
    · omega
    · right
      rw [← box_transfer input L R i z hL hbox (by omega)]
      exact he

private theorem agrees_box_seed {α : Type u} {n : Nat} (input : Vector α n)
    (L R i z : Nat) (hL : L ≤ i) (hbox : Agrees input L (R - L))
    (hz : IsZ input (i - L) z) (hseed : R - i ≤ z) :
    Agrees input i (R - i) := by
  intro k hk
  exact (hz.2.1 k (Nat.lt_of_lt_of_le hk hseed)).trans
    (box_transfer input L R i k hL hbox (by omega))

private structure ZState (n : Nat) where
  table : Vector Nat n
  left : Nat
  right : Fin (n + 1)

@[no_expose] private def zStep {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) : TimeM Nat (ZState n) := do
  TimeM.tick 1
  if hi : i.val < s.right.val then
    let j := i.val - s.left
    let b : Fin (n - i.val + 1) := ⟨s.right.val - i.val, by omega⟩
    if s.table[j]'(by omega) < b.val then
      pure { s with table := s.table.set i.val s.table[j] }
    else
      let q ← extendPrefix input i b
      pure ⟨s.table.set i.val q.val, i.val, ⟨i.val + q.val, by omega⟩⟩
  else
    let q ← extendPrefix input i ⟨0, by omega⟩
    if q.val = 0 then
      pure { s with table := s.table.set i.val 0 }
    else
      pure ⟨s.table.set i.val q.val, i.val, ⟨i.val + q.val, by omega⟩⟩

@[no_expose] private def zScan {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) : TimeM Nat (Vector Nat n) :=
  if h : i < n then do
    let s ← zStep input ⟨i, h⟩ s
    zScan input (i + 1) s
  else
    pure s.table
termination_by n - i

/-- Compute all maximal-prefix lengths using Gusfield's Z-box algorithm.
The first entry is the input length. Cost counts outer visits and actual comparisons. -/
public def computeZ {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) : TimeM Nat (Vector Nat n) :=
  if h : 0 < n then
    zScan input 1 ⟨(Vector.replicate n 0).set 0 n h, 0, ⟨0, by omega⟩⟩
  else
    pure (Vector.replicate n 0)

@[no_expose] private def Processed {α : Type u} {n : Nat}
    (input : Vector α n) (i : Nat) (table : Vector Nat n) : Prop :=
  ∀ j : Fin n, 1 ≤ j.val → j.val < i → IsZ input j.val table[j.val]

@[no_expose] private def Endpoints {n : Nat} (table : Vector Nat n) (i R : Nat) : Prop :=
  ∀ j : Fin n, 1 ≤ j.val → j.val < i → 0 < table[j.val] → j.val + table[j.val] ≤ R

@[no_expose] private def StateInv {α : Type u} {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) : Prop :=
  Processed input i s.table ∧
    ((s.left = 0 ∧ s.right.val = 0) ∨
      (1 ≤ s.left ∧ s.left < i ∧ s.left < s.right.val ∧
        Agrees input s.left (s.right.val - s.left))) ∧
    Endpoints s.table i s.right.val

private theorem processed_set {α : Type u} {n : Nat} (input : Vector α n)
    (i : Fin n) (table : Vector Nat n) (z : Nat) (hp : Processed input i.val table)
    (hz : IsZ input i.val z) : Processed input (i.val + 1) (table.set i.val z) := by
  intro j hj hji
  by_cases he : i.val = j.val
  · have he' : i = j := Fin.ext he
    subst j
    simpa only [Vector.getElem_set_self] using hz
  · rw [Vector.getElem_set_ne i.isLt j.isLt he]
    exact hp j hj (by omega)

private theorem endpoints_set {n : Nat} (i : Fin n) (table : Vector Nat n) (z R : Nat)
    (hp : Endpoints table i.val R) (hz : 0 < z → i.val + z ≤ R) :
    Endpoints (table.set i.val z) (i.val + 1) R := by
  intro j hj hji hjz
  by_cases he : i.val = j.val
  · have he' : i = j := Fin.ext he
    subst j
    simpa only [Vector.getElem_set_self] using hz (by
      simpa only [Vector.getElem_set_self] using hjz)
  · rw [Vector.getElem_set_ne i.isLt j.isLt he] at hjz ⊢
    exact hp j hj (by omega) hjz

private theorem stateInv_keep {α : Type u} {n : Nat} (input : Vector α n)
    (i : Fin n) (s : ZState n) (z : Nat) (hs : StateInv input i.val s)
    (hz : IsZ input i.val z) (hR : 0 < z → i.val + z ≤ s.right.val) :
    StateInv input (i.val + 1) { s with table := s.table.set i.val z } := by
  dsimp only [StateInv]
  refine ⟨processed_set input i s.table z hs.1 hz, ?_,
    endpoints_set i s.table z s.right.val hs.2.2 hR⟩
  rcases hs.2.1 with he | ⟨hL, hLi, hLR, hbox⟩
  · exact Or.inl he
  · exact Or.inr ⟨hL, by omega, hLR, hbox⟩

private theorem stateInv_new {α : Type u} {n : Nat} (input : Vector α n)
    (i : Fin n) (s : ZState n) (z : Nat) (hi : 1 ≤ i.val)
    (hs : StateInv input i.val s) (hz : IsZ input i.val z)
    (hpos : 0 < z) (hR : s.right.val ≤ i.val + z) :
    StateInv input (i.val + 1)
      ⟨s.table.set i.val z, i.val, ⟨i.val + z, by have := hz.1; omega⟩⟩ := by
  dsimp only [StateInv]
  refine ⟨processed_set input i s.table z hs.1 hz, Or.inr ?_, ?_⟩
  · refine ⟨hi, by omega, by omega, ?_⟩
    simpa only [Nat.add_sub_cancel_left] using hz.2.1
  · apply endpoints_set i s.table z (i.val + z)
    · intro j hj hji hjz
      exact Nat.le_trans (hs.2.2 j hj hji hjz) hR
    · intro _
      exact Nat.le_refl _

private theorem zStep_inv {α : Type u} [BEq α] [LawfulBEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) (hi : 1 ≤ i.val)
    (hs : StateInv input i.val s) : StateInv input (i.val + 1) (zStep input i s).ret := by
  rw [zStep]
  simp only [TimeM.ret_bind]
  split
  · rename_i hins
    have hb : 1 ≤ s.left ∧ s.left < i.val ∧ s.left < s.right.val ∧
        Agrees input s.left (s.right.val - s.left) := by
      rcases hs.2.1 with he | hb
      · have := he.2
        omega
      · exact hb
    have hj : i.val - s.left < n := by omega
    have hp := hs.1 ⟨i.val - s.left, hj⟩
      (by change 1 ≤ i.val - s.left; have := hb.2.1; omega)
      (by change i.val - s.left < i.val; have := hb.1; omega)
    split
    · rename_i hc
      simp only [TimeM.ret_pure]
      apply stateInv_keep input i s s.table[i.val - s.left] hs
      · exact isZ_copy input s.left s.right.val i.val s.table[i.val - s.left]
          (by have := hb.2.1; omega) (by have := s.right.isLt; omega) hb.2.2.2 hp hc
      · intro _
        omega
    · rename_i hc
      simp only [TimeM.ret_bind, TimeM.ret_pure]
      have hseed : Agrees input i.val (s.right.val - i.val) :=
        agrees_box_seed input s.left s.right.val i.val s.table[i.val - s.left]
          (by have := hb.2.1; omega) hb.2.2.2 hp (by omega)
      have he := extendPrefix_spec input i ⟨s.right.val - i.val, by omega⟩ hseed
      have hg := extendPrefix_ge input i ⟨s.right.val - i.val, by omega⟩
      simp only at he hg
      let q := (extendPrefix input i ⟨s.right.val - i.val, by omega⟩).ret
      have hz : IsZ input i.val q.val :=
        ⟨by have := q.isLt; omega, he.1, he.2⟩
      apply stateInv_new input i s q.val hi hs hz
      · dsimp only [q]
        omega
      · dsimp only [q]
        omega
  · rename_i hout
    simp only [TimeM.ret_bind]
    have he := extendPrefix_spec input i ⟨0, by omega⟩
      (by change Agrees input i.val 0; intro k hk; omega)
    let q := (extendPrefix input i ⟨0, by omega⟩).ret
    have hz : IsZ input i.val q.val :=
      ⟨by have := q.isLt; omega, he.1, he.2⟩
    split
    · rename_i hzero
      simp only [TimeM.ret_pure]
      apply stateInv_keep input i s 0 hs
      · simpa only [q, hzero] using hz
      · omega
    · rename_i hpos
      simp only [TimeM.ret_pure]
      apply stateInv_new input i s q.val hi hs hz
      · dsimp only [q]
        omega
      · omega

private theorem zScan_processed {α : Type u} [BEq α] [LawfulBEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) (hi : 1 ≤ i)
    (hs : StateInv input i s) : Processed input n (zScan input i s).ret := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.ret_bind]
    exact zScan_processed input (i + 1) (zStep input ⟨i, h⟩ s).ret (by omega)
      (zStep_inv input ⟨i, h⟩ s hi hs)
  · rename_i h
    simp only [TimeM.ret_pure]
    intro j hj hjn
    exact hs.1 j hj (by omega)
termination_by n - i

private theorem zStep_get_ne {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) (j : Fin n)
    (hij : i.val ≠ j.val) : (zStep input i s).ret.table[j.val] = s.table[j.val] := by
  rw [zStep]
  simp only [TimeM.ret_bind]
  split
  · split <;> simp only [TimeM.ret_bind, TimeM.ret_pure]
    all_goals exact Vector.getElem_set_ne i.isLt j.isLt hij
  · simp only [TimeM.ret_bind]
    split <;> simp only [TimeM.ret_pure]
    all_goals exact Vector.getElem_set_ne i.isLt j.isLt hij

private theorem zScan_zero {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) (h0 : 0 < n) (hi : 1 ≤ i) :
    (zScan input i s).ret[0] = s.table[0] := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.ret_bind]
    exact (zScan_zero input (i + 1) (zStep input ⟨i, h⟩ s).ret h0 (by omega)).trans
      (zStep_get_ne input ⟨i, h⟩ s ⟨0, h0⟩ (by change i ≠ 0; omega))
  · simp only [TimeM.ret_pure]
termination_by n - i

/-- The source's undefined first entry is completed with the full input length. -/
public theorem computeZ_zero {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (h : 0 < n) : (computeZ input).ret[0] = n := by
  rw [computeZ, dite_eq_left h]
  simpa only [Vector.getElem_set_self] using zScan_zero input 1
    ⟨(Vector.replicate n 0).set 0 n h, 0, ⟨0, by omega⟩⟩ h (by omega)

private theorem computeZ_isZ {α : Type u} [BEq α] [LawfulBEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) : IsZ input i.val (computeZ input).ret[i.val] := by
  by_cases hi : i.val = 0
  · have hn : 0 < n := by have := i.isLt; omega
    have he : i = ⟨0, hn⟩ := Fin.ext hi
    subst i
    change IsZ input 0 (computeZ input).ret[0]
    rw [computeZ_zero input hn]
    refine ⟨by omega, ?_, Or.inl (by omega)⟩
    intro k hk
    simp only [Nat.zero_add]
  · have hn : 0 < n := by have := i.isLt; omega
    have hs : StateInv input 1
        ⟨(Vector.replicate n 0).set 0 n hn, 0, ⟨0, by omega⟩⟩ := by
      refine ⟨?_, Or.inl ⟨rfl, rfl⟩, ?_⟩
      · intro j hj hj1
        omega
      · intro j hj hj1 hjz
        omega
    rw [computeZ, dite_eq_left hn]
    exact zScan_processed input 1 _ (by omega) hs i (by omega) i.isLt

/-- Every returned entry is the maximal common-prefix length of its suffix.
The explicit suffix-length bound rules out equality caused by `List.take` truncation. -/
public theorem computeZ_prefix_iff {α : Type u} [BEq α] [LawfulBEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (q : Nat) :
    q ≤ (computeZ input).ret[i.val] ↔ q ≤ n - i.val ∧
      input.toList.take q = (input.toList.drop i.val).take q :=
  isZ_prefix_iff input i.val _ (computeZ_isZ input i) q

private theorem zStep_entry_le {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) :
    (zStep input i s).ret.table[i.val] ≤ n - i.val := by
  rw [zStep]
  simp only [TimeM.ret_bind]
  split
  · split
    · simp only [TimeM.ret_pure, Vector.getElem_set_self]
      have := s.right.isLt
      omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure, Vector.getElem_set_self]
      have := (extendPrefix input i ⟨s.right.val - i.val, by omega⟩).ret.isLt
      omega
  · simp only [TimeM.ret_bind]
    split
    · simp only [TimeM.ret_pure, Vector.getElem_set_self]
      omega
    · simp only [TimeM.ret_pure, Vector.getElem_set_self]
      have := (extendPrefix input i ⟨0, by omega⟩).ret.isLt
      omega

private theorem zScan_bounds {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n)
    (hs : ∀ j : Fin n, s.table[j.val] ≤ n - j.val) :
    ∀ j : Fin n, (zScan input i s).ret[j.val] ≤ n - j.val := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.ret_bind]
    apply zScan_bounds input (i + 1) (zStep input ⟨i, h⟩ s).ret
    intro j
    by_cases he : i = j.val
    · have he' : (⟨i, h⟩ : Fin n) = j := Fin.ext he
      subst j
      exact zStep_entry_le input ⟨i, h⟩ s
    · rw [zStep_get_ne input ⟨i, h⟩ s j he]
      exact hs j
  · simp only [TimeM.ret_pure]
    exact hs
termination_by n - i

/-- Every suffix value is bounded even when the executable comparator is not lawful. -/
public theorem computeZ_getElem_le {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) : (computeZ input).ret[i.val] ≤ n - i.val := by
  have hn : 0 < n := by have := i.isLt; omega
  rw [computeZ, dite_eq_left hn]
  apply zScan_bounds input 1 _ ?_ i
  intro j
  simp only [Vector.getElem_set, Vector.getElem_replicate]
  split <;> omega

/- The cost specification follows the executed branch and returned extension endpoint.
It is not used to assign the algorithm's cost; actual adjacent ticks determine `TimeM.time`. -/
@[no_expose] private def stepComparisons {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) : Nat :=
  if hi : i.val < s.right.val then
    let j := i.val - s.left
    let b : Fin (n - i.val + 1) := ⟨s.right.val - i.val, by omega⟩
    if s.table[j]'(by omega) < b.val then
      0
    else
      let q := (extendPrefix input i b).ret.val
      q - b.val + if i.val + q < n then 1 else 0
  else
    let q := (extendPrefix input i ⟨0, by omega⟩).ret.val
    q + if i.val + q < n then 1 else 0

private theorem zStep_time_eq {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) :
    (zStep input i s).time = 1 + stepComparisons input i s := by
  rw [zStep, stepComparisons]
  simp only [TimeM.time_bind, TimeM.time_tick]
  split
  · split
    · simp only [TimeM.time_pure]
    · simp only [TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
      rw [extendPrefix_time]
  · simp only [TimeM.time_bind]
    rw [extendPrefix_time]
    split <;> split <;> simp only [TimeM.time_pure, Nat.sub_zero, Nat.add_zero]

@[no_expose] private def comparisonSum {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) : Nat :=
  if h : i < n then
    stepComparisons input ⟨i, h⟩ s +
      comparisonSum input (i + 1) (zStep input ⟨i, h⟩ s).ret
  else
    0
termination_by n - i

private theorem zScan_time_eq {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) :
    (zScan input i s).time = n - i + comparisonSum input i s := by
  rw [zScan, comparisonSum]
  split
  · rename_i h
    simp only [TimeM.time_bind]
    rw [zStep_time_eq, zScan_time_eq]
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by n - i

@[no_expose] private def computeZComparisons {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) : Nat :=
  if h : 0 < n then
    comparisonSum input 1 ⟨(Vector.replicate n 0).set 0 n h, 0, ⟨0, by omega⟩⟩
  else
    0

private theorem computeZ_time_eq {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) : (computeZ input).time = n - 1 + computeZComparisons input := by
  rw [computeZ, computeZComparisons]
  split
  · exact zScan_time_eq input 1 _
  · simp only [TimeM.time_pure]
    omega

private theorem zStep_cost {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) (hi : 1 ≤ i.val) :
    s.right.val ≤ (zStep input i s).ret.right.val ∧
      (zStep input i s).time ≤
        2 + max 1 (zStep input i s).ret.right.val - max 1 s.right.val := by
  rw [zStep]
  simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick]
  split
  · rename_i hins
    split
    · simp only [TimeM.ret_pure, TimeM.time_pure]
      constructor
      · exact Nat.le_refl _
      · omega
    · simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.ret_pure, TimeM.time_pure]
      have hg := extendPrefix_ge input i ⟨s.right.val - i.val, by omega⟩
      have hc := extendPrefix_time input i ⟨s.right.val - i.val, by omega⟩
      simp only at hg hc ⊢
      have hm : max 1 s.right.val = s.right.val := Nat.max_eq_right (by omega)
      have hm' : max 1
          (i.val + (extendPrefix input i ⟨s.right.val - i.val, by omega⟩).ret.val) =
          i.val + (extendPrefix input i ⟨s.right.val - i.val, by omega⟩).ret.val :=
        Nat.max_eq_right (by omega)
      rw [hm, hm']
      split at hc <;> omega
  · rename_i hout
    simp only [TimeM.ret_bind, TimeM.time_bind]
    have hc := extendPrefix_time input i ⟨0, by omega⟩
    simp only at hc
    split
    · rename_i hzero
      simp only [TimeM.ret_pure, TimeM.time_pure]
      rw [hzero] at hc
      simp only [Nat.zero_sub, Nat.add_zero] at hc
      split at hc <;> omega
    · rename_i hpos
      simp only [TimeM.ret_pure, TimeM.time_pure]
      have hm : max 1 s.right.val ≤ i.val := Nat.max_le.mpr ⟨hi, by omega⟩
      have hm' : max 1 (i.val + (extendPrefix input i ⟨0, by omega⟩).ret.val) =
          i.val + (extendPrefix input i ⟨0, by omega⟩).ret.val :=
        Nat.max_eq_right (by omega)
      rw [hm']
      split at hc <;> omega

private theorem zScan_time_le {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) (hi : 1 ≤ i) :
    (zScan input i s).time ≤ 2 * (n - i) + n - max 1 s.right.val := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.time_bind]
    have hs := zStep_cost input ⟨i, h⟩ s hi
    have ih := zScan_time_le input (i + 1) (zStep input ⟨i, h⟩ s).ret (by omega)
    have hr := (zStep input ⟨i, h⟩ s).ret.right.isLt
    have hs' := s.right.isLt
    have hm : max 1 (zStep input ⟨i, h⟩ s).ret.right.val ≤ n :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by n - i

/-- In the declared event model, the algorithm uses at most three events per positive index. -/
public theorem computeZ_time_le {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) : (computeZ input).time ≤ 3 * (n - 1) := by
  rw [computeZ]
  split
  · rename_i h
    have hs := zScan_time_le input 1
      ⟨(Vector.replicate n 0).set 0 n h, 0, ⟨0, by omega⟩⟩ (by omega)
    simp only [Nat.max_eq_left (Nat.zero_le 1)] at hs
    omega
  · simp only [TimeM.time_pure]
    omega

private theorem zStep_time_ge {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Fin n) (s : ZState n) :
    1 ≤ (zStep input i s).time := by
  rw [zStep]
  simp only [TimeM.time_bind, TimeM.time_tick]
  omega

private theorem zScan_time_ge {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) (i : Nat) (s : ZState n) :
    n - i ≤ (zScan input i s).time := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.time_bind]
    have hs := zStep_time_ge input ⟨i, h⟩ s
    have ih := zScan_time_ge input (i + 1) (zStep input ⟨i, h⟩ s).ret
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by n - i

/-- Every positive-index visit contributes one event, even a zero-comparison copy. -/
public theorem computeZ_time_ge {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) : n - 1 ≤ (computeZ input).time := by
  rw [computeZ]
  split
  · exact zScan_time_ge input 1 _
  · simp only [TimeM.time_pure]
    omega

private theorem isZ_replicate_value {α : Type u} {n : Nat} (a : α)
    (i z : Nat) (hi : i ≤ n) (hz : IsZ (Vector.replicate n a) i z) : z = n - i := by
  apply Nat.le_antisymm
  · have := hz.1
    omega
  · apply (isZ_prefix_iff (Vector.replicate n a) i z hz (n - i)).mpr
    refine ⟨Nat.le_refl _, ?_⟩
    simp only [Vector.toList_replicate, List.take_replicate, List.drop_replicate,
      Nat.min_self, Nat.min_eq_left (Nat.sub_le n i)]

/-- Repeated-symbol input returns the whole remaining suffix at every position. -/
public theorem computeZ_replicate {α : Type u} [BEq α] [LawfulBEq α]
    (a : α) (n : Nat) :
    (computeZ (Vector.replicate n a)).ret = Vector.ofFn (fun i : Fin n => n - i.val) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn hi]
  exact isZ_replicate_value a i _ (Nat.le_of_lt hi)
    (computeZ_isZ (Vector.replicate n a) ⟨i, hi⟩)

private theorem extendPrefix_replicate_value {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a : α) (i : Fin n) (q : Fin (n - i.val + 1)) :
    (extendPrefix (Vector.replicate n a) i q).ret.val = n - i.val := by
  have hseed : Agrees (Vector.replicate n a) i.val q.val := by
    intro k hk
    have hkn : k < n := by have := q.isLt; omega
    have hik : i.val + k < n := by have := q.isLt; omega
    simp only [Vector.getElem?_eq_getElem hkn, Vector.getElem?_eq_getElem hik,
      Vector.getElem_replicate]
  have he := extendPrefix_spec (Vector.replicate n a) i q hseed
  exact isZ_replicate_value a i.val _ (Nat.le_of_lt i.isLt)
    ⟨by have := (extendPrefix (Vector.replicate n a) i q).ret.isLt; omega, he.1, he.2⟩

private theorem extendPrefix_replicate_time {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a : α) (i : Fin n) (q : Fin (n - i.val + 1)) :
    (extendPrefix (Vector.replicate n a) i q).time = n - i.val - q.val := by
  rw [extendPrefix_time, extendPrefix_replicate_value]
  have he : i.val + (n - i.val) = n := by have := i.isLt; omega
  simp [he]

private theorem zStep_replicate_full {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a : α) (i : Fin n) (s : ZState n) (hi : 1 ≤ i.val)
    (hs : StateInv (Vector.replicate n a) i.val s) (hr : s.right.val = n) :
    (zStep (Vector.replicate n a) i s).time = 1 ∧
      (zStep (Vector.replicate n a) i s).ret.right.val = n := by
  rw [zStep]
  simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick]
  split
  · have hb : 1 ≤ s.left ∧ s.left < i.val := by
      rcases hs.2.1 with he | hb
      · have := he.2
        omega
      · exact ⟨hb.1, hb.2.1⟩
    have hj : i.val - s.left < n := by omega
    have hp := hs.1 ⟨i.val - s.left, hj⟩
      (by change 1 ≤ i.val - s.left; have := hb.2; omega)
      (by change i.val - s.left < i.val; have := hb.1; omega)
    have hv := isZ_replicate_value a (i.val - s.left) s.table[i.val - s.left]
      (by omega) hp
    split
    · omega
    · simp only [TimeM.ret_bind, TimeM.time_bind]
      have hext : extendPrefix (Vector.replicate n a) i
          ⟨s.right.val - i.val, by omega⟩ =
          pure (⟨s.right.val - i.val, by omega⟩ : Fin (n - i.val + 1)) := by
        rw [extendPrefix]
        have hstop : ¬i.val + (s.right.val - i.val) < n := by omega
        simp only [dite_eq_right hstop]
      rw [hext]
      simp only [TimeM.ret_pure, TimeM.time_pure, Nat.add_zero]
      constructor
      · trivial
      · omega
  · omega

private theorem zScan_replicate_full {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a : α) (i : Nat) (s : ZState n) (hi : 1 ≤ i)
    (hs : StateInv (Vector.replicate n a) i s) (hr : s.right.val = n) :
    (zScan (Vector.replicate n a) i s).time = n - i := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.time_bind]
    have hstep := zStep_replicate_full a ⟨i, h⟩ s hi hs hr
    rw [hstep.1]
    have ih := zScan_replicate_full a (i + 1)
      (zStep (Vector.replicate n a) ⟨i, h⟩ s).ret (by omega)
      (zStep_inv (Vector.replicate n a) ⟨i, h⟩ s hi hs) hstep.2
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by n - i

/-- Repeated-symbol input executes exactly `n - 1` comparisons as well as its outer visits. -/
public theorem computeZ_replicate_time {α : Type u} [BEq α] [LawfulBEq α]
    (a : α) (n : Nat) : (computeZ (Vector.replicate n a)).time = 2 * (n - 1) := by
  by_cases h2 : 1 < n
  · have hn : 0 < n := by omega
    let s : ZState n := ⟨(Vector.replicate n 0).set 0 n hn, 0, ⟨0, by omega⟩⟩
    have hs : StateInv (Vector.replicate n a) 1 s := by
      refine ⟨?_, Or.inl ⟨rfl, rfl⟩, ?_⟩
      · intro j hj hj1
        omega
      · intro j hj hj1 hjz
        omega
    have hp : n - 1 ≠ 0 := by omega
    have ht : (zStep (Vector.replicate n a) ⟨1, h2⟩ s).time = n := by
      rw [zStep]
      simp only [s, TimeM.time_bind, TimeM.time_tick,
        dite_eq_right (Nat.not_lt_zero 1)]
      rw [extendPrefix_replicate_time]
      split <;> simp only [TimeM.time_pure] <;> omega
    have hr : (zStep (Vector.replicate n a) ⟨1, h2⟩ s).ret.right.val = n := by
      rw [zStep]
      simp only [s, TimeM.ret_bind, dite_eq_right (Nat.not_lt_zero 1),
        extendPrefix_replicate_value, ite_eq_right hp, TimeM.ret_pure]
      omega
    rw [computeZ, dite_eq_left hn, zScan, dite_eq_left h2]
    simp only [TimeM.time_bind]
    change (zStep (Vector.replicate n a) ⟨1, h2⟩ s).time +
      (zScan (Vector.replicate n a) 2 (zStep (Vector.replicate n a) ⟨1, h2⟩ s).ret).time = _
    rw [ht, zScan_replicate_full a 2 _ (by omega)
      (zStep_inv (Vector.replicate n a) ⟨1, h2⟩ s (Nat.le_refl 1) hs) hr]
    omega
  · rw [computeZ]
    split
    · rw [zScan, dite_eq_right h2]
      simp only [TimeM.time_pure]
      omega
    · simp only [TimeM.time_pure]
      omega

private theorem isZ_unique {α : Type u} {n : Nat} (input : Vector α n)
    (i z w : Nat) (hz : IsZ input i z) (hw : IsZ input i w) : z = w := by
  apply Nat.le_antisymm
  · exact (isZ_prefix_iff input i w hw z).mpr
      ⟨by have := hz.1; omega, (agrees_iff_take input i z).mp hz.2.1⟩
  · exact (isZ_prefix_iff input i z hz w).mpr
      ⟨by have := hw.1; omega, (agrees_iff_take input i w).mp hw.2.1⟩

private theorem isZ_replicate_push {α : Type u} {n : Nat} (a b : α) (hab : a ≠ b)
    (i : Fin (n + 1)) (hi : 1 ≤ i.val) :
    IsZ ((Vector.replicate n a).push b) i.val (n - i.val) := by
  have hin : i.val ≤ n := by have := i.isLt; omega
  refine ⟨by omega, ?_, Or.inr ?_⟩
  · intro k hk
    have hkn : k < n := by omega
    have hik : i.val + k < n := by omega
    have hkn' : k < n + 1 := by omega
    have hik' : i.val + k < n + 1 := by omega
    simp only [Vector.getElem?_eq_getElem hkn', Vector.getElem?_eq_getElem hik',
      Vector.getElem_push, dite_eq_left hkn, dite_eq_left hik, Vector.getElem_replicate]
  · have hzn : n - i.val < n := by omega
    have he : i.val + (n - i.val) = n := by omega
    have hzn' : n - i.val < n + 1 := by omega
    have ha : ((Vector.replicate n a).push b)[n - i.val]? = some a := by
      simp only [Vector.getElem?_eq_getElem hzn', Vector.getElem_push,
        dite_eq_left hzn, Vector.getElem_replicate]
    have hb : ((Vector.replicate n a).push b)[i.val + (n - i.val)]? = some b := by
      rw [he]
      simp only [Vector.getElem?_eq_getElem (Nat.lt_succ_self n), Vector.getElem_push,
        dite_eq_right (Nat.lt_irrefl n)]
    rw [ha, hb]
    exact fun h => hab (Option.some.inj h)

private theorem extendPrefix_push_value {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a b : α) (hab : a ≠ b) (i : Fin (n + 1)) (hi : 1 ≤ i.val)
    (q : Fin (n + 1 - i.val + 1)) (hq : q.val ≤ n - i.val) :
    (extendPrefix ((Vector.replicate n a).push b) i q).ret.val = n - i.val := by
  have hz := isZ_replicate_push a b hab i hi
  have hseed : Agrees ((Vector.replicate n a).push b) i.val q.val := by
    intro k hk
    exact hz.2.1 k (Nat.lt_of_lt_of_le hk hq)
  have he := extendPrefix_spec ((Vector.replicate n a).push b) i q hseed
  exact isZ_unique ((Vector.replicate n a).push b) i.val _ (n - i.val)
    ⟨by have := (extendPrefix ((Vector.replicate n a).push b) i q).ret.isLt; omega,
      he.1, he.2⟩ hz

private theorem extendPrefix_push_time {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a b : α) (hab : a ≠ b) (i : Fin (n + 1)) (hi : 1 ≤ i.val)
    (q : Fin (n + 1 - i.val + 1)) (hq : q.val ≤ n - i.val) :
    (extendPrefix ((Vector.replicate n a).push b) i q).time = n - i.val - q.val + 1 := by
  rw [extendPrefix_time, extendPrefix_push_value a b hab i hi q hq]
  have he : i.val + (n - i.val) < n + 1 := by have := i.isLt; omega
  simp only [ite_eq_left he]

private theorem zStep_push_full {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a b : α) (hab : a ≠ b) (i : Fin (n + 1)) (s : ZState (n + 1))
    (hi : 1 ≤ i.val) (hs : StateInv ((Vector.replicate n a).push b) i.val s)
    (hr : s.right.val = n) :
    (zStep ((Vector.replicate n a).push b) i s).time = 2 ∧
      (zStep ((Vector.replicate n a).push b) i s).ret.right.val = n := by
  rw [zStep]
  simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.time_tick]
  split
  · have hb : 1 ≤ s.left ∧ s.left < i.val := by
      rcases hs.2.1 with he | hb
      · have := he.2
        omega
      · exact ⟨hb.1, hb.2.1⟩
    have hj : i.val - s.left < n + 1 := by omega
    have hj1 : 1 ≤ i.val - s.left := by have := hb.2; omega
    have hp : IsZ ((Vector.replicate n a).push b) (i.val - s.left)
        s.table[i.val - s.left] := hs.1 ⟨i.val - s.left, hj⟩ hj1
      (by change i.val - s.left < i.val; have := hb.1; omega)
    have hv := isZ_unique ((Vector.replicate n a).push b) (i.val - s.left)
      s.table[i.val - s.left] (n - (i.val - s.left)) hp
      (isZ_replicate_push a b hab ⟨i.val - s.left, hj⟩ hj1)
    split
    · omega
    · simp only [TimeM.ret_bind, TimeM.time_bind, TimeM.ret_pure, TimeM.time_pure]
      have hq : (⟨s.right.val - i.val, by omega⟩ :
          Fin (n + 1 - i.val + 1)).val ≤ n - i.val := by
        change s.right.val - i.val ≤ n - i.val
        omega
      constructor
      · rw [extendPrefix_push_time a b hab i hi _ hq]
        simp only
        omega
      · rw [extendPrefix_push_value a b hab i hi _ hq]
        have := i.isLt
        omega
  · rename_i hout
    have hin : i.val = n := by have := i.isLt; omega
    simp only [TimeM.ret_bind, TimeM.time_bind]
    have hq : (⟨0, by omega⟩ : Fin (n + 1 - i.val + 1)).val ≤ n - i.val := by
      change 0 ≤ n - i.val
      omega
    have ht := extendPrefix_push_time a b hab i hi ⟨0, by omega⟩ hq
    have hv := extendPrefix_push_value a b hab i hi ⟨0, by omega⟩ hq
    split
    · simp only [TimeM.ret_pure, TimeM.time_pure]
      constructor
      · rw [ht]
        omega
      · exact hr
    · omega

private theorem zScan_push_full {α : Type u} [BEq α] [LawfulBEq α]
    {n : Nat} (a b : α) (hab : a ≠ b) (i : Nat) (s : ZState (n + 1)) (hi : 1 ≤ i)
    (hs : StateInv ((Vector.replicate n a).push b) i s) (hr : s.right.val = n) :
    (zScan ((Vector.replicate n a).push b) i s).time = 2 * (n + 1 - i) := by
  rw [zScan]
  split
  · rename_i h
    simp only [TimeM.time_bind]
    have hstep := zStep_push_full a b hab ⟨i, h⟩ s hi hs hr
    rw [hstep.1]
    have ih := zScan_push_full a b hab (i + 1)
      (zStep ((Vector.replicate n a).push b) ⟨i, h⟩ s).ret (by omega)
      (zStep_inv ((Vector.replicate n a).push b) ⟨i, h⟩ s hi hs) hstep.2
    omega
  · simp only [TimeM.time_pure]
    omega
termination_by n + 1 - i

/-- A repeated prefix followed by a distinct final symbol preserves every explicit failure.
For total input length `N = n + 1`, this is `3 * N - 4` events. -/
public theorem computeZ_replicate_push_time {α : Type u} [BEq α] [LawfulBEq α]
    (a b : α) (hab : a ≠ b) (n : Nat) (hn : 0 < n) :
    (computeZ ((Vector.replicate n a).push b)).time = 3 * n - 1 := by
  have hn' : 0 < n + 1 := by omega
  have h1 : 1 < n + 1 := by omega
  let s : ZState (n + 1) :=
    ⟨(Vector.replicate (n + 1) 0).set 0 (n + 1) hn', 0, ⟨0, by omega⟩⟩
  have hs : StateInv ((Vector.replicate n a).push b) 1 s := by
    refine ⟨?_, Or.inl ⟨rfl, rfl⟩, ?_⟩
    · intro j hj hj1
      omega
    · intro j hj hj1 hjz
      omega
  have hq : (⟨0, by omega⟩ : Fin (n + 1 - 1 + 1)).val ≤ n - 1 := by
    change 0 ≤ n - 1
    omega
  have ht : (zStep ((Vector.replicate n a).push b) ⟨1, h1⟩ s).time = n + 1 := by
    rw [zStep]
    simp only [s, TimeM.time_bind, TimeM.time_tick,
      dite_eq_right (Nat.not_lt_zero 1)]
    rw [extendPrefix_push_time a b hab ⟨1, h1⟩ (Nat.le_refl 1) _ hq]
    split <;> simp only [TimeM.time_pure] <;> omega
  have htail : (zScan ((Vector.replicate n a).push b) 2
      (zStep ((Vector.replicate n a).push b) ⟨1, h1⟩ s).ret).time = 2 * (n - 1) := by
    by_cases h2 : 1 < n
    · have hp : n - 1 ≠ 0 := by omega
      have hv := extendPrefix_push_value a b hab ⟨1, h1⟩ (Nat.le_refl 1)
        ⟨0, by omega⟩ hq
      have hr : (zStep ((Vector.replicate n a).push b) ⟨1, h1⟩ s).ret.right.val = n := by
        rw [zStep]
        simp only [s, TimeM.ret_bind, dite_eq_right (Nat.not_lt_zero 1),
          hv, ite_eq_right hp, TimeM.ret_pure]
        omega
      have hh := zScan_push_full a b hab 2 _ (by omega)
        (zStep_inv ((Vector.replicate n a).push b) ⟨1, h1⟩ s (Nat.le_refl 1) hs) hr
      omega
    · rw [zScan, dite_eq_right (by omega : ¬2 < n + 1)]
      simp only [TimeM.time_pure]
      omega
  rw [computeZ, dite_eq_left hn', zScan, dite_eq_left h1]
  simp only [TimeM.time_bind]
  change (zStep ((Vector.replicate n a).push b) ⟨1, h1⟩ s).time +
    (zScan ((Vector.replicate n a).push b) 2
      (zStep ((Vector.replicate n a).push b) ⟨1, h1⟩ s).ret).time = _
  rw [ht, htail]
  omega

private theorem computeZComparisons_le {α : Type u} [BEq α] {n : Nat}
    (input : Vector α n) : computeZComparisons input ≤ 2 * (n - 1) := by
  have he := computeZ_time_eq input
  have hl := computeZ_time_le input
  omega

private theorem computeZComparisons_replicate {α : Type u} [BEq α] [LawfulBEq α]
    (a : α) (n : Nat) : computeZComparisons (Vector.replicate n a) = n - 1 := by
  have he := computeZ_time_eq (Vector.replicate n a)
  have ht := computeZ_replicate_time a n
  omega

private theorem computeZComparisons_replicate_push {α : Type u} [BEq α] [LawfulBEq α]
    (a b : α) (hab : a ≠ b) (n : Nat) (hn : 0 < n) :
    computeZComparisons ((Vector.replicate n a).push b) = 2 * n - 1 := by
  have he := computeZ_time_eq ((Vector.replicate n a).push b)
  have ht := computeZ_replicate_push_time a b hab n hn
  omega

end Cslib.Algorithms.Lean.StringMatching
