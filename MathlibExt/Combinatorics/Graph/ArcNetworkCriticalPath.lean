/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetworkWalk
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Logic.Relation

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Lattice.Nat

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Critical-path bounds and earliest event dates on an arc network

An activity-on-arc network has an event type `V`, an arc type `E` with
`tail head : E → V` and arc durations `dur : E → ℕ`. An arc is its element of `E`, so parallel
arcs stay distinct. Event times `τ : V → ℕ` are a feasible schedule when the head event of
every arc occurs no earlier than its tail event plus the arc's duration,
`τ (tail e) + dur e ≤ τ (head e)`. A walk is an arc list (`IsArcWalk`) and its duration is
`(l.map dur).sum`.

- Critical-path lower bound (`IsFeasibleSchedule.add_sum_map_le`): under a feasible schedule
  every walk from `o` to `d` satisfies `τ o + (l.map dur).sum ≤ τ d`, with no acyclicity
  assumption (a cycle of positive duration has no feasible schedule).
- Earliest event dates (`exists_isFeasibleSchedule_eq_sum`): if `E` is finite, the network has
  no nonempty closed walk and every event is reachable from a source event `s` by a walk, then
  some feasible schedule puts `s` at tick `0` and each event at the duration of some walk from
  `s`. With the lower bound this schedule is earliest, and the provided walk to each event has
  maximum duration among walks from `s`. A specification, not an algorithm: no longest-path
  recurrence is stated.

Every time and duration is a natural number of ticks; tick `0` is the start.

Reference: J. E. Kelley Jr. and M. R. Walker, Critical-path planning and scheduling,
*Proceedings of the Eastern Joint Computer Conference*, 1959, pp. 160-173 (earliest event
times as longest path lengths from the source in an activity-on-arc network).
-/

/-- Event times `τ : V → ℕ` are a feasible schedule of the activity-on-arc network
`tail head : E → V` with arc durations `dur : E → ℕ`, all in ticks, when the head event of
every arc occurs no earlier than its tail event plus the arc's duration. -/
def IsFeasibleSchedule {V E : Type*} (tail head : E → V) (dur : E → ℕ) (τ : V → ℕ) : Prop :=
  ∀ e, τ (tail e) + dur e ≤ τ (head e)
private theorem mem_of_mem_or {E : Type*} {o1 o2 : Option E} {a : E} (h : a ∈ o1.or o2) :
    a ∈ o1 ∨ (o1 = none ∧ a ∈ o2) := by
  cases o1 with
  | none => exact Or.inr ⟨rfl, h⟩
  | some b => exact Or.inl h
private theorem mem_or_left {E : Type*} {o1 o2 : Option E} {a : E} (h : a ∈ o1) :
    a ∈ o1.or o2 := by
  cases o1 with
  | none => exact absurd h (Option.not_mem_none a)
  | some b => exact h
private theorem getLast?_cons_or {E : Type*} (a : E) (l : List E) :
    (a :: l).getLast? = l.getLast?.or (some a) := by
  have h : (a :: l) = [a] ++ l := by simp
  rw [h, List.getLast?_append, List.getLast?_singleton]
/-- Critical-path lower bound: under a feasible schedule of an activity-on-arc network, the
duration of every walk `l` from `o` to `d` fits between the two events,
`τ o + (l.map dur).sum ≤ τ d`. In particular the sink event follows the source event by at least
the duration of every source-to-sink walk, a critical (longest) one included. No acyclicity is
assumed. -/
theorem IsFeasibleSchedule.add_sum_map_le {V E : Type*} {tail head : E → V} {dur : E → ℕ}
    {τ : V → ℕ} (hτ : IsFeasibleSchedule tail head dur τ) {o d : V} {l : List E}
    (hl : IsArcWalk tail head o d l) : τ o + (l.map dur).sum ≤ τ d := by
  revert o hl
  induction l with
  | nil =>
    intro o hl
    obtain ⟨hempty, -, -, -⟩ := hl
    have hod : o = d := hempty rfl
    subst hod
    simp
  | cons a rest ih =>
    intro o hl
    have hl_rest : IsArcWalk tail head (head a) d rest := walk_tail hl
    obtain ⟨-, hhead, -, -⟩ := hl
    have htail : tail a = o := hhead a (by rw [List.head?_cons, Option.mem_def])
    have ih' := ih hl_rest
    have he := hτ a
    rw [htail] at he
    simp only [List.map_cons, List.sum_cons]
    omega
private theorem isChain_append_singleton {E : Type*} {r : E → E → Prop} {l : List E} {e : E}
    (hchain : l.IsChain r) (hboundary : ∀ g ∈ l.getLast?, r g e) :
    (l ++ [e]).IsChain r := by
  revert hchain hboundary
  induction l with
  | nil =>
    intro hchain hboundary
    simp only [List.nil_append]
    exact List.isChain_singleton e
  | cons f fs ih =>
    intro hchain hboundary
    rw [List.cons_append, List.isChain_cons]
    rw [List.isChain_cons] at hchain
    obtain ⟨hpw, hch⟩ := hchain
    refine ⟨?_, ih hch ?_⟩
    · intro x hx
      rw [List.head?_append] at hx
      obtain hx | ⟨hfs, hx⟩ := mem_of_mem_or hx
      · exact hpw x hx
      · rw [List.head?_eq_none_iff] at hfs
        subst hfs
        simp at hx
        subst hx
        exact hboundary f (by rw [List.getLast?_singleton, Option.mem_def])
    · intro g hg
      exact hboundary g (by rw [getLast?_cons_or]; exact mem_or_left hg)
private theorem isChain_middle_singleton {E : Type*} {r : E → E → Prop} {B : List E} {a : E}
    {C : List E} (h : (B ++ a :: C).IsChain r) : (B ++ [a]).IsChain r := by
  revert h
  induction B with
  | nil =>
    intro h
    simp only [List.nil_append] at h ⊢
    exact List.isChain_singleton a
  | cons b B' ih =>
    intro h
    simp only [List.cons_append] at h ⊢
    rw [List.isChain_cons] at h ⊢
    obtain ⟨hpw, hch⟩ := h
    refine ⟨?_, ih hch⟩
    intro x hx
    have hhd : (B' ++ [a]).head? = (B' ++ a :: C).head? := by simp [List.head?_append]
    rw [hhd] at hx
    exact hpw x hx
private theorem exists_append_cons_of_mem {E : Type*} {a : E} {l : List E} (h : a ∈ l) :
    ∃ B C, l = B ++ a :: C := by
  revert h
  induction l with
  | nil =>
    intro h
    simp at h
  | cons f fs ih =>
    intro h
    simp at h
    rcases h with rfl | h
    · exact ⟨[], fs, rfl⟩
    · obtain ⟨B, C, rfl⟩ := ih h
      exact ⟨f :: B, C, rfl⟩
private theorem nodup_of_isArcWalk {V E : Type*} {tail head : E → V}
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = [])
    {o d : V} {l : List E} (hl : IsArcWalk tail head o d l) : l.Nodup := by
  revert o hl
  induction l with
  | nil =>
    intro o hl
    exact List.nodup_nil
  | cons a rest ih =>
    intro o hl
    rw [List.nodup_cons]
    refine ⟨?_, ih (walk_tail hl)⟩
    intro hmem
    obtain ⟨B, C, rfl⟩ := exists_append_cons_of_mem hmem
    have hclosed : IsArcWalk tail head (head a) (head a) (B ++ [a]) := by
      have hchain' : (B ++ a :: C).IsChain (fun a b => head a = tail b) := by
        have hc := hl.2.2.1
        rw [List.isChain_cons] at hc
        exact hc.2
      refine ⟨fun _ => rfl, ?_, isChain_middle_singleton hchain', ?_⟩
      · clear hchain'
        revert hl
        cases B with
        | nil =>
          intro hl
          have hc := hl.2.2.1
          simp only [List.nil_append] at hc ⊢
          intro f hf
          rw [List.head?_cons, Option.mem_def] at hf
          simp at hf
          subst hf
          rw [List.isChain_cons] at hc
          have h2 := hc.1 a (by rw [List.head?_cons, Option.mem_def])
          exact h2.symm
        | cons b B' =>
          intro hl
          have hc := hl.2.2.1
          have hhd : ((b :: B') ++ [a]).head? = some b := by simp [List.cons_append]
          rw [hhd]
          intro f hf
          rw [Option.mem_def] at hf
          simp at hf
          subst hf
          have h1 : (a :: ((b :: B') ++ a :: C)) = a :: b :: (B' ++ a :: C) := by
            simp [List.cons_append]
          rw [h1, List.isChain_cons] at hc
          have h2 := hc.1 b (by rw [List.head?_cons, Option.mem_def])
          exact h2.symm
      · have hg : (B ++ [a]).getLast? = some a := by
          rw [List.getLast?_append, List.getLast?_singleton]
          rfl
        rw [hg]
        intro f hf
        rw [Option.mem_def] at hf
        simp at hf
        subst hf
        rfl
    have hempty := hacyc (head a) (B ++ [a]) hclosed
    simp at hempty
private theorem length_le_card_of_isArcWalk {V E : Type*} [Fintype E] {tail head : E → V}
    (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = [])
    {o d : V} {l : List E} (hl : IsArcWalk tail head o d l) :
    l.length ≤ Fintype.card E :=
  List.Nodup.length_le_card (nodup_of_isArcWalk hacyc hl)
private theorem exists_max_of_bounded : ∀ (B : ℕ) (S : Set ℕ),
    S.Nonempty → (∀ k ∈ S, k ≤ B) → ∃ m ∈ S, ∀ k ∈ S, k ≤ m := by
  intro B
  induction B with
  | zero =>
    intro S ne hB
    obtain ⟨k0, hk0⟩ := ne
    refine ⟨k0, hk0, fun k hk => ?_⟩
    have h0 : k0 = 0 := Nat.le_zero.mp (hB k0 hk0)
    have h1 : k = 0 := Nat.le_zero.mp (hB k hk)
    omega
  | succ B ih =>
    intro S ne hB
    by_cases hmem : B + 1 ∈ S
    · exact ⟨B + 1, hmem, fun k hk => hB k hk⟩
    · refine ih S ne ?_
      intro k hk
      have hle : k ≤ B + 1 := hB k hk
      have hne : k ≠ B + 1 := by
        intro heq
        rw [heq] at hk
        exact hmem hk
      omega
/-- Earliest event dates exist: in an activity-on-arc network with finitely many arcs, no
nonempty closed walk, and every event reachable from the source event `s`, some feasible
schedule puts `s` at tick `0` and every event `v` at the duration of a walk from `s` to `v`. With
the critical-path lower bound this is the earliest schedule (`τ' s + τ v ≤ τ' v` for every
feasible `τ'`), and the provided walk to each event, a sink in particular, has maximum duration
among walks from `s`. No separate finiteness hypothesis on the events is needed: by reachability
every event other than `s` is the head of an arc, so there are finitely many. A specification,
not an algorithm. -/
theorem exists_isFeasibleSchedule_eq_sum {V E : Type*} [Finite E] {tail head : E → V}
    (dur : E → ℕ) {s : V} (hacyc : ∀ v (l : List E), IsArcWalk tail head v v l → l = [])
    (hreach : ∀ v, ∃ l, IsArcWalk tail head s v l) :
    ∃ τ : V → ℕ, IsFeasibleSchedule tail head dur τ ∧ τ s = 0 ∧
      ∀ v, ∃ l, IsArcWalk tail head s v l ∧ (l.map dur).sum = τ v := by
  let _ : Fintype E := Fintype.ofFinite E
  set Dmax : ℕ := Finset.univ.sup dur with hDmax
  have hdur_le : ∀ e : E, dur e ≤ Dmax := fun e => Finset.le_sup (Finset.mem_univ e)
  have hsum_le : ∀ l : List E, (l.map dur).sum ≤ l.length * Dmax := by
    intro l
    induction l with
    | nil => simp
    | cons a l' ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.add_one_mul, Nat.add_comm (List.length l' * Dmax) Dmax]
      exact Nat.add_le_add (hdur_le a) ih
  have hlen_le : ∀ {o d : V} {l : List E},
      IsArcWalk tail head o d l → l.length ≤ Fintype.card E := by
    intro o d l hl
    exact length_le_card_of_isArcWalk hacyc hl
  have hmax : ∀ v, ∃ m, (∃ l, IsArcWalk tail head s v l ∧ (l.map dur).sum = m) ∧
      ∀ k, (∃ l, IsArcWalk tail head s v l ∧ (l.map dur).sum = k) → k ≤ m := by
    intro v
    have hne : {k : ℕ | ∃ l, IsArcWalk tail head s v l ∧ (l.map dur).sum = k}.Nonempty := by
      obtain ⟨l0, hl0⟩ := hreach v
      exact ⟨(l0.map dur).sum, l0, hl0, rfl⟩
    have hbdd : ∀ k ∈ {k : ℕ | ∃ l, IsArcWalk tail head s v l ∧ (l.map dur).sum = k},
        k ≤ Fintype.card E * Dmax := by
      intro k hk
      obtain ⟨l, hl, rfl⟩ := hk
      have hle := hlen_le hl
      have hmono : l.length * Dmax ≤ Fintype.card E * Dmax := by gcongr
      exact Nat.le_trans (hsum_le l) hmono
    obtain ⟨m, hm, hmax'⟩ := exists_max_of_bounded _ _ hne hbdd
    exact ⟨m, hm, fun k hk => hmax' k hk⟩
  refine ⟨fun v => Classical.choose (hmax v), ?_, ?_, ?_⟩
  · intro e
    show Classical.choose (hmax (tail e)) + dur e ≤ Classical.choose (hmax (head e))
    obtain ⟨l, hl, hsum⟩ := (Classical.choose_spec (hmax (tail e))).1
    have hl' : IsArcWalk tail head s (head e) (l ++ [e]) := walk_snoc hl rfl
    have hle := (Classical.choose_spec (hmax (head e))).2 ((l.map dur).sum + dur e)
      ⟨l ++ [e], hl', by simp [List.map_append, List.sum_append]⟩
    omega
  · show Classical.choose (hmax s) = 0
    obtain ⟨⟨l, hl, hsum⟩, -⟩ := Classical.choose_spec (hmax s)
    have hempty : l = [] := hacyc s l hl
    subst hempty
    simp only [List.map_nil, List.sum_nil] at hsum
    exact hsum.symm
  · intro v
    show ∃ l, IsArcWalk tail head s v l ∧ (l.map dur).sum = Classical.choose (hmax v)
    exact (Classical.choose_spec (hmax v)).1

end MathlibExt.Combinatorics.Graph.ArcNetwork
