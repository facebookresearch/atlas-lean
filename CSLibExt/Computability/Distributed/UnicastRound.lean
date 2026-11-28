/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Distributed.LamportClock

@[expose] public section

/-!
# Causality in a round of unicast messages

Let a list of pairs specify which processes send to which recipients, counting repeated
pairs as separate messages. Give each process a marker before all sends and another after all
receipts. In the resulting Lamport execution an initial marker precedes a final marker exactly
when they are on the same process or the list contains a message between their processes.
There is no transitive propagation through a second message: all sends precede all receipts.
-/

namespace Cslib.Distributed.UnicastRound

open LamportClock

/-- Each send position of an execution is named by at most one receipt position. Unlike
`WellFormed`, this condition excludes two different events receiving the same message. -/
def SingleDelivery {P : Type*} (tr : List (Event P)) : Prop :=
  ∀ {i j k : ℕ} {ej ek : Event P}, tr[j]? = some ej → tr[k]? = some ek →
    ej.recvFrom = some i → ek.recvFrom = some i → j = k

variable {n : ℕ} (links : List (Fin n × Fin n))

/-- A finite execution on `n` processes for an ordered list of unicast messages. It consists
of one initial marker per process, one send per list entry, the corresponding receipts in the
same order, and one final marker per process. Entry `k` has its own send at position `n + k`. -/
def execution : List (Event (Fin n)) :=
  let markers := List.ofFn fun p : Fin n => (⟨p, none⟩ : Event (Fin n))
  let sends := List.ofFn fun k : Fin links.length => (⟨links[k].1, none⟩ : Event (Fin n))
  let receipts := List.ofFn fun k : Fin links.length =>
    (⟨links[k].2, some (n + k)⟩ : Event (Fin n))
  markers ++ (sends ++ (receipts ++ markers))

/-- The round has two events per process for its markers and two per listed message. -/
@[simp] theorem length_execution :
    (execution links).length = n + links.length + links.length + n := by
  simp [execution, Nat.add_assoc]

/-- Position of process `p`'s initial marker, before every send in the round. -/
def first (p : Fin n) : Fin (execution links).length :=
  ⟨p, by rw [length_execution]; omega⟩

/-- Position of process `p`'s final marker, after every receipt in the round. -/
def last (p : Fin n) : Fin (execution links).length :=
  ⟨n + links.length + links.length + p, by rw [length_execution]; omega⟩

private theorem get_first (p : Fin n) :
    (execution links)[p.val]? = some ⟨p, none⟩ := by
  simp [execution, List.getElem?_append, p.isLt]

private theorem get_send (k : Fin links.length) :
    (execution links)[n + k.val]? = some ⟨links[k].1, none⟩ := by
  simp [execution, List.getElem?_append, k.isLt]

private theorem get_recv (k : Fin links.length) :
    (execution links)[n + links.length + k.val]? = some ⟨links[k].2, some (n + k)⟩ := by
  simp [execution, List.getElem?_append, Nat.add_assoc, k.isLt]

private theorem get_last (p : Fin n) :
    (execution links)[n + links.length + links.length + p.val]? = some ⟨p, none⟩ := by
  simp [execution, Nat.add_assoc, p.isLt]

private theorem receipt_slot {j i : ℕ} {e : Event (Fin n)} (hj : (execution links)[j]? = some e)
    (hr : e.recvFrom = some i) : ∃ k : Fin links.length,
      j = n + links.length + k ∧ i = n + k ∧ e.proc = links[k].2 := by
  have hjlen := (List.getElem?_eq_some_iff.mp hj).1
  rw [length_execution] at hjlen
  by_cases h₁ : j < n
  · rw [get_first links ⟨j, h₁⟩] at hj
    cases Option.some.inj hj; cases hr
  by_cases h₂ : j < n + links.length
  · let k : Fin links.length := ⟨j - n, by omega⟩
    have he : j = n + k := by dsimp [k]; omega
    rw [he, get_send] at hj
    cases Option.some.inj hj; cases hr
  by_cases h₃ : j < n + links.length + links.length
  · let k : Fin links.length := ⟨j - (n + links.length), by omega⟩
    have he : j = n + links.length + k := by dsimp [k]; omega
    rw [he, get_recv] at hj
    cases Option.some.inj hj
    exact ⟨k, he, (Option.some.inj hr).symm, rfl⟩
  · let p : Fin n := ⟨j - (n + links.length + links.length), by omega⟩
    have he : j = n + links.length + links.length + p := by dsimp [p]; omega
    rw [he, get_last] at hj
    cases Option.some.inj hj; cases hr

/-- Every receipt in the round names an earlier send. -/
theorem wellFormed : WellFormed (execution links) := by
  intro j ej i hj hr
  obtain ⟨k, rfl, rfl, -⟩ := receipt_slot links hj hr
  have := k.isLt
  omega

/-- No two different receipts in the round name the same send, even for repeated pairs of
processes in the message list. -/
theorem singleDelivery : SingleDelivery (execution links) := by
  intro i j l ej el hj hl hr hs
  obtain ⟨k, rfl, hi, -⟩ := receipt_slot links hj hr
  obtain ⟨t, rfl, ht, -⟩ := receipt_slot links hl hs
  omega

-- A change of process uses one link crossing the cut between sends and receipts.
private def Reach (i j : ℕ) (p q : Fin n) : Prop :=
  p = q ∨ i < n + links.length ∧ n + links.length ≤ j ∧ (p, q) ∈ links

private theorem step_reach {i j : ℕ} {ei ej : Event (Fin n)}
    (h : Step (execution links) i j) (hi : (execution links)[i]? = some ei)
    (hj : (execution links)[j]? = some ej) : Reach links i j ei.proc ej.proc := by
  obtain ⟨-, ei', ej', hi', hj', hp⟩ := h
  obtain rfl := Option.some.inj (hi'.symm.trans hi)
  obtain rfl := Option.some.inj (hj'.symm.trans hj)
  rcases hp with hp | hr
  · exact Or.inl hp
  · obtain ⟨k, rfl, rfl, hq⟩ := receipt_slot links hj hr
    rw [get_send] at hi
    cases Option.some.inj hi
    refine Or.inr ⟨Nat.add_lt_add_left k.isLt _, Nat.le_add_right .., ?_⟩
    simp [hq]

private theorem hb_reach {i j : ℕ} (h : HappensBefore (execution links) i j) :
    ∀ {ei ej}, (execution links)[i]? = some ei → (execution links)[j]? = some ej →
      Reach links i j ei.proc ej.proc := by
  induction h with
  | single hs => exact fun hi hj => step_reach links hs hi hj
  | tail hab hbc ih =>
    intro ea ec ha hc
    obtain ⟨eb, hb⟩ := (HappensBefore.exists_events hab).2
    rcases ih ha hb with hp | ⟨haCut, hbCut, habLink⟩ <;>
      rcases step_reach links hbc hb hc with hq | ⟨hbCut', hcCut, hbcLink⟩
    · exact Or.inl (hp.trans hq)
    · exact Or.inr ⟨(HappensBefore.lt hab).trans hbCut', hcCut, hp.symm ▸ hbcLink⟩
    · exact Or.inr ⟨haCut, hbCut.trans hbc.1.le, hq ▸ habLink⟩
    · exact (not_lt_of_ge hbCut hbCut').elim

/-- An initial marker precedes a final marker exactly for a common process or a listed
sender–recipient pair. In particular, two messages sharing an intermediate process do not
introduce an extra comparison. -/
theorem first_before_last_iff (p q : Fin n) :
    HappensBefore (execution links) (first links p) (last links q) ↔ p = q ∨ (p, q) ∈ links := by
  constructor
  · intro h
    rcases hb_reach links h (get_first links p) (get_last links q) with hp | ⟨-, -, hpq⟩
    · exact Or.inl hp
    · exact Or.inr hpq
  · rintro (rfl | hpq)
    · exact .single ⟨by simp only [first, last]; omega, _, _, get_first links p,
        get_last links p, Or.inl rfl⟩
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp hpq
      have hk' : links[k] = (p, q) := hk
      have h₁ : Step (execution links) (first links p) (n + k.val) :=
        ⟨by simp only [first]; omega, _, _, get_first links p, get_send links k,
          Or.inl (by simp [hk'])⟩
      have h₂ : Step (execution links) (n + k.val) (n + links.length + k.val) :=
        ⟨by have := k.isLt; omega, _, _, get_send links k, get_recv links k, Or.inr rfl⟩
      exact .tail (.tail (.single h₁) h₂) ⟨by simp only [last]; have := k.isLt; omega, _, _,
        get_recv links k, get_last links q, Or.inl (by simp [hk'])⟩

/-- No two initial markers stand in the strict happened-before relation. -/
theorem not_first_before_first (p q : Fin n) :
    ¬ HappensBefore (execution links) (first links p) (first links q) := by
  intro h
  rcases hb_reach links h (get_first links p) (get_first links q) with hp | ⟨-, hq, -⟩
  · exact h.lt.ne (congrArg (fun t => (first links t).val) hp)
  · simp only [first] at hq; omega

/-- No two final markers stand in the strict happened-before relation. -/
theorem not_last_before_last (p q : Fin n) :
    ¬ HappensBefore (execution links) (last links p) (last links q) := by
  intro h
  rcases hb_reach links h (get_last links p) (get_last links q) with hp | ⟨hp, -⟩
  · exact h.lt.ne (congrArg (fun t => (last links t).val) hp)
  · simp only [last] at hp; omega

/-- No final marker precedes any initial marker. -/
theorem not_last_before_first (p q : Fin n) :
    ¬ HappensBefore (execution links) (last links p) (first links q) := by
  intro h
  have := h.lt
  simp only [last, first] at this
  omega

/-- All `2n` marker positions in the round are distinct: the map sending a left process to
its initial marker and a right process to its final marker is injective. -/
theorem markers_injective : Function.Injective (Sum.elim (first links) (last links)) := by
  intro x y h
  have hv := congrArg Fin.val h
  cases x with
  | inl p => cases y with
    | inl q => exact congrArg Sum.inl (Fin.ext hv)
    | inr q => simp only [Sum.elim_inl, Sum.elim_inr, first, last] at hv; omega
  | inr p => cases y with
    | inl q => simp only [Sum.elim_inl, Sum.elim_inr, first, last] at hv; omega
    | inr q =>
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [Sum.elim_inr, last] at hv
      omega

end Cslib.Distributed.UnicastRound
