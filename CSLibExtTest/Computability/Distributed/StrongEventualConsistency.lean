/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.StrongEventualConsistency
import Mathlib.Data.Finset.Insert

/-!
# Strong eventual consistency fixtures

Two replicas observe one identified update. Only the first bit of each payload is observable;
the second bit is the replica identity. The fixtures vary delivery, visibility and completion
independently, with delivery and visibility times given as step indices (before the next snapshot).
-/

namespace Cslib.Distributed.Replication.Tests

private abbrev Schedule := Bool → Option ℕ

private def seen (schedule : Schedule) (t : ℕ) (r : Bool) : Bool :=
  match schedule r with
  | none => false
  | some k => decide (k < t)

private def reads : Setoid (Bool × Bool) where
  r a b := a.1 = b.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

-- The first three steps have atomic methods. A method started at step 3 may stay pending.
private def trace (arrival visible : Schedule) (finishes : Bool → Bool) :
    History Bool Unit (Bool × Bool) where
  correct := fun _ => True
  states := ⟨fun t r => (seen visible t r, r)⟩
  deliveries := ⟨fun k r => if arrival r = some k then {()} else ∅⟩
  started := fun _ t => t < 3 ∨ t = 3
  completion := fun r t =>
    if t < 3 then some t else if t = 3 ∧ finishes r = true then some 4 else none
  completion_valid := by
    intro r t u h
    by_cases hearly : t < 3
    · simp only [ite_eq_left hearly, Option.some.injEq] at h
      exact ⟨Or.inl hearly, h.le⟩
    · simp only [ite_eq_right hearly] at h
      split at h
      · rename_i hfinish
        cases h
        exact ⟨Or.inr hfinish.1, by omega⟩
      · cases h

private def arrival : Schedule
  | false => some 0
  | true => some 1

private def delayed : Schedule
  | false => some 0
  | true => some 2

private def missing : Schedule
  | false => some 0
  | true => none

private def finishesAll : Bool → Bool := fun _ => true

private theorem delivered_iff (arr vis : Schedule) (finishes : Bool → Bool) (r : Bool) (t : ℕ) :
    () ∈ (trace arr vis finishes).delivered r t ↔ seen arr t r = true := by
  change (∃ k < t, () ∈ (if arr r = some k then {()} else ∅ : Finset Unit)) ↔ _
  cases harr : arr r with
  | none => simp [seen, harr]
  | some n =>
    simp only [seen, harr, decide_eq_true_eq, Option.some.injEq]
    constructor
    · rintro ⟨k, hkt, hk⟩
      by_cases h : n = k
      · simpa [h] using hkt
      · simp [h] at hk
    · intro hn
      exact ⟨n, hn, by simp⟩

private theorem delivered_eq_iff (arr vis : Schedule) (finishes : Bool → Bool)
    (i j : Bool) (t s : ℕ) :
    (trace arr vis finishes).delivered i t = (trace arr vis finishes).delivered j s ↔
      seen arr t i = seen arr s j := by
  constructor
  · intro h
    have hSeen : (seen arr t i = true) ↔ seen arr s j = true := by
      rw [← delivered_iff arr vis finishes i t, ← delivered_iff arr vis finishes j s, h]
    cases hi : seen arr t i <;> cases hj : seen arr s j <;> simp_all
  · intro h
    ext u
    cases u
    rw [delivered_iff, delivered_iff, h]

private theorem bothSeen (t : ℕ) (ht : 2 ≤ t) (r : Bool) : seen arrival t r = true := by
  cases r
  · exact decide_eq_true (show 0 < t by omega)
  · exact decide_eq_true (show 1 < t by omega)

private theorem allDelivered (vis : Schedule) (finishes : Bool → Bool) :
    EventualDelivery (trace arrival vis finishes) := by
  intro i j _ _ t u _
  cases u
  exact ⟨max t 2, le_max_left t 2, (delivered_iff arrival vis finishes j (max t 2)).2
    (bothSeen _ (le_max_right t 2) _)⟩

private theorem allFinish (arr vis : Schedule) : Termination (trace arr vis finishesAll) := by
  intro r t ht
  change t < 3 ∨ t = 3 at ht
  rcases ht with ht | rfl
  · exact ⟨t, le_rfl, by simp [trace, ht]⟩
  · exact ⟨4, by decide, rfl⟩

private theorem strongWhenVisible (arr : Schedule) (finishes : Bool → Bool) :
    StrongConvergence (trace arr arr finishes) reads := by
  intro i j _ _ t s h
  exact (delivered_eq_iff arr arr finishes i j t s).1 h

-- A receives at step 0; B receives at step 1 but exposes the update only after step 2.
private def eventual : History Bool Unit (Bool × Bool) := trace arrival delayed finishesAll

private theorem equalTail (t : ℕ) (ht : 2 ≤ t) :
    eventual.delivered false t = eventual.delivered true t :=
  (delivered_eq_iff _ _ _ _ _ _ _).2 ((bothSeen t ht false).trans (bothSeen t ht true).symm)

example : EventualConsistency eventual reads := by
  refine ⟨allDelivered _ _, ?_, allFinish _ _⟩
  intro i j _ _ t _
  refine ⟨max t 3, le_max_left t 3, ?_⟩
  intro k hk
  have hk3 := le_trans (le_max_right t 3) hk
  have hVisible (r : Bool) : seen delayed k r = true := by
    cases r
    · exact decide_eq_true (show 0 < k by omega)
    · exact decide_eq_true (show 2 < k by omega)
  exact (hVisible i).trans (hVisible j).symm

example : () ∈ eventual.delivered false 2 ∧ () ∈ eventual.delivered true 2 :=
  ⟨(delivered_iff _ _ _ _ _).2 rfl, (delivered_iff _ _ _ _ _).2 rfl⟩

example : ¬ StrongEventualConsistency eventual reads := by
  intro h
  have bad : true = false := h.2.1 false true trivial trivial 2 2 (equalTail 2 le_rfl)
  cases bad

-- If both replicas change visibility together, same-tick agreement is not enough for SEC.
private def together : History Bool Unit (Bool × Bool) :=
  trace arrival (fun _ => some 2) finishesAll

example : ∀ t, reads.r (together.states t false) (together.states t true) := fun _ => rfl

example : ¬ StrongConvergence together reads := by
  intro h
  have hDelivered : together.delivered false 2 = together.delivered true 3 :=
    (delivered_eq_iff _ _ _ _ _ _ _).2 rfl
  have bad : false = true := h false true trivial trivial 2 3 hDelivered
  cases bad

-- B never receives the update, although all methods finish and equal sets imply equivalence.
private def lost : History Bool Unit (Bool × Bool) := trace missing missing finishesAll

example : StrongConvergence lost reads ∧ Termination lost ∧ ¬ EventualDelivery lost := by
  refine ⟨strongWhenVisible _ _, allFinish _ _, ?_⟩
  intro h
  obtain ⟨t, _, ht⟩ := h false true trivial trivial 1 () ((delivered_iff _ _ _ _ _).2 rfl)
  have bad : false = true := (delivered_iff missing missing finishesAll true t).1 ht
  cases bad

-- If only one of A or B is correct, the other is neither an obligated source nor a recipient.
example (r : Bool) : EventualDelivery { lost with correct := (· = r) } := by
  intro i j hi hj t u hu
  change i = r at hi
  change j = r at hj
  subst i j
  exact ⟨t, le_rfl, hu⟩

-- An incomplete method is a distinct failure even when delivery and strong convergence hold.
private def stuck : History Bool Unit (Bool × Bool) := trace arrival arrival not

private theorem stuckDoesNotTerminate : ¬ Termination stuck := by
  intro h
  obtain ⟨t, _, ht⟩ := h true 3 (Or.inr rfl)
  change none = some t at ht
  cases ht

example : EventualDelivery stuck ∧ StrongConvergence stuck reads ∧ ¬ Termination stuck :=
  ⟨allDelivered _ _, strongWhenVisible _ _, stuckDoesNotTerminate⟩

-- The termination clause says all executions, including those at a replica not marked correct.
example : ¬ Termination { stuck with correct := (· = false) } := stuckDoesNotTerminate

private def good : History Bool Unit (Bool × Bool) := trace arrival arrival finishesAll

private theorem goodSEC : StrongEventualConsistency good reads :=
  ⟨allDelivered _ _, strongWhenVisible _ _, allFinish _ _⟩

example : EventualConsistency good reads := goodSEC.eventualConsistency

-- Equal delivered sets and equivalent observations can occur at different ticks, with unequal
-- raw payloads. At snapshot 1, A has the update and B does not yet have it.
example : good.states 1 false ≠ good.states 2 true ∧
    reads.r (good.states 1 false) (good.states 2 true) ∧
    () ∈ good.delivered false 1 ∧ () ∉ good.delivered true 1 := by
  refine ⟨by decide, goodSEC.2.1 false true trivial trivial 1 2 ?_, ?_, ?_⟩
  · exact (delivered_eq_iff _ _ _ _ _ _ _).2 rfl
  · exact (delivered_iff _ _ _ _ _).2 rfl
  · intro h
    have bad : false = true := (delivered_iff arrival arrival finishesAll true 1).1 h
    cases bad

end Cslib.Distributed.Replication.Tests
