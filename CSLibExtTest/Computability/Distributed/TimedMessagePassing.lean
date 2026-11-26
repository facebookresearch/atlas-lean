/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.TimedMessagePassing
import Mathlib.Data.Finset.Insert

/-! # Boundary tests for timed message-passing histories -/

namespace Cslib.Distributed.TimedMessagePassing

open Set

private abbrev DemoStep := Step 2 ℕ ℕ
private abbrev Demo := History 2 ℕ ℕ
private abbrev pos (t i : ℕ) : Position := toLex (t, i)
private abbrev firstSend := pos 0 0
private abbrev secondSend := pos 1 0
private abbrev firstReceive := pos 1 1

@[local simp] private theorem ofLex_pair (t i : ℕ) :
    ofLex ((t, i) : Position) = (t, i) := rfl

private theorem toLex_pair (t i : ℕ) :
    pos t i = ((t, i) : Position) := rfl

private def input : Fin 2 → ℕ := fun _ ↦ 0

private def protocol : Protocol 2 ℕ ℕ ℕ where
  init := fun _ v ↦ v
  instruction p s :=
    if p = 0 then .send 1 7 (s + 1) else .receive (fun ms ↦ s + ms.card)

private def send (next : ℕ) : DemoStep := ⟨0, .send 1 7, next⟩
private def recv (ids : Finset Position) (next : ℕ) : DemoStep := ⟨1, .receive ids, next⟩

private def history (second later : List DemoStep) : Demo where
  initial := input
  steps
    | 0 => [send 1]
    | 1 => second
    | _ + 2 => later

-- The two sends have identical endpoints and payloads but different addresses.
private def demo (ids : Finset Position) (next : ℕ) : Demo :=
  history [send 2, recv ids next] [recv ∅ next]

private def both : Finset Position := {firstSend, secondSend}
private def good : Demo := demo both 2
private def skipped : Demo := demo ∅ 0
private def idle : Demo := history [] []

private theorem demo_send_iff {ids : Finset Position} {next : ℕ} {x : Position}
    {q p : Fin 2} {m : ℕ} :
    (demo ids next).sendAt? x = some (q, p, m) ↔
      (x = firstSend ∨ x = secondSend) ∧ q = 0 ∧ p = 1 ∧ m = 7 := by
  rcases x with ⟨(_ | _ | t), (_ | _ | i)⟩ <;>
    simp [History.sendAt?, History.stepAt?, Position.tick, toLex_pair, demo, history, send, recv] <;>
    grind

private theorem demo_receive_iff {ids ds : Finset Position} {next : ℕ} {x : Position}
    {p : Fin 2} : (demo ids next).receiveAt? x = some (p, ds) ↔
      p = 1 ∧ (x = firstReceive ∧ ds = ids ∨ (∃ t, x = pos (t + 2) 0) ∧ ds = ∅) := by
  rcases x with ⟨(_ | _ | t), (_ | _ | i)⟩ <;>
    simp [History.receiveAt?, History.stepAt?, Position.tick, toLex_pair, demo, history, send,
      recv] <;> grind

private theorem demo_delivered_iff {ids : Finset Position} {next : ℕ} {sent x : Position} :
    (demo ids next).DeliveredAt sent x ↔ x = firstReceive ∧ sent ∈ ids := by
  constructor
  · rintro ⟨_, _, hr, hmem⟩
    rcases (demo_receive_iff.mp hr).2 with ⟨rfl, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨rfl, hmem⟩
    · simp at hmem
  · rintro ⟨rfl, hmem⟩
    exact ⟨1, ids, rfl, hmem⟩

private theorem demo_wellFormed (ids : Finset Position) (next : ℕ)
    (hids : ∀ i ∈ ids, i = firstSend ∨ i = secondSend) : (demo ids next).WellFormed := by
  constructor
  · rintro (_ | _ | t) <;> simp [demo, history, send, recv]
  · intro x p ds hrec sent hsent
    obtain ⟨rfl, hx | hx⟩ := demo_receive_iff.mp hrec
    · obtain ⟨rfl, rfl⟩ := hx
      refine ⟨⟨0, 7, demo_send_iff.mpr ⟨hids sent hsent, rfl, rfl, rfl⟩⟩, ?_, ?_⟩
      · rcases hids sent hsent with rfl | rfl <;> decide
      · intro y hy hd
        exact (lt_irrefl firstReceive) ((demo_delivered_iff.mp hd).1 ▸ hy)
    · obtain ⟨_, rfl⟩ := hx
      exact (Finset.notMem_empty _ hsent).elim

example : good.WellFormed := by
  apply demo_wellFormed
  simp [both]

example : skipped.WellFormed := demo_wellFormed ∅ 0 (by simp)

example : good.DeliveredAt firstSend firstReceive ∧ good.DeliveredAt secondSend firstReceive := by
  simp [good, demo_delivered_iff, both]

example : ¬ good.Lost firstSend := by
  rintro ⟨_, _, _, _, _, hnever⟩
  exact hnever firstReceive (by simp [good, demo_delivered_iff, both])

-- A later address at the very same tick is not an earlier send.
example : ¬ (history [recv {pos 1 1} 0, send 2] []).WellFormed := by
  intro h
  have hp := h.receivePending (pos 1 0) 1 {pos 1 1} rfl (by simp : pos 1 1 ∈ _)
  exact (by decide : ¬ pos 1 1 < pos 1 0) hp.2.1

-- The sender cannot take a send addressed to the other processor.
example : ¬ (history [⟨0, .receive {firstSend}, 0⟩] []).WellFormed := by
  intro h
  have hp := h.receivePending (pos 1 0) 0 {firstSend} rfl (by simp : firstSend ∈ _)
  obtain ⟨q, m, hs⟩ := hp.1
  change some ((0 : Fin 2), 1, 7) = some (q, 0, m) at hs
  simp at hs

-- A receive cannot deliver an address where no step exists.
example : ¬ (history [recv {pos 0 1} 0] []).WellFormed := by
  intro h
  have hp := h.receivePending (pos 1 0) 1 {pos 0 1} rfl (by simp : pos 0 1 ∈ _)
  obtain ⟨q, m, hs⟩ := hp.1
  change none = some (q, (1 : Fin 2), m) at hs
  cases hs

example : ¬ (history [send 2, send 3] []).WellFormed := by
  intro h
  simpa [history, send] using h.oncePerTick 1

example : ¬ (history [recv {firstSend} 1] [recv {firstSend} 2]).WellFormed := by
  intro h
  have hd₁ : (history [recv {firstSend} 1] [recv {firstSend} 2]).DeliveredAt firstSend (pos 1 0) :=
    ⟨1, {firstSend}, rfl, by simp⟩
  have hd₂ : (history [recv {firstSend} 1] [recv {firstSend} 2]).DeliveredAt firstSend (pos 2 0) :=
    ⟨1, {firstSend}, rfl, by simp⟩
  exact (by decide : pos 1 0 ≠ pos 2 0) (h.delivery_unique hd₁ hd₂)

private theorem demo_sender_conforms (ids : Finset Position) (next : ℕ) :
    (demo ids next).Conforms protocol input 0 := by
  refine ⟨rfl, ?_⟩
  rintro ⟨(_ | _ | t), (_ | _ | i)⟩ s hs hp <;>
    simp [History.stepAt?, Position.tick, demo, history, send, recv] at hs <;>
    subst s <;> first | exact ⟨rfl, rfl, rfl⟩ | exact (by decide : (1 : Fin 2) ≠ 0) hp

private theorem demo_receiver_conforms (ids : Finset Position) (next : ℕ)
    (hnext : next = ((demo ids next).batch ids).card) : (demo ids next).Conforms protocol input 1 := by
  refine ⟨rfl, ?_⟩
  rintro ⟨(_ | _ | t), (_ | _ | i)⟩ s hs hp <;>
    simp [History.stepAt?, Position.tick, demo, history, send, recv] at hs <;> subst s
  · exact (by decide : (0 : Fin 2) ≠ 1) hp
  · exact (by decide : (0 : Fin 2) ≠ 1) hp
  · change next = 0 + ((demo ids next).batch ids).card
    simpa only [Nat.zero_add] using hnext
  · cases t <;> rfl

example : good.Conforms protocol input 0 := demo_sender_conforms both 2

private theorem good_receiver_correct : good.Correct protocol input 1 := by
  refine ⟨demo_receiver_conforms both 2 (by decide), ?_⟩
  intro t
  exact ⟨t + 2, by omega, recv ∅ 2, by simp [good, demo, history], rfl⟩

-- Counting just one equal payload would give the wrong successor state.
example : ¬ (demo both 1).Conforms protocol input 1 := by
  intro h
  have hbad : (1 : ℕ) = 2 := h.2 firstReceive (recv both 1) rfl rfl
  omega

example : ¬ ({ good with steps := fun _ ↦ [⟨0, .send 1 8, 1⟩] } : Demo).Conforms
    protocol input 0 := by
  intro h
  have hbad : (7 : ℕ) = 8 := (h.2 firstSend ⟨0, .send 1 8, 1⟩ rfl rfl).2.1
  omega

example : ¬ good.Conforms protocol (fun _ ↦ 1) 0 := by
  intro h
  exact (by decide : (0 : ℕ) ≠ 1) h.1

private theorem demo_lost_iff {ids : Finset Position} {next : ℕ} {sent : Position}
    (hsent : sent = firstSend ∨ sent = secondSend) :
    (demo ids next).Lost sent ↔ sent ∉ ids := by
  constructor
  · rintro ⟨_, _, _, _, _, hnever⟩ hmem
    exact hnever firstReceive (demo_delivered_iff.mpr ⟨rfl, hmem⟩)
  · intro hmem
    refine ⟨0, 1, 7, demo_send_iff.mpr ⟨hsent, rfl, rfl, rfl⟩, ?_, ?_⟩
    · intro t
      exact ⟨pos (t + 2) 0, ∅, by change t ≤ t + 2; omega, rfl⟩
    · intro x hd
      exact hmem (demo_delivered_iff.mp hd).2

example : skipped.Lost firstSend :=
  (demo_lost_iff (Or.inl rfl)).mpr (by simp)

-- Delivering the first occurrence does not deliver the second one's equal payload.
example : ¬ (demo {firstSend} 1).Lost firstSend ∧ (demo {firstSend} 1).Lost secondSend := by
  rw [demo_lost_iff (Or.inl rfl), demo_lost_iff (Or.inr rfl)]
  exact ⟨not_not_intro (by simp), by decide⟩

private theorem idle_noReceive (x : Position) : idle.receiveAt? x = none := by
  rcases x with ⟨(_ | _ | t), (_ | i)⟩ <;> rfl

example : idle.WellFormed := by
  constructor
  · rintro (_ | _ | t) <;> simp [idle, history, send]
  · intro x p ds hrec
    simp [idle_noReceive] at hrec

-- A send stays undelivered here, but the receiver is never scheduled, so it is not lost.
example : ¬ idle.Lost firstSend := by
  rintro ⟨_, _, _, _, hinf, _⟩
  obtain ⟨x, _, _, hx⟩ := hinf 0
  simp [idle_noReceive] at hx

example : idle.CommunicationBound univ 1 := by
  refine ⟨by decide, ?_⟩
  intro _ x _ _ _ _ _ hrec
  simp [idle_noReceive] at hrec

-- The receive exactly at send tick + Δ meets the bound on the closed interval.
example : good.CommunicationBound (Icc 0 1) 1 := by
  refine ⟨by decide, ?_⟩
  intro sent x q p m ids hs hr _ hI hΔ
  obtain ⟨_, hx | hx⟩ := demo_receive_iff.mp hr
  · obtain ⟨rfl, _⟩ := hx
    refine ⟨firstReceive, le_rfl, demo_delivered_iff.mpr ⟨rfl, ?_⟩⟩
    rcases (demo_send_iff.mp hs).1 with rfl | rfl <;> simp [both]
  · obtain ⟨⟨t, rfl⟩, _⟩ := hx
    have : t + 2 ≤ 1 := hI.2
    omega

example : ¬ skipped.CommunicationBound (Icc 0 1) 1 := by
  intro h
  obtain ⟨x, _, hx⟩ := h.2 firstSend firstReceive 0 1 7 ∅ rfl rfl
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)
  simp [skipped, demo_delivered_iff] at hx

-- Hold the same history fixed but exclude the receive endpoint.
example : skipped.CommunicationBound (Ico 0 1) 1 := by
  refine ⟨by decide, ?_⟩
  intro sent x q p m ids hs hr _ hI _
  obtain ⟨_, ⟨rfl, _⟩ | ⟨⟨t, rfl⟩, _⟩⟩ := demo_receive_iff.mp hr
  · exact (by decide : ¬ firstReceive.tick < 1) hI.2 |>.elim
  · have : t + 2 < 1 := hI.2
    omega

-- With Δ = 2 the receive at tick 2 does not obligate delivery of a send before I.
example : skipped.CommunicationBound (Icc 1 2) 2 := by
  refine ⟨by decide, ?_⟩
  intro sent x q p m ids hs _ hsent hrec hΔ
  rcases (demo_send_iff.mp hs).1 with rfl | rfl
  · exact (by decide : ¬ 1 ≤ firstSend.tick) hsent.1 |>.elim
  · have h : secondSend.tick = 1 := rfl
    have : x.tick ≤ 2 := hrec.2
    omega

private theorem receiver_of_ne_sender {p : Fin 2} (hp : p ≠ 0) : p = 1 :=
  Fin.eq_of_val_eq (by
    have : p.val ≠ 0 := fun h0 ↦ hp (Fin.eq_of_val_eq h0)
    have := p.isLt
    omega)

example : good.ProcessorBound protocol input (Icc 0 1) 2 := by
  refine ⟨by decide, ?_⟩
  intro t hwin p _
  have h : t + 1 ∈ Ico t (t + 2) := ⟨by omega, by omega⟩
  have ht : t + 1 ≤ 1 := (hwin h).2
  have : t = 0 := by omega
  subst t
  refine ⟨1, ⟨by decide, by decide⟩, ?_⟩
  by_cases hp : p = 0
  · exact ⟨send 2, by simp [good, demo, history], hp.symm⟩
  · exact ⟨recv both 2, by simp [good, demo, history], (receiver_of_ne_sender hp).symm⟩

-- Only the receiver is correct after the sender's finite, conforming activity.
example : good.ProcessorBound protocol input (Ico 2 3) 1 := by
  refine ⟨by decide, ?_⟩
  intro t hwin p hcorrect
  have ht : t ∈ Ico t (t + 1) := ⟨le_rfl, by omega⟩
  have hI : 2 ≤ t ∧ t < 3 := hwin ht
  have : t = 2 := by omega
  subst t
  have hp : p ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, s, hs, hproc⟩ := hcorrect.2 2
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = k + 2 := ⟨u - 2, by omega⟩
    simp [good, demo, history] at hs
    subst s
    exact (by decide : (1 : Fin 2) ≠ 0) hproc
  exact ⟨2, ht, recv ∅ 2, by simp [good, demo, history], (receiver_of_ne_sender hp).symm⟩

-- The correct receiver misses the one-tick window [0, 1); its tick-1 step does not count.
example : ¬ good.ProcessorBound protocol input (Icc 0 1) 1 := by
  intro h
  have hwin : Ico (0 : ℕ) (0 + 1) ⊆ Icc 0 1 := fun _ h ↦ ⟨h.1, (Nat.le_of_lt h.2).trans (by decide)⟩
  obtain ⟨u, hu, hs⟩ := h.2 0 hwin 1 good_receiver_correct
  have hu' : u = 0 := by have : u < 0 + 1 := hu.2; omega
  subst u
  simp [History.StepsAt, good, demo, history, send] at hs

example : good.ProcessorBound protocol input (Ico 0 1) 2 := by
  refine ⟨by decide, ?_⟩
  intro t hwin
  have h : t + 1 ∈ Ico t (t + 2) := ⟨by omega, by omega⟩
  have : t + 1 < 1 := (hwin h).2
  omega

example : ¬ good.ProcessorBound protocol input (Icc 0 1) 0 := by
  intro h
  exact (by decide : ¬ (0 : ℕ) < 0) h.1

end Cslib.Distributed.TimedMessagePassing
