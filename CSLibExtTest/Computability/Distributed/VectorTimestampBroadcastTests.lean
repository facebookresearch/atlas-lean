/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.VectorTimestampBroadcastCorrectness
import Mathlib.Data.Fintype.Pi

/-!
# A three-process execution of vector-timestamp causal broadcast

A and B send independent first messages with the same payload. B receives and delivers A's
message before sending a second message. C receives that dependent message first. Even after
C delivers B's first message, it must still await A's. The complete schedule includes each
transport echo, all remote deliveries, and an infinite idle tail. The tests certify its local
transition guards, canonical transport and inspection fairness, not just its printed outputs.
-/

namespace Cslib.Distributed.VectorTimestampBroadcast.Tests

open ReliableBroadcast

private abbrev Site := Fin 3
private abbrev Wire := Packet Site Unit
private abbrev S := Step Site Unit

-- Cache equality of finite-domain tags for the nested bounded quantifiers in the trace checker.
private instance : DecidableEq Wire := inferInstanceAs (DecidableEq (Message Site Unit × (Site → ℕ)))

private def x : Wire := (⟨0, 0, ()⟩, fun _ => 0)
private def y : Wire := (⟨1, 0, ()⟩, fun _ => 0)
private def z : Wire := (⟨1, 1, ()⟩, fun r => if r = 2 then 0 else 1)

private def script : List S := [
  .send x, .send y, .receive 1 x, .inspect 1 x true, .send z,
  .receive 2 z, .inspect 2 z false, .receive 2 y, .inspect 2 y true, .inspect 2 z false,
  .receive 2 x, .inspect 2 x true, .inspect 2 z true,
  .receive 0 y, .inspect 0 y true, .receive 0 z, .inspect 0 z true,
  .receive 0 x, .receive 1 y, .receive 1 z]

private def run : Trace Site Unit := fun t => script[t]?.getD .idle
private abbrev Cut := Fin script.length

private theorem idle {t : ℕ} (h : script.length ≤ t) : run t = .idle := by
  simp [run, List.getElem?_eq_none h]

private instance : DecidableEq S := fun s s' => by
  cases s <;> cases s' <;> first
    | exact isTrue rfl
    | exact decidable_of_iff' _ (Iff.of_eq (Step.send.injEq _ _))
    | exact decidable_of_iff' _ (Iff.of_eq (Step.receive.injEq _ _ _ _))
    | exact decidable_of_iff' _ (Iff.of_eq (Step.inspect.injEq _ _ _ _ _ _))
    | exact decidable_of_iff' _ (Iff.of_eq (Step.crash.injEq _ _))
    | exact isFalse (by intro h; cases h)

private instance (t : ℕ) (s : S) : Decidable (Admissible run t s) := by
  cases s <;> dsimp only [Admissible, Pending, Fits] <;> infer_instance

private theorem legal : Legal run := by
  have table : ∀ i : Cut, Admissible run i (run i) := by decide
  intro t
  by_cases ht : t < script.length
  · exact table ⟨t, ht⟩
  · rw [idle (by omega : script.length ≤ t)]
    simp [Admissible, Step.actor]

-- For each actual receipt in the script: a strictly earlier matching send, unique receipt at
-- the site, and a copy for each site. Also check that every send has its transport self-echo.
private def Row (i : Cut) : S → Prop
  | .send w => ∃ j : Cut, i.val ≤ j.val ∧ run j = .receive w.1.sender w
  | .receive p w => (∃ j : Cut, j.val < i.val ∧ run j = .send w) ∧
      (∀ j : Cut, run j = .receive p w → j = i) ∧
      (∀ q : Site, ∃ j : Cut, run j = .receive q w) ∧
      (∃ j : Cut, (run j).output = some (p, w))
  | _ => True

private instance (i : Cut) (s : S) : Decidable (Row i s) := by
  cases s <;> unfold Row <;> infer_instance

private theorem rows (i : Cut) : Row i (run i) := by revert i; decide

private theorem at_send {t : ℕ} {p : Site} {w : Wire}
    (h : (run t).transport = some (.broadcast p w)) : run t = .send w ∧ p = w.1.sender := by
  cases e : run t <;> simp_all [Step.transport]; grind

private theorem at_recv {t : ℕ} {p : Site} {w : Wire}
    (h : (run t).transport = some (.deliver p w)) : run t = .receive p w := by
  cases e : run t <;> simp_all [Step.transport]

private theorem in_script {t : ℕ} {s : S} (h : run t = s) (hne : s ≠ .idle) :
    t < script.length := by
  by_contra! ht
  exact hne (h.symm.trans (idle ht))

private theorem receiver_row {t : ℕ} {p : Site} {w : Wire} (h : run t = .receive p w) :
    Row ⟨t, in_script h (by simp)⟩ (.receive p w) := by
  have ht := rows ⟨t, in_script h (by simp)⟩
  simpa only [h] using ht

private theorem transport : Transport run := by
  constructor
  · intro p _ w t h
    obtain ⟨hs, rfl⟩ := at_send h
    have ht := rows ⟨t, in_script hs (by simp)⟩
    rw [show run (⟨t, _⟩ : Cut) = .send w from hs] at ht
    obtain ⟨j, hj, he⟩ := ht
    exact ⟨j, hj, by rw [he]; rfl⟩
  · intro p _ w t h q _
    obtain ⟨j, hj⟩ := (receiver_row (at_recv h)).2.2.1 q
    exact ⟨j, by rw [hj]; rfl⟩
  · intro p w t h
    have tab := receiver_row (at_recv h)
    obtain ⟨j, hj, hs⟩ := tab.1
    refine ⟨?_, j, hj, by rw [hs]; rfl⟩
    intro u hu
    have hr := at_recv hu
    exact congrArg Fin.val (tab.2.1 ⟨u, in_script hr (by simp)⟩ hr)

private theorem fair : FairInspection run := by
  intro p _ w t h
  have hp := h (max t script.length) (le_max_left ..)
  obtain ⟨i, -, hr⟩ := hp.2.1
  obtain ⟨j, hj⟩ := (receiver_row hr).2.2.2
  exact (hp.2.2 j (lt_of_lt_of_le j.isLt (le_max_right ..)) hj).elim

-- A client of the main theorem with all hypotheses discharged on an infinite nonempty run.
example : IsReliableBroadcast Diffusion.Message.sender (correct run) (application run) :=
  (vectorTimestamp_causalBroadcast legal transport fair).1

-- Same data do not identify sends, even within the stream from B.
example : y.1.payload = z.1.payload ∧ y.1.sender = z.1.sender ∧ y.1 ≠ z.1 := by decide

-- Prompt source delivery is visible *before* the later transport echo. Echo emits nothing.
example : application run 0 = some (.broadcast 0 x.1) ∧
    application run 1 = some (.deliver 0 x.1) ∧ run 17 = .receive 0 x ∧
    (run 17).output = none ∧ clock run 0 0 17 = clock run 0 0 18 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- At C, z is pending, not delivered; the sender component alone is insufficient at cut 9.
example : Pending run 2 z 6 ∧ ¬ Fits run 2 z 6 ∧ (run 6).output = none ∧
    clock run 2 1 9 = z.2 1 ∧ ¬ Fits run 2 z 9 ∧ (run 9).output = none ∧
    Fits run 2 z 12 ∧ (run 12).output = some (2, z) ∧ ¬ Pending run 2 z 13 := by
  unfold Pending Fits; decide

-- A and B see their own message first and the other's second.
example : (run 0).output = some (0, x) ∧ (run 14).output = some (0, y) ∧
    (run 1).output = some (1, y) ∧ (run 3).output = some (1, x) := by decide

-- Generation of real direct edges from a receiver's delivery and a sender's prior broadcast.
example : Precedes run x.1 z.1 ∧ Precedes run y.1 z.1 :=
  ⟨.single ⟨7, 8, by decide, rfl, .inr rfl⟩, .single ⟨2, 8, by decide, rfl, .inl rfl⟩⟩

private theorem all_correct (p : Site) : p ∈ correct run := by
  have table : ∀ i : Cut, ∀ q : Site, run i ≠ .crash q := by decide
  intro t h
  exact table ⟨t, in_script h (by simp)⟩ p h

-- The complete run has three correct processes; liveness actually applies to z at C.
example : ∃ n > 8, application run n = some (.deliver 2 z.1) :=
  correct_broadcast_terminates legal transport fair (all_correct 1) rfl (all_correct 2)

-- The two observed orders do not hide an application-causal edge in either direction.
example : ¬ Precedes run x.1 y.1 ∧ ¬ Precedes run y.1 x.1 := by
  constructor
  · intro h
    obtain ⟨u, hu, he⟩ := causal_delivery legal transport h
      (show application run 3 = some (.deliver 1 y.1) from rfl)
    rcases u with _ | (_ | (_ | u)) <;> first | omega | cases he
  · intro h
    obtain ⟨u, hu, he⟩ := causal_delivery legal transport h
      (show application run 1 = some (.deliver 0 x.1) from rfl)
    obtain rfl : u = 0 := by omega
    cases he

-- A faulty sender can self-deliver and stop without *any* correct transport receipt. This
-- legal run deliberately would not implement uniform agreement at the application layer.
private def halted : Trace Site Unit
  | 0 => .send x
  | 1 => .crash 0
  | _ + 2 => .idle

private theorem stopped : (0 : Site) ∉ correct halted := fun h => h 1 rfl

private theorem no_receipt (p : Site) (w : Wire) (t : ℕ) : halted t ≠ .receive p w := by
  rcases t with _ | (_ | t) <;> simp [halted]

private theorem haltLegal : Legal halted := by
  intro t
  rcases t with _ | (_ | t)
  · exact ⟨by simp, rfl, rfl⟩
  · refine ⟨?_, trivial⟩
    intro p _ i hi
    obtain rfl : i = 0 := by omega
    simp [halted]
  · simp [halted, Admissible, Step.actor]

private theorem haltTransport : Transport halted := by
  constructor
  · intro p hp w t h
    rcases t with _ | (_ | t) <;> simp [halted, Step.transport] at h
    obtain ⟨rfl, -⟩ := h
    exact (stopped hp).elim
  · intro p _ w t h
    rcases t with _ | (_ | t) <;> simp [halted, Step.transport] at h
  · intro p w t h
    rcases t with _ | (_ | t) <;> simp [halted, Step.transport] at h

private theorem haltFair : FairInspection halted := by
  intro p _ w t h
  obtain ⟨j, -, hr⟩ := (h t le_rfl).2.1
  exact (no_receipt p w j hr).elim

example : Transport halted ∧ Legal halted ∧ FairInspection halted ∧ (1 : Site) ∈ correct halted ∧
    application halted 1 = some (.deliver 0 x.1) ∧ ∀ t, (halted t).output ≠ some (1, x) := by
  refine ⟨haltTransport, haltLegal, haltFair, ?_, rfl, ?_⟩
  · intro t; rcases t with _ | (_ | t) <;> dsimp only [halted] <;> decide
  · intro t; rcases t with _ | (_ | t) <;> dsimp only [halted, Step.output] <;> decide

end Cslib.Distributed.VectorTimestampBroadcast.Tests
