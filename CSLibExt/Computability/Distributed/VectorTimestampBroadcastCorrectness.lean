/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.VectorTimestampBroadcast

/-!
# Correctness of causal broadcast with vector timestamps

Each receiver extends a prefix of each sender's stream. This is a consequence of checking the
pre-increment tag and removing the delivered packet, not a constraint on the order of receipts.
The prefix invariant transfers the sender's earlier application observations to each receiver.
For agreement, the induction runs over the delivery history of a *correct witness*: its receipts
(and validity for its own sends) justify each use of ordinary transport agreement. No delivery
at a faulty process alone forces a delivery elsewhere.

See A. Bieniusa, *Programming Distributed Systems: Fault-tolerance in Message-Passing Distributed
Systems*, 2020, slides 41 and 47, for the specification and vector algorithm respectively.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.VectorTimestampBroadcast

open ReliableBroadcast

variable {P D : Type*} {a : Trace P D} {p r : P} {w v : Packet P D} {i j t : ℕ}

private theorem out_cases {s : Step P D} (h : s.output = some (p, w)) :
    (s = .send w ∧ p = w.1.sender) ∨ s = .inspect p w true := by
  cases s with
  | inspect q z b => cases b <;> simp_all [Step.output]
  | send z => simp [Step.output] at h; grind
  | _ => simp [Step.output] at h

private theorem tr_send {s : Step P D} : s.transport = some (.broadcast p w) ↔
    s = .send w ∧ p = w.1.sender := by cases s <;> simp [Step.transport]; grind

private theorem tr_recv {s : Step P D} : s.transport = some (.deliver p w) ↔
    s = .receive p w := by cases s <;> simp [Step.transport]

private theorem recv_origin (R : Transport a) (h : a t = .receive p w) :
    ∃ i < t, a i = .send w := by
  obtain ⟨i, hi, hs⟩ := (R.uniformIntegrity p w t (tr_recv.mpr h)).2
  exact ⟨i, hi, (tr_send.mp hs).1⟩

variable [DecidableEq P]

/-- In a legal wrapper trace, each send uses the sender's current self-count as its serial
and its entire current vector as its tag, before prompt local delivery increments that count.
Neither reliable transport nor fair inspection is needed. -/
theorem stamp (L : Legal a) (h : a i = .send w) :
    w.1.seq = clock a w.1.sender w.1.sender i ∧ w.2 = fun r => clock a w.1.sender r i := by
  have hl := (L i).2
  rwa [h] at hl

private theorem check (L : Legal a) {b : Bool} (h : a i = .inspect p w b) :
    b = true ↔ Pending a p w i ∧ Fits a p w i := by
  have hl := (L i).2
  rwa [h] at hl

private theorem out_origin (L : Legal a) (R : Transport a) (h : (a t).output = some (p, w)) :
    ∃ i ≤ t, a i = .send w := by
  rcases out_cases h with ⟨hs, -⟩ | hd
  · exact ⟨t, le_rfl, hs⟩
  · obtain ⟨j, hj, hr⟩ := ((check L hd).mp rfl).1.2.1
    obtain ⟨i, hi, hs⟩ := recv_origin R hr
    exact ⟨i, by omega, hs⟩

private theorem monoClock (p r : P) : Monotone (clock a p r) := by
  apply monotone_nat_of_le_succ
  intro n
  simp [clock]

private theorem bump (h : (a i).output = some (p, w)) :
    clock a p w.1.sender (i + 1) = clock a p w.1.sender i + 1 := by
  simp [clock, Step.component, h]

private theorem strictClock (h : (a i).output = some (p, w)) (hij : i < j) :
    clock a p w.1.sender i < clock a p w.1.sender j := by
  have hm := monoClock (a := a) p w.1.sender (show i + 1 ≤ j by omega)
  rw [bump h] at hm
  omega

private theorem send_lt (L : Legal a) (hs : a i = .send w) (hs' : a j = .send v)
    (hp : w.1.sender = v.1.sender) (hij : i < j) : w.1.seq < v.1.seq := by
  have ho : (a i).output = some (w.1.sender, w) := by rw [hs]; rfl
  rw [(stamp L hs).1, (stamp L hs').1, ← hp]
  exact strictClock ho hij

/-- In a legal wrapper trace, two sends with the same sender and serial occur at the same
step and carry the same message and tag, even if other sends have identical payloads.
This uniqueness follows from the local rules alone. -/
theorem send_unique (L : Legal a) (hs : a i = .send w) (hs' : a j = .send v)
    (hp : w.1.sender = v.1.sender) (hk : w.1.seq = v.1.seq) : i = j ∧ w = v := by
  have he : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have := send_lt L hs hs' hp h; omega
    · exact h
    · have := send_lt L hs' hs hp.symm h; omega
  subst j
  exact ⟨rfl, Step.send.inj (hs.symm.trans hs')⟩

private theorem packet_unique (L : Legal a) (R : Transport a) {q : P}
    (h : (a i).output = some (p, w)) (h' : (a j).output = some (q, v))
    (hp : w.1.sender = v.1.sender) (hk : w.1.seq = v.1.seq) : w = v := by
  obtain ⟨_, _, hs⟩ := out_origin L R h
  obtain ⟨_, _, hs'⟩ := out_origin L R h'
  exact (send_unique L hs hs' hp hk).2

private theorem not_repeat (L : Legal a) (R : Transport a) (hi : (a i).output = some (p, w))
    (hj : (a j).output = some (p, w)) (hij : i < j) : False := by
  rcases out_cases hj with ⟨hs, -⟩ | hd
  · obtain ⟨u, hu, hs'⟩ := out_origin L R hi
    have := (send_unique L hs hs' rfl rfl).1
    omega
  · exact ((check L hd).mp rfl).1.2.2 i hij hi

private theorem fits_output (L : Legal a) (h : (a t).output = some (p, w)) : Fits a p w t := by
  rcases out_cases h with ⟨hs, rfl⟩ | hd
  · intro r; rw [(stamp L hs).2]
  · exact ((check L hd).mp rfl).2

private theorem serial_le (L : Legal a) (R : Transport a) (h : (a t).output = some (p, w)) :
    w.1.seq ≤ clock a p w.1.sender t := by
  obtain ⟨i, -, hs⟩ := out_origin L R h
  have hf := fits_output L h w.1.sender
  simpa only [(stamp L hs).1, (stamp L hs).2] using hf

private theorem next_serial (L : Legal a) (R : Transport a)
    (hprefix : ∀ k < clock a p w.1.sender t,
      ∃ i < t, ∃ v, (a i).output = some (p, v) ∧ v.1.sender = w.1.sender ∧ v.1.seq = k)
    (h : (a t).output = some (p, w)) : w.1.seq = clock a p w.1.sender t := by
  apply le_antisymm (serial_le L R h)
  by_contra! hlt
  obtain ⟨i, hi, v, hv, hp, hk⟩ := hprefix _ hlt
  obtain rfl := packet_unique L R hv h hp hk
  exact not_repeat L R hv h hi

/-- In a legal wrapper trace whose stamped send/receive projection satisfies reliable broadcast
(`Transport`), every zero-based serial below a receiver's count for a given sender has already
been application-delivered there. This prefix property needs no fair inspection and holds even
at a receiver that later crashes. -/
theorem sender_prefix (L : Legal a) (R : Transport a) (t : ℕ) (p r : P) :
    ∀ k < clock a p r t,
      ∃ i < t, ∃ w, (a i).output = some (p, w) ∧ w.1.sender = r ∧ w.1.seq = k := by
  induction t with
  | zero => simp [clock]
  | succ t ih =>
    intro k hk
    by_cases hlt : k < clock a p r t
    · obtain ⟨i, hi, hv⟩ := ih k hlt
      exact ⟨i, by omega, hv⟩
    · simp only [clock] at hk
      split at hk <;> rename_i hc
      · obtain ⟨⟨q, w⟩, ho, hp⟩ := Option.map_eq_some_iff.mp hc
        change (q, w.1.sender) = (p, r) at hp
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        have he := next_serial L R ih ho
        exact ⟨t, by omega, w, ho, rfl, by omega⟩
      · omega

/-- In a legal wrapper trace with reliable broadcast on stamped packets (`Transport`), a
receiver's count for the sender immediately before an application delivery equals the message's
zero-based serial. The one-based `k`-th message thus follows exactly `k-1` deliveries from its
sender. This holds without fair inspection, even at a receiver that later crashes. -/
theorem delivery_serial (L : Legal a) (R : Transport a) (h : (a t).output = some (p, w)) :
    w.1.seq = clock a p w.1.sender t := next_serial L R (sender_prefix L R t p _) h

omit [DecidableEq P] in
private theorem app_send {n : ℕ} {m : Message P D} : application a n = some (.broadcast p m) ↔
    ∃ i w, n = 2 * i ∧ a i = .send w ∧ p = w.1.sender ∧ m = w.1 := by
  constructor
  · intro h
    unfold application at h
    split at h <;> rename_i hn
    · cases hs : a (n / 2) with
      | send w =>
        simp only [hs, Step.input, Option.some.injEq, Event.broadcast.injEq] at h
        exact ⟨_, w, by omega, hs, h.1.symm, h.2.symm⟩
      | _ => simp [hs, Step.input] at h
    · obtain ⟨⟨_, _⟩, -, he⟩ := Option.map_eq_some_iff.mp h
      contradiction
  · rintro ⟨i, w, rfl, hs, rfl, rfl⟩
    simp [application, hs, Step.input]

omit [DecidableEq P] in
private theorem app_out {n : ℕ} {m : Message P D} : application a n = some (.deliver p m) ↔
    ∃ i w, n = 2 * i + 1 ∧ (a i).output = some (p, w) ∧ m = w.1 := by
  constructor
  · intro h
    unfold application at h
    split at h <;> rename_i hn
    · cases hs : a (n / 2) <;> simp [hs, Step.input] at h
    · obtain ⟨⟨q, w⟩, ho, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := Event.deliver.inj he
      exact ⟨_, w, by omega, ho, rfl⟩
  · rintro ⟨i, w, rfl, ho, rfl⟩
    have : (2 * i + 1) / 2 = i := by omega
    simp [application, this, ho]

private theorem direct_order (L : Legal a) (R : Transport a) {x y : Message P D}
    (hxy : ObservedBefore a x y) (hy : application a t = some (.deliver p y)) :
    ∃ u < t, application a u = some (.deliver p x) := by
  obtain ⟨d, v, rfl, hd, rfl⟩ := app_out.mp hy
  obtain ⟨u, n, hun, hb, hx⟩ := hxy
  obtain ⟨j, z, rfl, hs, he, hm⟩ := app_send.mp hb
  obtain ⟨j', -, hs'⟩ := out_origin L R hd
  obtain ⟨-, rfl⟩ := send_unique L hs' hs he (congrArg Diffusion.Message.seq hm)
  obtain ⟨i, w, hij, ho, rfl⟩ : ∃ i w, i < j ∧ (a i).output = some (v.1.sender, w) ∧ x = w.1 := by
    rcases hx with h | h
    · obtain ⟨i, w, rfl, hi, hp, rfl⟩ := app_send.mp h
      exact ⟨i, w, by omega, by rw [hi, hp]; rfl, rfl⟩
    · obtain ⟨i, w, rfl, hi, rfl⟩ := app_out.mp h
      exact ⟨i, w, by omega, hi, rfl⟩
  have hlt := strictClock ho hij
  have hf := fits_output L hd w.1.sender
  rw [(stamp L hs).2] at hf
  have hk : w.1.seq < clock a p w.1.sender d :=
    (delivery_serial L R ho) ▸ lt_of_lt_of_le hlt hf
  obtain ⟨k, hkd, w', hout, hsender, hseq⟩ := sender_prefix L R d p _ _ hk
  obtain rfl := packet_unique L R hout ho hsender hseq
  exact ⟨_, by omega, app_out.mpr ⟨k, w', rfl, hout, rfl⟩⟩

/-- In a legal wrapper trace with reliable broadcast on stamped packets (`Transport`), if a
process application-delivers a message, then it has already application-delivered every causal
predecessor. This holds even if the process later crashes; no inspection fairness is needed.
Causality is the transitive closure of earlier application broadcasts or deliveries at the sender
of the subsequent message. -/
theorem causal_delivery (L : Legal a) (R : Transport a) {x y : Message P D}
    (h : Precedes a x y) (hy : application a t = some (.deliver p y)) :
    ∃ u < t, application a u = some (.deliver p x) := by
  induction h generalizing t with
  | single h => exact direct_order L R h hy
  | tail _ h ih =>
    obtain ⟨j, hj, he⟩ := direct_order L R h hy
    obtain ⟨i, hi, ho⟩ := ih he
    exact ⟨i, hi.trans hj, ho⟩

/-- In a legal wrapper trace (`Legal`) with fair inspection of persistently pending packets at
correct processes (`FairInspection`), suppose a correct receiver gets a packet from another
process and its counts dominate the packet's tag at some cut (`Fits`). Then the receiver
application-delivers the packet at some step, possibly before that cut. Fairness schedules an
inspection if the packet stays pending; legality makes the inspection succeed when the packet
is pending and fits. The receipt is a hypothesis; transport reliability is not required. -/
theorem eventually_drain (L : Legal a) (F : FairInspection a) (hp : p ∈ correct a)
    (hne : p ≠ w.1.sender) (hr : a i = .receive p w) (hf : Fits a p w t) :
    ∃ j, (a j).output = some (p, w) := by
  by_contra! h
  have hpend (u : ℕ) (hu : max (i + 1) t ≤ u) : Pending a p w u :=
    ⟨hne, ⟨i, by omega, hr⟩, fun j _ => h j⟩
  obtain ⟨u, hu, b, hb⟩ := F p hp w _ hpend
  have he := (check L hb).mpr ⟨hpend u hu, fun r =>
    (hf r).trans (monoClock p r (by omega : t ≤ u))⟩
  subst b
  exact h u (by rw [hb]; rfl)

/-- A pending packet whose guard holds now at a correct receiver is actually delivered at or
after this cut. This uses only the inspection semantics and scheduling fairness. -/
theorem enabled_pending_drains (L : Legal a) (F : FairInspection a) (hp : p ∈ correct a)
    (hw : Pending a p w t) (hf : Fits a p w t) :
    ∃ j ≥ t, (a j).output = some (p, w) := by
  obtain ⟨i, -, hr⟩ := hw.2.1
  obtain ⟨j, hj⟩ := eventually_drain L F hp hw.1 hr hf
  exact ⟨j, le_of_not_gt (fun h => hw.2.2 j h hj), hj⟩

omit [DecidableEq P] in
private theorem receive_everywhere (R : Transport a) (hp : p ∈ correct a) {q : P}
    (hq : q ∈ correct a) (h : a t = .receive p w) : ∃ j, a j = .receive q w := by
  obtain ⟨j, hj⟩ := R.agreement p hp w t (tr_recv.mpr h) q hq
  exact ⟨j, tr_recv.mp hj⟩

private theorem transfer (L : Legal a) (R : Transport a) (F : FairInspection a)
    (hp : p ∈ correct a) {q : P} (hq : q ∈ correct a) (h : (a t).output = some (p, w))
    (hf : Fits a q w i) : ∃ j, (a j).output = some (q, w) := by
  by_cases he : q = w.1.sender
  · obtain ⟨j, -, hj⟩ := out_origin L R h
    exact ⟨j, by rw [hj, he]; rfl⟩
  obtain ⟨j, hr⟩ : ∃ j, a j = .receive p w := by
    rcases out_cases h with ⟨hs, rfl⟩ | hd
    · obtain ⟨j, -, hj⟩ := R.validity _ hp w t (tr_send.mpr ⟨hs, rfl⟩)
      exact ⟨j, tr_recv.mp hj⟩
    · obtain ⟨j, -, hj⟩ := ((check L hd).mp rfl).1.2.1
      exact ⟨j, hj⟩
  obtain ⟨k, hk⟩ := receive_everywhere R hp hq hr
  exact eventually_drain L F hq he hk hf

private theorem catch_up (L : Legal a) (R : Transport a) (F : FairInspection a)
    (hp : p ∈ correct a) {q : P} (hq : q ∈ correct a) (t : ℕ) :
    ∃ T, ∀ r, clock a p r t ≤ clock a q r T := by
  induction t with
  | zero => exact ⟨0, fun _ => le_rfl⟩
  | succ t ih =>
    obtain ⟨T, hT⟩ := ih
    cases ho : (a t).output with
    | none => exact ⟨T, fun r => by simpa [clock, Step.component, ho] using hT r⟩
    | some pair =>
      obtain ⟨s, w⟩ := pair
      by_cases hs : s = p
      · subst s
        obtain ⟨j, hj⟩ := transfer L R F hp hq ho (fun r => (fits_output L ho r).trans (hT r))
        refine ⟨max T (j + 1), fun r => ?_⟩
        by_cases he : r = w.1.sender
        · subst r
          rw [bump ho, ← delivery_serial L R ho, delivery_serial L R hj, ← bump hj]
          exact monoClock q _ (le_max_right ..)
        · have hr := (hT r).trans (monoClock (a := a) q r (le_max_left T (j + 1)))
          simpa [clock, Step.component, ho, Ne.symm he] using hr
      · exact ⟨T, fun r => by simpa [clock, Step.component, ho, hs] using hT r⟩

/-- The wrapper's application projection satisfies the canonical reliable-broadcast interface:
validity, agreement from a delivery at a correct process, and strict no-creation and no-duplicate
at every process. The assumptions are the local transition semantics, the same interface on the
*transport* projection, and fair local inspection at correct processes. -/
theorem application_isReliableBroadcast (L : Legal a) (R : Transport a) (F : FairInspection a) :
    IsReliableBroadcast Diffusion.Message.sender (correct a) (application a) := by
  constructor
  · intro p _ m t h
    obtain ⟨i, w, rfl, hs, rfl, rfl⟩ := app_send.mp h
    exact ⟨_, Nat.le_succ _, app_out.mpr ⟨i, w, rfl, by rw [hs]; rfl, rfl⟩⟩
  · intro p hp m t h q hq
    obtain ⟨i, w, -, ho, rfl⟩ := app_out.mp h
    obtain ⟨T, hT⟩ := catch_up L R F hp hq i
    obtain ⟨j, hj⟩ := transfer L R F hp hq ho (fun r => (fits_output L ho r).trans (hT r))
    exact ⟨_, app_out.mpr ⟨j, w, rfl, hj, rfl⟩⟩
  · intro p m t h
    obtain ⟨i, w, rfl, ho, rfl⟩ := app_out.mp h
    obtain ⟨k, hki, hs⟩ := out_origin L R ho
    refine ⟨?_, 2 * k, by omega, app_send.mpr ⟨k, w, rfl, hs, rfl, rfl⟩⟩
    intro t' h'
    obtain ⟨j, v, rfl, hv, hm⟩ := app_out.mp h'
    obtain rfl := packet_unique L R ho hv (congrArg Diffusion.Message.sender hm)
      (congrArg Diffusion.Message.seq hm)
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (not_repeat L R ho hv hij).elim
    · rfl
    · exact (not_repeat L R hv ho hji).elim

/-- In a legal wrapper trace whose stamped send/receive projection satisfies reliable broadcast
(`Transport`), assume fair inspections of persistently pending packets at correct processes.
Then each application broadcast by a correct sender is followed strictly later by an application
delivery of that message at every correct process, including the sender. -/
theorem correct_broadcast_terminates (L : Legal a) (R : Transport a) (F : FairInspection a)
    (hp : p ∈ correct a) {m : Message P D} (hs : application a t = some (.broadcast p m))
    {q : P} (hq : q ∈ correct a) : ∃ j > t, application a j = some (.deliver q m) := by
  have rb := application_isReliableBroadcast L R F
  obtain ⟨i, -, hi⟩ := rb.validity p hp m t hs
  obtain ⟨j, hj⟩ := rb.agreement p hp m i hi q hq
  obtain ⟨k, hkj, hk⟩ := (rb.uniformIntegrity q m j hj).2
  obtain ⟨u, w, rfl, hu, -, rfl⟩ := app_send.mp hs
  obtain ⟨v, z, rfl, hv, hpz, hm⟩ := app_send.mp hk
  obtain ⟨rfl, -⟩ := send_unique L hu hv hpz (congrArg Diffusion.Message.seq hm)
  exact ⟨j, hkj, hj⟩

/-- **Vector timestamps implement reliable causal broadcast.** For every legal wrapper trace
with canonical reliable transport on stamped packets and fair inspections at correct processes,
the serialized application events satisfy reliable broadcast on the original message identities.
Moreover every delivery (also before a crash) follows all its causal predecessors, where
causality closes actual earlier application broadcasts and deliveries at the sender under
transitivity. This is an event-trace result; it imposes no ordering on concurrent sends. -/
theorem vectorTimestamp_causalBroadcast (L : Legal a) (R : Transport a) (F : FairInspection a) :
    IsReliableBroadcast Diffusion.Message.sender (correct a) (application a) ∧
      ∀ {p x y t}, Precedes a x y → application a t = some (.deliver p y) →
        ∃ u < t, application a u = some (.deliver p x) :=
  ⟨application_isReliableBroadcast L R F, fun h hy => causal_delivery L R h hy⟩

end Cslib.Distributed.VectorTimestampBroadcast
