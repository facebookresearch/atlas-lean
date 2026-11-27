/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

/-!
# Signed-message Byzantine agreement

We model one instance of Lamport, Shostak and Pease's `SM(m)` by a finite, completed history
of abstract sends and receipts. The generals are `Option L`: `none` is the commander and
`some i` is lieutenant `i`. Only messages to lieutenants are relevant. A message records its
immediate sender separately from its nested chain of signatures. The commander's signature
is implicit at the root; the list records the lieutenant signatures from innermost to outermost.

In `History.FollowsSM`, delivery is correct and the immediate sender is known (A1–A2).
Send and receipt obligations match by content, not by a unique transmission identifier;
identical copies have no effect after the first acceptance. Completion models the end of
reception in step (3) (A3); this is not a construction of a termination detector. The
verification bit abstracts public verification (A4): every verified
receipt containing a loyal signature has a prior send of its exact signed prefix by that loyal
general. Faulty signatures need not originate with their claimed signers. There is no signature
algorithm here. Rejected messages have no effect on the local sets of orders.

A verified bare order must come directly from the commander and is accepted only with an empty
local set; this first acceptance forwards even when `m = 0`. A newly accepted nonempty chain
is forwarded only when it has fewer than `m` lieutenant signatures. A lieutenant sends the
extended chain only to other lieutenants not in the incoming chain. The cutoff controls sending,
not acceptance. At or above it, the chain including the commander contains more signers than
there are traitors. The proof traces a loyal signature to its genuine shorter prefix to recover
the corresponding forwarding obligation (or uses the loyal commander's original broadcast).

## Reference

L. Lamport, R. Shostak and M. Pease, *The Byzantine Generals Problem*, ACM TOPLAS 4(3),
382–401 (1982), §4, Algorithm SM(m) and Theorem 2.
-/

@[expose] public section

namespace Cslib.Distributed.Byzantine.SignedMessages

/-- An abstract signed order message. `verified` says that the entire nested signature chain
passes verification, not that every claimed signer is loyal or personally signed it. -/
structure Message (L V : Type*) where
  /-- The immediate sender; `none` denotes the commander. -/
  sender : Option L
  /-- The receiving lieutenant. -/
  recipient : L
  /-- The order at the root of the signed message. -/
  order : V
  /-- The lieutenant signatures in order, not including the commander's implicit signature. -/
  chain : List L
  /-- The result of ideal public verification of the entire chain. -/
  verified : Bool
  deriving DecidableEq

namespace Message

variable {L V : Type*}

/-- The commander's initial message to lieutenant `i`. -/
def initial (v : V) (i : L) : Message L V := ⟨none, i, v, [], true⟩

/-- The result of appending the receiving lieutenant's signature and addressing the result to
lieutenant `j`. The algorithm uses this only on a verified message. -/
def relay (d : Message L V) (j : L) : Message L V :=
  ⟨some d.recipient, j, d.order, d.chain ++ [d.recipient], true⟩

/-- A proper receipt requires verification, distinct lieutenant signers, and exclusion of the
recipient from the chain. If the chain is empty, the order must also come directly from the
commander (step (2)(A)). -/
def Proper (d : Message L V) : Prop :=
  d.verified = true ∧ d.chain.Nodup ∧ d.recipient ∉ d.chain ∧ (d.chain = [] → d.sender = none)

instance [DecidableEq L] (d : Message L V) : Decidable d.Proper := by
  unfold Proper
  infer_instance

/-- Step (2)(A) forwards a newly accepted bare order unconditionally; step (2)(B) forwards
an extended chain only below the cutoff. -/
def MayForward (m : ℕ) (d : Message L V) : Prop :=
  d.chain = [] ∨ d.chain.length < m

instance [DecidableEq L] (m : ℕ) (d : Message L V) : Decidable (d.MayForward m) := by
  unfold MayForward
  infer_instance

/-- Eligible forwarding targets exclude the signer of the new message and the earlier
lieutenant signers. -/
def RelayTarget (d : Message L V) (j : L) : Prop := j ≠ d.recipient ∧ j ∉ d.chain

instance [DecidableEq L] (d : Message L V) (j : L) : Decidable (d.RelayTarget j) := by
  unfold RelayTarget
  infer_instance

private theorem proper_initial (v : V) (i : L) : (initial v i).Proper := by
  simp [Proper, initial]

private theorem proper_relay {d : Message L V} (hd : d.Proper) {j : L}
    (hj : d.RelayTarget j) : (d.relay j).Proper := by
  have hdistinct : ∀ a ∈ d.chain, a ≠ d.recipient :=
    fun _ ha he => hd.2.2.1 (he ▸ ha)
  simpa [Proper, relay, List.nodup_append, hd.2.1, hj.1, hj.2] using hdistinct

end Message

/-- The two kinds of events in a signed-message history. -/
inductive Phase
  | send
  | receive
  deriving DecidableEq

/-- A send or receipt of an abstract signed order message. -/
structure Event (L V : Type*) where
  /-- Whether this is a send or a receipt. -/
  phase : Phase
  /-- The same message, including the immediate sender, is recorded at transmission and receipt. -/
  message : Message L V

namespace Event

variable {L V : Type*} [DecidableEq L] [DecidableEq V]

/-- A receipt adds a new value if it is properly signed and, in the bare-order case, the
recipient's previous set is empty. Messages for values already present do not add or forward
anything. -/
def Accepts (e : Event L V) (known : Finset V) : Prop :=
  e.phase = .receive ∧ e.message.Proper ∧
    (e.message.chain = [] → known = ∅) ∧ e.message.order ∉ known

instance (e : Event L V) (known : Finset V) : Decidable (e.Accepts known) := by
  unfold Accepts
  infer_instance

end Event

/-- A finite chronological sequence of sends and receipts. Earlier events have smaller indices. -/
abbrev History (L V : Type*) := List (Event L V)

namespace History

variable {L V : Type*} [DecidableEq L] [DecidableEq V]

/-- The orders known to lieutenant `i` after processing the first `t` events, starting from
an empty set. Insertion into the empty set in step (2)(A) gives exactly the required singleton. -/
def ordersBefore (h : History L V) (i : L) : ℕ → Finset V
  | 0 => ∅
  | t + 1 =>
    let known := h.ordersBefore i t
    match h[t]? with
    | some e => if e.message.recipient = i ∧ e.Accepts known then insert e.message.order known
        else known
    | none => known

/-- Lieutenant `i`'s final set of accepted orders. -/
def orders (h : History L V) (i : L) : Finset V := h.ordersBefore i h.length

/-- The event at `r` is a receipt at which its recipient adds a new order. -/
def Learns (h : History L V) (r : Fin h.length) : Prop :=
  (h.get r).Accepts (h.ordersBefore (h.get r).message.recipient r)

instance (h : History L V) (r : Fin h.length) : Decidable (h.Learns r) := by
  unfold Learns
  infer_instance

/-- The local rules and communication assumptions for a completed history of `SM(m)`.
The set `faulty` includes the commander precisely when it contains `none`. The rules restrict
what a loyal general sends, require all its prescribed sends and their delivery, and require
prior provenance only for signatures of loyal generals. They do not constrain what a faulty
sender can send beyond these communication and ideal authentication assumptions. -/
structure FollowsSM (h : History L V) (m : ℕ) (faulty : Finset (Option L)) (v : V) : Prop where
  /-- Every send has a later receipt of the same message. -/
  delivered : ∀ s : Fin h.length, (h.get s).phase = .send →
    ∃ r : Fin h.length, s < r ∧ (h.get r).phase = .receive ∧ (h.get r).message = (h.get s).message
  /-- Every receipt comes from an earlier send with the same immediate sender and content. -/
  sent : ∀ r : Fin h.length, (h.get r).phase = .receive →
    ∃ s : Fin h.length, s < r ∧ (h.get s).phase = .send ∧ (h.get s).message = (h.get r).message
  /-- A loyal commander sends its signed initial order to every lieutenant. -/
  issue : none ∉ faulty → ∀ i : L,
    ∃ s : Fin h.length, (h.get s).phase = .send ∧ (h.get s).message = Message.initial v i
  /-- Each required forwarding of a newly accepted order occurs. -/
  forward : ∀ r : Fin h.length, h.Learns r → some (h.get r).message.recipient ∉ faulty →
    (h.get r).message.MayForward m → ∀ j : L, (h.get r).message.RelayTarget j →
    ∃ s : Fin h.length, r < s ∧ (h.get s).phase = .send ∧
      (h.get s).message = (h.get r).message.relay j
  /-- A loyal commander's only sends are initial orders. A loyal lieutenant sends only the
  exact extension prescribed by a prior first acceptance and only to a permitted recipient. -/
  loyalSend : ∀ s : Fin h.length, (h.get s).phase = .send → (h.get s).message.sender ∉ faulty →
    (h.get s).message = Message.initial v (h.get s).message.recipient ∨
      ∃ r : Fin h.length, r < s ∧ h.Learns r ∧ (h.get r).message.MayForward m ∧
        (h.get r).message.RelayTarget (h.get s).message.recipient ∧
        (h.get s).message = (h.get r).message.relay (h.get s).message.recipient
  /-- The loyal commander's verified signature comes from a prior send of the bare order. -/
  commanderSignature : ∀ r : Fin h.length, (h.get r).phase = .receive →
    (h.get r).message.verified = true → none ∉ faulty →
    ∃ s : Fin h.length, s < r ∧ (h.get s).phase = .send ∧ (h.get s).message.sender = none ∧
      (h.get s).message.order = (h.get r).message.order ∧ (h.get s).message.chain = []
  /-- A loyal lieutenant's verified signature comes from a prior send of the exact prefix
  ending with that signature, for the same order. No such witness is required for a traitor. -/
  lieutenantSignature : ∀ r : Fin h.length, (h.get r).phase = .receive →
    (h.get r).message.verified = true → ∀ a : Fin (h.get r).message.chain.length,
    some ((h.get r).message.chain.get a) ∉ faulty →
    ∃ s : Fin h.length, s < r ∧ (h.get s).phase = .send ∧
      (h.get s).message.sender = some ((h.get r).message.chain.get a) ∧
      (h.get s).message.order = (h.get r).message.order ∧
      (h.get s).message.chain = (h.get r).message.chain.take (a + 1)

private theorem ordersBefore_succ (h : History L V) (i : L) (r : Fin h.length) :
    h.ordersBefore i (r + 1) =
      if (h.get r).message.recipient = i ∧ (h.get r).Accepts (h.ordersBefore i r) then
        insert (h.get r).message.order (h.ordersBefore i r) else h.ordersBefore i r := by
  simp [ordersBefore, List.get_eq_getElem]

private theorem mem_ordersBefore_iff (h : History L V) (i : L) (w : V) {t : ℕ}
    (ht : t ≤ h.length) : w ∈ h.ordersBefore i t ↔
      ∃ r : Fin h.length, (r : ℕ) < t ∧ h.Learns r ∧
        (h.get r).message.recipient = i ∧ (h.get r).message.order = w := by
  induction t with
  | zero => simp [ordersBefore]
  | succ t ih =>
    specialize ih (by omega)
    let r : Fin h.length := ⟨t, by omega⟩
    change w ∈ h.ordersBefore i ((r : ℕ) + 1) ↔ _
    rw [ordersBefore_succ]
    constructor
    · intro hw
      split at hw
      · rename_i he
        rcases Finset.mem_insert.mp hw with heq | hold
        · refine ⟨r, Nat.lt_succ_self _, ?_, he.1, heq.symm⟩
          simpa only [Learns, he.1] using he.2
        · obtain ⟨s, hs, hlearn, hi, horder⟩ := ih.mp hold
          exact ⟨s, Nat.lt_succ_of_lt hs, hlearn, hi, horder⟩
      · obtain ⟨s, hs, hlearn, hi, horder⟩ := ih.mp hw
        exact ⟨s, Nat.lt_succ_of_lt hs, hlearn, hi, horder⟩
    · rintro ⟨s, hs, hlearn, hi, horder⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with hlt | heq
      · have hold := ih.mpr ⟨s, hlt, hlearn, hi, horder⟩
        split
        · exact Finset.mem_insert_of_mem hold
        · exact hold
      · have hsr : s = r := Fin.ext heq
        subst s
        have he : (h.get r).message.recipient = i ∧ (h.get r).Accepts (h.ordersBefore i r) :=
          ⟨hi, by simpa only [Learns, hi] using hlearn⟩
        rw [ite_eq_left he, ← horder]
        exact Finset.mem_insert_self _ _

private theorem learns_mem_orders {h : History L V} {r : Fin h.length} (hr : h.Learns r) :
    (h.get r).message.order ∈ h.orders (h.get r).message.recipient :=
  (mem_ordersBefore_iff h _ _ le_rfl).mpr ⟨r, r.isLt, hr, rfl, rfl⟩

private theorem receive_mem_orders {h : History L V} {r : Fin h.length}
    (hr : (h.get r).phase = .receive) (hp : (h.get r).message.Proper)
    (he : (h.get r).message.chain = [] → h.ordersBefore (h.get r).message.recipient r = ∅) :
    (h.get r).message.order ∈ h.orders (h.get r).message.recipient := by
  by_cases hn : (h.get r).message.order ∈ h.ordersBefore (h.get r).message.recipient r
  · obtain ⟨s, hs, hl, hi, hv⟩ := (mem_ordersBefore_iff h _ _ r.isLt.le).mp hn
    exact (mem_ordersBefore_iff h _ _ le_rfl).mpr ⟨s, hs.trans r.isLt, hl, hi, hv⟩
  · exact learns_mem_orders (r := r) ⟨hr, hp, he, hn⟩

namespace FollowsSM

variable {h : History L V} {m : ℕ} {faulty : Finset (Option L)} {v : V}

private theorem order_eq_of_loyal_commander (H : h.FollowsSM m faulty v)
    (hc : none ∉ faulty) {r : Fin h.length} (hr : h.Learns r) : (h.get r).message.order = v := by
  obtain ⟨s, -, hs, hsender, horder, -⟩ := H.commanderSignature r hr.1 hr.2.1.1 hc
  rcases H.loyalSend s hs (hsender.symm ▸ hc) with he | ⟨t, -, -, -, -, he⟩
  · exact horder.symm.trans (congrArg Message.order he)
  · have he' : (h.get s).message.sender = some (h.get t).message.recipient :=
      congrArg Message.sender he
    rw [hsender] at he'
    cases he'

/-- In a completed history satisfying `FollowsSM` with a loyal commander, applying the faithful
acceptance rule to any lieutenant's receipts gives exactly the singleton containing the issued
order. -/
theorem orders_eq_singleton (H : h.FollowsSM m faulty v) (hc : none ∉ faulty)
    (i : L) : h.orders i = {v} := by
  have onlyIssued : h.orders i ⊆ {v} := by
    intro w hw
    obtain ⟨r, -, hr, -, he⟩ := (mem_ordersBefore_iff h i w le_rfl).mp hw
    exact Finset.mem_singleton.mpr (he.symm.trans (H.order_eq_of_loyal_commander hc hr))
  obtain ⟨s, hs, he⟩ := H.issue hc i
  obtain ⟨r, -, hr, he'⟩ := H.delivered s hs
  have hm := he'.trans he
  have hmem : v ∈ h.orders i := by
    by_cases hk : h.ordersBefore i r = ∅
    · have hpre : h.ordersBefore (h.get r).message.recipient r = ∅ := by
        rw [hm]
        exact hk
      have hp : (h.get r).message.Proper := hm.symm ▸ Message.proper_initial v i
      rw [← show (h.get r).message.recipient = i from congrArg Message.recipient hm,
        ← show (h.get r).message.order = v from congrArg Message.order hm]
      exact receive_mem_orders hr hp (fun _ => hpre)
    · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hk
      obtain ⟨t, ht, hl, hi, ho⟩ := (mem_ordersBefore_iff h i w r.isLt.le).mp hw
      have hw' : w ∈ h.orders i :=
        (mem_ordersBefore_iff h i w le_rfl).mpr ⟨t, ht.trans r.isLt, hl, hi, ho⟩
      simpa only [Finset.mem_singleton.mp (onlyIssued hw')] using hw'
  exact Finset.Subset.antisymm onlyIssued (Finset.singleton_subset_iff.mpr hmem)

private theorem recover_relay (H : h.FollowsSM m faulty v) {r : Fin h.length}
    (hr : h.Learns r) (a : Fin (h.get r).message.chain.length)
    (ha : some ((h.get r).message.chain.get a) ∉ faulty) :
    ∃ t : Fin h.length, t < r ∧ h.Learns t ∧
      (h.get t).message.recipient = (h.get r).message.chain.get a ∧
      (h.get t).message.order = (h.get r).message.order ∧
      (h.get t).message.chain = (h.get r).message.chain.take a ∧
      (h.get t).message.MayForward m := by
  obtain ⟨s, hsr, hs, hsender, ho, hchain⟩ := H.lieutenantSignature r hr.1 hr.2.1.1 a ha
  rcases H.loyalSend s hs (hsender.symm ▸ ha) with he | ⟨t, hts, ht, hforward, -, hrelay⟩
  · have he' : (h.get s).message.sender = none := congrArg Message.sender he
    rw [hsender] at he'
    cases he'
  have hs' : (h.get s).message.sender = some (h.get t).message.recipient :=
    congrArg Message.sender hrelay
  have hrec := Option.some.inj (hs'.symm.trans hsender)
  have hchain' := (congrArg Message.chain hrelay).symm.trans hchain
  change (h.get t).message.chain ++ [(h.get t).message.recipient] = _ at hchain'
  rw [hrec, List.take_succ_eq_append_getElem a.isLt] at hchain'
  exact ⟨t, Nat.lt_trans hts hsr, ht, hrec, (congrArg Message.order hrelay).symm.trans ho,
    List.append_cancel_right hchain', hforward⟩

private theorem mem_orders_of_mayForward (H : h.FollowsSM m faulty v) {r : Fin h.length}
    (hr : h.Learns r) (hi : some (h.get r).message.recipient ∉ faulty)
    (hf : (h.get r).message.MayForward m) (j : L) (hj : some j ∉ faulty) :
    (h.get r).message.order ∈ h.orders j := by
  by_cases he : j = (h.get r).message.recipient
  · simpa only [he] using learns_mem_orders hr
  by_cases hm : j ∈ (h.get r).message.chain
  · obtain ⟨a, ha⟩ := List.mem_iff_get.mp hm
    obtain ⟨t, -, ht, hrec, ho, -, -⟩ := H.recover_relay hr a (by simpa only [ha] using hj)
    simpa only [hrec, ha, ho] using learns_mem_orders ht
  · obtain ⟨s, -, hs, hrelay⟩ := H.forward r hr hi hf j ⟨he, hm⟩
    obtain ⟨t, -, ht, hmsg⟩ := H.delivered s hs
    have hd := hmsg.trans hrelay
    have hp : (h.get t).message.Proper := hd.symm ▸ Message.proper_relay hr.2.1 ⟨he, hm⟩
    have hn : (h.get t).message.chain ≠ [] := by
      rw [hd]
      simp [Message.relay]
    convert receive_mem_orders ht hp (fun hnil => (hn hnil).elim) using 1 <;>
      rw [hd] <;> rfl

omit [DecidableEq L] in
private theorem exists_loyal_signer {chain : List L} (hd : chain.Nodup) (hm : m ≤ chain.length)
    (hc : none ∈ faulty) (hb : faulty.card ≤ m) :
    ∃ a : Fin chain.length, some (chain.get a) ∉ faulty := by
  classical
  by_contra! hall
  have hsub : (none :: chain.map some).toFinset ⊆ faulty := by
    intro q hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_map] at hq
    rcases hq with rfl | ⟨i, hi, rfl⟩
    · exact hc
    · obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hi
      exact hall a
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (by simp [List.nodup_map_iff, Option.some_injective, hd]),
    List.length_cons, List.length_map] at hcard
  omega

/-- In a completed history satisfying `FollowsSM` and the fault bound, an order known to any
loyal lieutenant is known to every loyal lieutenant. At the cutoff with a faulty commander, a
loyal lieutenant's signature must occur in the chain. Its genuine prefix was accepted earlier
and was short enough to forward. -/
theorem orders_eq (H : h.FollowsSM m faulty v) (hb : faulty.card ≤ m) {i j : L}
    (hi : some i ∉ faulty) (hj : some j ∉ faulty) : h.orders i = h.orders j := by
  by_cases hc : none ∉ faulty
  · rw [H.orders_eq_singleton hc i, H.orders_eq_singleton hc j]
  have hc' : none ∈ faulty := not_not.mp hc
  suffices transfer : ∀ {p q : L}, some p ∉ faulty → some q ∉ faulty → h.orders p ⊆ h.orders q by
    exact Finset.Subset.antisymm (transfer hi hj) (transfer hj hi)
  intro p q hp hq w hw
  obtain ⟨r, -, hr, hrec, horder⟩ := (mem_ordersBefore_iff h p w le_rfl).mp hw
  rw [← horder]
  by_cases hf : (h.get r).message.MayForward m
  · exact H.mem_orders_of_mayForward hr (hrec.symm ▸ hp) hf q hq
  have hm : m ≤ (h.get r).message.chain.length := Nat.le_of_not_gt (fun hlt => hf (Or.inr hlt))
  obtain ⟨a, ha⟩ := exists_loyal_signer hr.2.1.2.1 hm hc' hb
  obtain ⟨t, -, ht, hsigner, ho, -, htf⟩ := H.recover_relay hr a ha
  rw [← ho]
  exact H.mem_orders_of_mayForward ht (hsigner.symm ▸ ha) htf q hq

end FollowsSM

end History

/-- A single choice function shared by all lieutenants. It returns the only order from a
singleton, and the distinguished retreat order from the empty set. There is no additional
condition on the value returned on sets with multiple elements. -/
structure Choice (V : Type*) [DecidableEq V] where
  /-- The distinguished order for an empty set. -/
  retreat : V
  /-- The function applied to the final finite set of orders. -/
  select : Finset V → V
  /-- A singleton determines its own order. -/
  select_singleton : ∀ v, select {v} = v
  /-- The default order is used when no order is accepted. -/
  select_empty : select ∅ = retreat

/-- In step (3), lieutenant `i` applies the shared choice function to the final set of orders. -/
def History.decision {L V : Type*} [DecidableEq L] [DecidableEq V]
    (h : History L V) (choice : Choice V) (i : L) : V := choice.select (h.orders i)

/-- **Signed-message Byzantine agreement** (Lamport–Shostak–Pease, §4, Theorem 2).
For every completed history of `SM(m)` with at most `m` traitors, all loyal lieutenants decide
the same order (IC1), and if the commander is loyal, every loyal lieutenant decides the order
it issued (IC2). There is no lower bound on the number of lieutenants. -/
theorem sm_interactiveConsistency {L V : Type*} [DecidableEq L] [DecidableEq V]
    {h : History L V} {m : ℕ} {faulty : Finset (Option L)} {v : V}
    (choice : Choice V) (H : h.FollowsSM m faulty v) (hb : faulty.card ≤ m) :
    (∀ i j : L, some i ∉ faulty → some j ∉ faulty → h.decision choice i = h.decision choice j) ∧
    (none ∉ faulty → ∀ i : L, some i ∉ faulty → h.decision choice i = v) := by
  refine ⟨fun i j hi hj => congrArg choice.select (H.orders_eq hb hi hj), fun hc i _ => ?_⟩
  rw [History.decision, H.orders_eq_singleton hc i, choice.select_singleton]

end Cslib.Distributed.Byzantine.SignedMessages
