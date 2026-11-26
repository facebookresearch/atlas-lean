/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Causal delivery of updates
-/
module

public import CSLibExt.Computability.Distributed.LamportClock

/-!
# Causal delivery of updates

Causal delivery of the updates of a replicated object (M. Shapiro, N. Preguiça, C. Baquero and
M. Zawirski, *Conflict-free replicated data types*, SSS 2011; INRIA research report RR-7687,
Section 2.4), over the executions of `LamportClock.lean`, read as executions of a replicated
system. The processes are the replicas. An event that receives no message issues a new update,
which is identified with the position of that event; an event that receives from position `i`
delivers the update issued at position `i`. A replica counts as having delivered the updates it
issues, as the replica where an update originates applies it at once.

Happened-before is Lamport's relation `LamportClock.HappensBefore` on the events: the transitive
closure of replica-local order and of the order from the issue of an update to each of its
deliveries. An update happened before another when its issue happened before the issue of the
other.

* `CausalDelivery`: every replica delivers an update only after it has issued or delivered every
  update that happened before it.
* `causalDelivery_of_consistent`: if every replica that delivers an update also issues or
  delivers every update that happened before it, and does so in an order consistent with
  happened-before, then the execution provides causal delivery.
* `happensBefore_iff_transGen_delivered`: when every receipt names an earlier issue,
  happened-before between updates is the transitive closure of the replica-local order of issues
  and of the order from delivering an update to issuing a later one at the same replica, the
  order by which Shapiro et al. define happened-before.
-/

@[expose] public section

namespace Cslib.Distributed.Replication

open LamportClock

variable {R : Type*}

/-- **Causal delivery of updates.** Read an execution $e_0, \dots, e_{n-1}$, whose events each
belong to a process and may receive the message of the event at some position, as an execution
of a replicated system whose replicas are the processes: an event that receives no message issues
a new update, identified with the position of that event, and an event that receives from
position $i$ delivers the update issued at position $i$. An update $u_1$ happened before an
update $u_2$ when the issue of $u_1$ happened before the issue of $u_2$ in Lamport's sense: a
chain of events leads from the issue of $u_1$ to the issue of $u_2$, in which each event is
followed by a later event that belongs to the same replica or receives from it. The execution
provides causal delivery when every replica delivers an update $u_2$ only after it has delivered
every update $u_1$ that happened before $u_2$, where a replica counts the updates it issues as
delivered. That is, whenever the event at position $j$, of replica $r$, delivers the update $u_2$
issued at position $i_2$, and the update $u_1$ issued at position $i_1$ happened before $u_2$,
some position $k < j$ holds an event of $r$ that either issues $u_1$ ($k = i_1$) or delivers it.
-/
def CausalDelivery (tr : List (Event R)) : Prop :=
  ∀ (j i₁ i₂ : ℕ) (ej e₁ e₂ : Event R), tr[j]? = some ej → ej.recvFrom = some i₂ →
    tr[i₂]? = some e₂ → e₂.recvFrom = none → tr[i₁]? = some e₁ → e₁.recvFrom = none →
    HappensBefore tr i₁ i₂ →
    ∃ k < j, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = ej.proc ∧
      (k = i₁ ∨ ek.recvFrom = some i₁)

/- Delivery consistent with happened-before is causal. Say that the event at position `k`, of
replica `r`, handles the update issued at position `i` when `k = i` or the event delivers that
update. Suppose that whenever replica `r` delivers an update `u₂` and an update `u₁` happened
before `u₂`, some event of `r` handles `u₁` (`hpast`), and every event of `r` that handles `u₁`
comes before every event of `r` that delivers `u₂` (`horder`). Then the execution provides causal
delivery. -/
theorem causalDelivery_of_consistent {tr : List (Event R)}
    (hpast : ∀ (j i₁ i₂ : ℕ) (ej e₁ e₂ : Event R), tr[j]? = some ej → ej.recvFrom = some i₂ →
      tr[i₂]? = some e₂ → e₂.recvFrom = none → tr[i₁]? = some e₁ → e₁.recvFrom = none →
      HappensBefore tr i₁ i₂ →
      ∃ k, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = ej.proc ∧
        (k = i₁ ∨ ek.recvFrom = some i₁))
    (horder : ∀ (j k i₁ i₂ : ℕ) (ej ek e₁ e₂ : Event R), tr[j]? = some ej →
      ej.recvFrom = some i₂ → tr[i₂]? = some e₂ → e₂.recvFrom = none → tr[i₁]? = some e₁ →
      e₁.recvFrom = none → HappensBefore tr i₁ i₂ → tr[k]? = some ek → ek.proc = ej.proc →
      (k = i₁ ∨ ek.recvFrom = some i₁) → k < j) :
    CausalDelivery tr := by
  intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  obtain ⟨k, ek, hk, hp, hu⟩ := hpast j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  exact ⟨k, horder j k i₁ i₂ ej ek e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb hk hp hu, ek, hk, hp, hu⟩

/-- **Happened-before between updates, by delivery.** Read a well-formed execution as an
execution of a replicated system whose replicas are the processes: an event that receives no
message issues a new update, identified with the position of that event, and an event that
receives from position $i$ delivers the update issued at position $i$. Suppose that every receipt
names a position that holds an issue. Say that an update $a$ precedes an update $b$ directly when
the replica that issues $b$ has issued or delivered $a$ before it issues $b$: some position
$k < b$ holds an event of that replica that either is the issue of $a$ ($k = a$) or delivers $a$.
Then for any two updates $u_1$ and $u_2$, position $u_1$ happened before position $u_2$ in
Lamport's sense if and only if there is a chain $u_1 = v_0, v_1, \dots, v_m = u_2$ of updates
with $m \ge 1$ in which each $v_l$ precedes $v_{l+1}$ directly. So happened-before between
updates is the transitive closure of the replica-local order of issues and of the order from
delivering an update to issuing a later one at the same replica. -/
theorem happensBefore_iff_transGen_delivered {tr : List (Event R)} (hwf : WellFormed tr)
    (hiss : ∀ (j i : ℕ) (ej : Event R), tr[j]? = some ej → ej.recvFrom = some i →
      ∃ ei : Event R, tr[i]? = some ei ∧ ei.recvFrom = none)
    {i₁ i₂ : ℕ} {e₁ e₂ : Event R} (h₁ : tr[i₁]? = some e₁) (hn₁ : e₁.recvFrom = none)
    (h₂ : tr[i₂]? = some e₂) (hn₂ : e₂.recvFrom = none) :
    HappensBefore tr i₁ i₂ ↔ Relation.TransGen (fun a b => ∃ ea eb : Event R,
      tr[a]? = some ea ∧ ea.recvFrom = none ∧ tr[b]? = some eb ∧ eb.recvFrom = none ∧
      ∃ k < b, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = eb.proc ∧
        (k = a ∨ ek.recvFrom = some a)) i₁ i₂ := by
  set U : ℕ → ℕ → Prop := fun a b => ∃ ea eb : Event R,
      tr[a]? = some ea ∧ ea.recvFrom = none ∧ tr[b]? = some eb ∧ eb.recvFrom = none ∧
      ∃ k < b, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = eb.proc ∧
        (k = a ∨ ek.recvFrom = some a)
  constructor
  · intro h
    -- Every event that the issue of `u₁` happened before belongs to a replica that has, by
    -- then, handled an update `v` equal to `u₁` or reached from `u₁` by direct steps.
    have key : ∀ {m : ℕ}, HappensBefore tr i₁ m → ∀ em : Event R, tr[m]? = some em →
        ∃ v, ∃ ev : Event R, tr[v]? = some ev ∧ ev.recvFrom = none ∧
          (v = i₁ ∨ Relation.TransGen U i₁ v) ∧
          ∃ k ≤ m, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = em.proc ∧
            (k = v ∨ ek.recvFrom = some v) := by
      intro m hm
      induction hm with
      | single hs =>
          obtain ⟨hlt, ei, em', hi, hm', hp | hr⟩ := hs <;> intro em hem <;>
            obtain rfl : em' = em := Option.some.inj (hm'.symm.trans hem)
          · exact ⟨i₁, e₁, h₁, hn₁, Or.inl rfl, i₁, hlt.le, ei, hi, hp, Or.inl rfl⟩
          · exact ⟨i₁, e₁, h₁, hn₁, Or.inl rfl, _, le_rfl, em', hem, rfl, Or.inr hr⟩
      | @tail b c _ hs ih =>
          obtain ⟨hbc, eb, ec, hb, hc, hp | hr⟩ := hs <;> intro em hem <;>
            obtain rfl : ec = em := Option.some.inj (hc.symm.trans hem) <;>
            obtain ⟨v, ev, hv, hnv, hvi, k, hkb, ek, hk, hpk, hkv⟩ := ih eb hb
          · exact ⟨v, ev, hv, hnv, hvi, k, hkb.trans hbc.le, ek, hk, hpk.trans hp, hkv⟩
          · obtain ⟨eb', hb', hnb⟩ := hiss c b ec hc hr
            obtain rfl : eb' = eb := Option.some.inj (hb'.symm.trans hb)
            have hvb : b = v ∨ Relation.TransGen U i₁ b := by
              rcases hkb.lt_or_eq with hkb | rfl
              · have hU' : U v b := ⟨ev, eb', hv, hnv, hb, hnb, k, hkb, ek, hk, hpk, hkv⟩
                rcases hvi with rfl | hvi
                · exact Or.inr (.single hU')
                · exact Or.inr (hvi.tail hU')
              · rw [hk] at hb
                obtain rfl : ek = eb' := Option.some.inj hb
                rcases hkv with hkv | hkv
                · exact Or.inl hkv
                · rw [hnb] at hkv; exact absurd hkv (by simp)
            refine ⟨b, eb', hb, hnb, ?_, c, le_rfl, ec, hc, rfl, Or.inr hr⟩
            rcases hvb with rfl | hvb
            · exact hvi
            · exact Or.inr hvb
    obtain ⟨v, ev, hv, hnv, hvi, k, hk2, ek, hk, hpk, hkv⟩ := key h e₂ h₂
    rcases hk2.lt_or_eq with hk2 | rfl
    · have hU' : U v i₂ := ⟨ev, e₂, hv, hnv, h₂, hn₂, k, hk2, ek, hk, hpk, hkv⟩
      rcases hvi with rfl | hvi
      · exact .single hU'
      · exact hvi.tail hU'
    · rw [hk] at h₂
      obtain rfl : ek = e₂ := Option.some.inj h₂
      rcases hkv with rfl | hkv
      · rcases hvi with rfl | hvi
        · exact absurd h (happensBefore_irrefl tr _)
        · exact hvi
      · rw [hn₂] at hkv; exact absurd hkv (by simp)
  · intro h
    have hstep : ∀ {a b : ℕ}, U a b → HappensBefore tr a b := by
      rintro a b ⟨ea, eb, ha, -, hb, -, k, hkb, ek, hk, hp, rfl | hr⟩
      · exact .single ⟨hkb, ek, eb, hk, hb, Or.inl hp⟩
      · exact .tail (.single ⟨hwf k ek a hk hr, ea, ek, ha, hk, Or.inr hr⟩)
          ⟨hkb, ek, eb, hk, hb, Or.inl hp⟩
    exact Relation.TransGen.lift' id (fun _ _ hs => hstep hs) _ _ h

end Cslib.Distributed.Replication
