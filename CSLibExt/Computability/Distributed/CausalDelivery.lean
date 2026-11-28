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
issues, as the replica where an update originates applies it at once. An event that receives from
a position holding no issue delivers nothing: it stands for a message that carries no update.

* `DirectlyBefore`: an update directly precedes another when the replica that issues the second
  has issued or delivered the first before; this is the order by which Shapiro et al. define
  happened-before between updates.
* `DeliveryOrder`: the order-only test on arbitrary event lists.
* `CausalDelivery`: a well-formed execution satisfies `DeliveryOrder`: every replica delivers an
  update only after it has issued or delivered every update that happened before it, where
  happened-before is the transitive closure of `DirectlyBefore`.
* `happensBefore_iff_transGen_directlyBefore`: when every receipt names an earlier issue, the
  transitive closure of `DirectlyBefore` is Lamport's happened-before (`LamportClock.HappensBefore`)
  between the issues. Without that hypothesis the two can differ (see the tests): a receipt from
  an earlier receipt delivers nothing, but adds a step to Lamport's relation.
-/

@[expose] public section

namespace Cslib.Distributed.Replication

open LamportClock

variable {R : Type*}

/-- **An update directly precedes another, by delivery.** Read an execution $e_0, \dots, e_{n-1}$,
whose events each belong to a process and may receive the message of the event at some position,
as an execution of a replicated system whose replicas are the processes: an event that receives no
message issues a new update, identified with the position of that event, and a receipt naming
position $i$ delivers the update at $i$ if that position holds an issue; otherwise it delivers no
update. An update $a$ directly precedes an update $b$ when the replica that issues $b$ has issued
or delivered $a$ before it issues $b$: positions $a$ and $b$ hold issues, and some position
$k < b$ holds an event of the replica that issues $b$ that either is the issue of $a$ ($k = a$) or
delivers $a$. This is the relation by which M. Shapiro, N. Preguiça, C. Baquero and M. Zawirski
define happened-before between updates (*Conflict-free replicated data types*, INRIA research
report RR-7687, version 2, Section 2.4, p. 7: Definition 2.5 and the definition of happened-before
after it): $a$ belongs to the causal history of the replica of $b$ just before $b$ is issued. -/
def DirectlyBefore (tr : List (Event R)) (a b : ℕ) : Prop :=
  ∃ ea eb : Event R, tr[a]? = some ea ∧ ea.recvFrom = none ∧ tr[b]? = some eb ∧
    eb.recvFrom = none ∧ ∃ k < b, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = eb.proc ∧
      (k = a ∨ ek.recvFrom = some a)

theorem DirectlyBefore.lt {tr : List (Event R)} (hwf : WellFormed tr) {a b : ℕ}
    (h : DirectlyBefore tr a b) : a < b := by
  obtain ⟨-, -, -, -, -, -, k, hkb, ek, hk, -, rfl | hr⟩ := h
  · exact hkb
  · exact (hwf k ek a hk hr).trans hkb

theorem lt_of_transGen_directlyBefore {tr : List (Event R)} (hwf : WellFormed tr) {a b : ℕ}
    (h : Relation.TransGen (DirectlyBefore tr) a b) : a < b := by
  induction h with
  | single h => exact h.lt hwf
  | tail _ h ih => exact ih.trans (h.lt hwf)

/-- **Order of update deliveries.** In an event list, each receipt of an update must be
preceded at the same replica by the issue or delivery of each update in its causal history.
The causal history is given by the transitive closure of `DirectlyBefore`. A receipt delivers
an update only if it names a position holding an issue. This predicate checks delivery order
alone; it does not require receipts to refer to earlier positions. -/
def DeliveryOrder (tr : List (Event R)) : Prop :=
  ∀ (j i₁ i₂ : ℕ) (ej e₁ e₂ : Event R), tr[j]? = some ej → ej.recvFrom = some i₂ →
    tr[i₂]? = some e₂ → e₂.recvFrom = none → tr[i₁]? = some e₁ → e₁.recvFrom = none →
    Relation.TransGen (DirectlyBefore tr) i₁ i₂ →
    ∃ k < j, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = ej.proc ∧
      (k = i₁ ∨ ek.recvFrom = some i₁)

/-- **Causal delivery of updates.** In a finite list of replica events, a receipt is well formed
only if it names an earlier event. A receipt of an update issued at that earlier position must
be preceded at the same replica by the issue or delivery of each update in its causal history.
That history is given by nonempty chains of `DirectlyBefore`: an update directly precedes another
when the replica issuing the latter has already issued or received the former.

This is only a safety condition: an update can be delivered more than once, or never. A receipt
of a message that carries no update does not count as an update delivery. -/
def CausalDelivery (tr : List (Event R)) : Prop :=
  WellFormed tr ∧ DeliveryOrder tr

/-- **Happened-before between updates, by delivery.** Read a well-formed execution, one in which
every receipt names an earlier position, as an execution of a replicated system whose replicas
are the processes: an event that receives no message issues a new update, identified with the
position of that event, and an event that receives from position $i$ delivers the update issued
at position $i$. Suppose that every receipt names a position that holds an issue. Say that an
update $a$ directly precedes an update $b$ when the replica that issues $b$ has issued or
delivered $a$ before it issues $b$. Then for any two updates $u_1$ and $u_2$, position $u_1$
happened before position $u_2$ in Lamport's sense if and only if there is a chain
$u_1 = v_0, v_1, \dots, v_m = u_2$ of updates with $m \ge 1$ in which each $v_l$ directly
precedes $v_{l+1}$. So on such executions Lamport's happened-before between updates is the
transitive closure of the replica-local order of issues and of the order from delivering an
update to issuing a later one at the same replica. -/
theorem happensBefore_iff_transGen_directlyBefore {tr : List (Event R)} (hwf : WellFormed tr)
    (hiss : ∀ (j i : ℕ) (ej : Event R), tr[j]? = some ej → ej.recvFrom = some i →
      ∃ ei : Event R, tr[i]? = some ei ∧ ei.recvFrom = none)
    {i₁ i₂ : ℕ} {e₁ e₂ : Event R} (h₁ : tr[i₁]? = some e₁) (hn₁ : e₁.recvFrom = none)
    (h₂ : tr[i₂]? = some e₂) (hn₂ : e₂.recvFrom = none) :
    HappensBefore tr i₁ i₂ ↔ Relation.TransGen (DirectlyBefore tr) i₁ i₂ := by
  constructor
  · intro h
    -- Every event that the issue of `u₁` happened before belongs to a replica that has, by
    -- then, handled an update `v` equal to `u₁` or reached from `u₁` by direct steps.
    have key : ∀ {m : ℕ}, HappensBefore tr i₁ m → ∀ em : Event R, tr[m]? = some em →
        ∃ v, ∃ ev : Event R, tr[v]? = some ev ∧ ev.recvFrom = none ∧
          (v = i₁ ∨ Relation.TransGen (DirectlyBefore tr) i₁ v) ∧
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
            have hvb : b = v ∨ Relation.TransGen (DirectlyBefore tr) i₁ b := by
              rcases hkb.lt_or_eq with hkb | rfl
              · have hU' : DirectlyBefore tr v b :=
                  ⟨ev, eb', hv, hnv, hb, hnb, k, hkb, ek, hk, hpk, hkv⟩
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
    · have hU' : DirectlyBefore tr v i₂ := ⟨ev, e₂, hv, hnv, h₂, hn₂, k, hk2, ek, hk, hpk, hkv⟩
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
    have hstep : ∀ {a b : ℕ}, DirectlyBefore tr a b → HappensBefore tr a b := by
      rintro a b ⟨ea, eb, ha, -, hb, -, k, hkb, ek, hk, hp, rfl | hr⟩
      · exact .single ⟨hkb, ek, eb, hk, hb, Or.inl hp⟩
      · exact .tail (.single ⟨hwf k ek a hk hr, ea, ek, ha, hk, Or.inr hr⟩)
          ⟨hkb, ek, eb, hk, hb, Or.inl hp⟩
    exact Relation.TransGen.lift' id (fun _ _ hs => hstep hs) _ _ h

end Cslib.Distributed.Replication
