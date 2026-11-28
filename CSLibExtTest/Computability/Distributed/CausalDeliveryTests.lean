/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.CausalDelivery

/-!
# Tests for causal delivery of updates

* `tr`, over three replicas: replica `0` issues an update `u` (position `0`); replica `1`
  delivers `u` and then issues an update `v` (position `2`), so `u` directly precedes `v`;
  replica `2` delivers `u` and then `v`, and replica `0` delivers `v`. This execution provides
  causal delivery. Replica `0` never delivers `u`: it issued it.
* `bad`: replica `2` delivers `v` without having delivered `u`, and causal delivery fails.
* `conc`: replicas `0` and `1` issue concurrent updates, which replica `2` delivers in the
  opposite order to replica `0`. Causal delivery holds, as it does not order concurrent updates.
* The empty execution provides causal delivery.
* In `tr`, `happensBefore_iff_transGen_directlyBefore` relates direct precedence to Lamport's
  happened-before, and on every execution whose receipts name earlier issues causal delivery is
  the same as the condition stated with Lamport's happened-before (`LamportCausalDelivery`).
* `relay`, over four replicas: a well-formed execution in which replica `2` receives from the
  delivery at position `1`. That receipt delivers nothing, so no chain of direct precedence joins
  the update issued at `0` to the update issued at `3`, and causal delivery holds; but the
  receipt makes the issue at `0` happen before the issue at `3` in Lamport's sense, and the
  condition stated with Lamport's happened-before fails.
* `receiveBeforeIssue`: the order-only test holds, but causal delivery fails because a receipt
  names a later issue.
* `early`: the same forward reference also fails the order-only test when the received update
  has a causal predecessor that was not yet delivered.
* `backward`: a receipt that names a later issue makes that update directly precede an earlier
  one, which Lamport's happened-before never does; so the bridge theorem needs well-formedness.
-/

@[expose] public section

namespace Cslib.Distributed.Replication.CausalDeliveryTests

open LamportClock

theorem exists_of_transGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) : ∃ c, r c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

/-- An execution with causal delivery. -/
def tr : List (Event (Fin 3)) :=
  [⟨0, none⟩, ⟨1, some 0⟩, ⟨1, none⟩, ⟨2, some 0⟩, ⟨2, some 2⟩, ⟨0, some 2⟩]

theorem tr_wellFormed : WellFormed tr := by
  intro j ej i hj hr
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [tr] at hj <;> subst hj <;> simp at hr <;>
    omega

/-- `u` directly precedes `v`: `u` is delivered at replica `1`, which then issues `v`. -/
theorem db02 : DirectlyBefore tr 0 2 :=
  ⟨_, _, rfl, rfl, rfl, rfl, 1, by decide, _, rfl, rfl, Or.inr rfl⟩

example : CausalDelivery tr := by
  refine ⟨tr_wellFormed, ?_⟩
  intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  have hlt := lt_of_transGen_directlyBefore tr_wellFormed hhb
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [tr] at hj <;> subst hj <;>
    simp at hr <;> subst hr
  all_goals first
    | omega
    | (rcases i₁ with _ | _ | i₁
       · first
         | exact ⟨3, by decide, _, rfl, rfl, Or.inr rfl⟩
         | exact ⟨0, by decide, _, rfl, rfl, Or.inl rfl⟩
       · simp [tr] at h₁; subst h₁; simp at hn₁
       · omega)

/-- An execution without causal delivery. -/
def bad : List (Event (Fin 3)) :=
  [⟨0, none⟩, ⟨1, some 0⟩, ⟨1, none⟩, ⟨2, some 2⟩]

/-- Replica `2` delivers `v` although it has not delivered `u`, which happened before `v`. -/
example : ¬ CausalDelivery bad := by
  intro h
  obtain ⟨k, hk, ek, hek, hp, -⟩ := h.2 3 0 2 _ _ _ rfl rfl rfl rfl rfl rfl
    (.single ⟨_, _, rfl, rfl, rfl, rfl, 1, by decide, _, rfl, rfl, Or.inr rfl⟩)
  rcases k with _ | _ | _ | k
  · simp [bad] at hek; subst hek; simp at hp
  · simp [bad] at hek; subst hek; simp at hp
  · simp [bad] at hek; subst hek; simp at hp
  · omega

/-- Concurrent updates delivered in different orders. -/
def conc : List (Event (Fin 3)) :=
  [⟨0, none⟩, ⟨1, none⟩, ⟨2, some 1⟩, ⟨2, some 0⟩, ⟨0, some 1⟩, ⟨1, some 0⟩]

/-- Nothing directly precedes the two updates of `conc`. -/
theorem conc_not_directlyBefore {a b : ℕ} (hb : b ≤ 1) : ¬ DirectlyBefore conc a b := by
  rintro ⟨-, eb, -, -, heb, -, k, hk, ek, hek, hp, -⟩
  rcases b with _ | _ | b
  · omega
  · obtain rfl : k = 0 := by omega
    simp [conc] at heb hek; subst heb hek; simp at hp
  · omega

/-- The two updates of `conc` are concurrent. -/
example : ¬ Relation.TransGen (DirectlyBefore conc) 0 1 ∧
    ¬ Relation.TransGen (DirectlyBefore conc) 1 0 :=
  ⟨fun h => (exists_of_transGen h).elim fun _ h => conc_not_directlyBefore le_rfl h,
    fun h => (exists_of_transGen h).elim fun _ h => conc_not_directlyBefore (by decide) h⟩

example : CausalDelivery conc := by
  refine ⟨?_, ?_⟩
  · intro j ej i hj hr
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [conc] at hj <;> subst hj <;>
      simp at hr <;> omega
  · intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
    obtain ⟨c, hc⟩ := exists_of_transGen hhb
    rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [conc] at hj <;> subst hj <;>
      simp at hr <;> subst hr
    all_goals exact absurd hc (conc_not_directlyBefore (by decide))

example : CausalDelivery ([] : List (Event (Fin 3))) := by
  refine ⟨?_, ?_⟩
  · intro j _ _ hj
    simp at hj
  · intro j _ _ _ _ _ hj
    simp at hj

/-! ## Lamport's happened-before -/

/-- Causal delivery stated with Lamport's happened-before between the issues in place of
happened-before by delivery. -/
def LamportCausalDelivery {R : Type*} (tr : List (Event R)) : Prop :=
  ∀ (j i₁ i₂ : ℕ) (ej e₁ e₂ : Event R), tr[j]? = some ej → ej.recvFrom = some i₂ →
    tr[i₂]? = some e₂ → e₂.recvFrom = none → tr[i₁]? = some e₁ → e₁.recvFrom = none →
    HappensBefore tr i₁ i₂ →
    ∃ k < j, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = ej.proc ∧
      (k = i₁ ∨ ek.recvFrom = some i₁)

/-- When every receipt names an earlier issue, the two conditions agree. -/
theorem causalDelivery_iff_lamport {R : Type*} {tr : List (Event R)} (hwf : WellFormed tr)
    (hiss : ∀ (j i : ℕ) (ej : Event R), tr[j]? = some ej → ej.recvFrom = some i →
      ∃ ei : Event R, tr[i]? = some ei ∧ ei.recvFrom = none) :
    CausalDelivery tr ↔ LamportCausalDelivery tr := by
  constructor
  · intro h j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
    exact h.2 j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁
      ((happensBefore_iff_transGen_directlyBefore hwf hiss h₁ hn₁ h₂ hn₂).mp hhb)
  · intro h
    refine ⟨hwf, ?_⟩
    intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
    exact h j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁
      ((happensBefore_iff_transGen_directlyBefore hwf hiss h₁ hn₁ h₂ hn₂).mpr hhb)

theorem tr_receipts : ∀ (j i : ℕ) (ej : Event (Fin 3)), tr[j]? = some ej →
    ej.recvFrom = some i → ∃ ei : Event (Fin 3), tr[i]? = some ei ∧ ei.recvFrom = none := by
  intro j i ej hj hr
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [tr] at hj <;> subst hj <;> simp at hr <;>
    subst hr <;> exact ⟨_, rfl, rfl⟩

/-- Replica `1` delivers `u` before it issues `v`, so `u` happened before `v`. -/
example : HappensBefore tr 0 2 :=
  (happensBefore_iff_transGen_directlyBefore tr_wellFormed tr_receipts (i₁ := 0) (i₂ := 2) rfl rfl
    rfl rfl).mpr (.single db02)

example : Relation.TransGen (DirectlyBefore tr) 0 2 :=
  (happensBefore_iff_transGen_directlyBefore tr_wellFormed tr_receipts rfl rfl rfl rfl).mp
    (.tail (b := 1) (.single ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩)
      ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩)

example : LamportCausalDelivery tr ↔ CausalDelivery tr :=
  (causalDelivery_iff_lamport tr_wellFormed tr_receipts).symm

/-! ## Unusual executions -/

/-- A well-formed execution in which replica `2` receives from the delivery at position `1`, and
replica `3` delivers the update issued at position `3`. -/
def relay : List (Event (Fin 4)) :=
  [⟨0, none⟩, ⟨1, some 0⟩, ⟨2, some 1⟩, ⟨2, none⟩, ⟨3, some 3⟩]

theorem relay_wellFormed : WellFormed relay := by
  intro j ej i hj hr
  rcases j with _ | _ | _ | _ | _ | j <;> simp [relay] at hj <;> subst hj <;> simp at hr <;>
    omega

/-- The receipt from the delivery at position `1` makes the issue at `0` happen before the issue
at `3` in Lamport's sense. -/
theorem relay_hb03 : HappensBefore relay 0 3 :=
  .tail (b := 2) (.tail (b := 1) (.single ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩)
    ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩) ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩

/-- No update directly precedes the update issued at `3`: replica `2` never delivers the update
issued at `0`. -/
theorem relay_not_directlyBefore (b : ℕ) : ¬ DirectlyBefore relay b 3 := by
  rintro ⟨ea, eb, ha, hna, hb, -, k, hk, ek, hek, hp, hkb⟩
  simp only [relay] at hb
  obtain rfl := Option.some.inj hb
  rcases k with _ | _ | _ | k
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek
    rcases hkb with rfl | hkb
    · simp [relay] at ha; subst ha; simp at hna
    · simp at hkb; subst hkb; simp [relay] at ha; subst ha; simp at hna
  · omega

example : ¬ Relation.TransGen (DirectlyBefore relay) 0 3 := fun h =>
  (exists_of_transGen h).elim fun b h => relay_not_directlyBefore b h

/-- Causal delivery holds: the receipt at position `2` delivers nothing, and nothing happened
before the updates delivered at positions `1` and `4`. -/
example : CausalDelivery relay := by
  refine ⟨relay_wellFormed, ?_⟩
  intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  obtain ⟨c, hc⟩ := exists_of_transGen hhb
  rcases j with _ | _ | _ | _ | _ | j <;> simp [relay] at hj <;> subst hj <;>
    simp at hr <;> subst hr
  all_goals first
    | (obtain ⟨-, -, -, -, -, -, k, hk, -⟩ := hc; omega)
    | exact absurd hc (relay_not_directlyBefore c)
    | (simp [relay] at h₂; subst h₂; simp at hn₂)

/-- The condition stated with Lamport's happened-before fails: replica `3` delivers the update
issued at `3` without having delivered the update issued at `0`. -/
example : ¬ LamportCausalDelivery relay := by
  intro h
  obtain ⟨k, hk, ek, hek, hp, -⟩ := h 4 0 3 _ _ _ rfl rfl rfl rfl rfl rfl relay_hb03
  rcases k with _ | _ | _ | _ | k
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · omega

/-- The order-only test does not reject a receipt of the sole update before it is issued. -/
private def receiveBeforeIssue : List (Event (Fin 2)) := [⟨0, some 1⟩, ⟨1, none⟩]

example : DeliveryOrder receiveBeforeIssue := by
  intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  obtain ⟨_, eb, _, _, hb, _, k, hk, ek, hek, hp, _⟩ := (exists_of_transGen hhb).choose_spec
  rcases i₂ with _ | _ | i₂
  · omega
  · obtain rfl : k = 0 := by omega
    simp [receiveBeforeIssue] at hb hek
    subst eb ek
    simp at hp
  · simp [receiveBeforeIssue] at h₂

/-- Causal delivery rejects the same list because its receipt points forward. -/
example : ¬ CausalDelivery receiveBeforeIssue := fun h =>
  absurd (h.1 0 _ 1 rfl rfl) (by decide)

/-- An event list that is not well formed: the receipt at position `0` names the update issued
at position `2`, and replica `0` issues updates at positions `1` and `2`. -/
def early : List (Event (Fin 2)) :=
  [⟨1, some 2⟩, ⟨0, none⟩, ⟨0, none⟩]

example : ¬ WellFormed early := fun h => absurd (h 0 _ 2 rfl rfl) (by decide)

/-- In the order-only test, this receipt is a delivery: the update issued at `1` happened
before the one issued at `2`, and replica `1` has delivered nothing before position `0`. -/
example : ¬ DeliveryOrder early := by
  intro h
  obtain ⟨k, hk, -⟩ := h 0 1 2 _ _ _ rfl rfl rfl rfl rfl rfl
    (.single ⟨_, _, rfl, rfl, rfl, rfl, 1, by decide, _, rfl, rfl, Or.inl rfl⟩)
  omega

/-- An execution that is not well formed: replica `0` delivers the update issued at position `2`
by replica `1` before it issues the update at position `1`. -/
def backward : List (Event (Fin 2)) :=
  [⟨0, some 2⟩, ⟨0, none⟩, ⟨1, none⟩]

/-- The update issued at `2` directly precedes the update issued at `1`, but its issue does not
happen before the issue at `1` in Lamport's sense. -/
example : DirectlyBefore backward 2 1 ∧ ¬ HappensBefore backward 2 1 :=
  ⟨⟨_, _, rfl, rfl, rfl, rfl, 0, by decide, _, rfl, rfl, Or.inr rfl⟩,
    fun h => absurd h.lt (by decide)⟩

end Cslib.Distributed.Replication.CausalDeliveryTests
