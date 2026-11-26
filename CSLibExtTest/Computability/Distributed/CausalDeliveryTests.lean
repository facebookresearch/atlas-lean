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
  delivers `u` and then issues an update `v` (position `2`), so `u` happened before `v`; replica
  `2` delivers `u` and then `v`, and replica `0` delivers `v`. This execution provides causal
  delivery. Replica `0` never delivers `u`: it issued it.
* `bad`: replica `2` delivers `v` without having delivered `u`, and causal delivery fails.
* `conc`: replicas `0` and `1` issue concurrent updates, which replica `2` delivers in the
  opposite order to replica `0`. Causal delivery holds, as it does not order concurrent updates.
* The empty execution provides causal delivery.
* In `tr`, replica `1` delivers `u` before it issues `v`, so `u` precedes `v` directly, and
  `happensBefore_iff_transGen_delivered` relates this to happened-before.
* `relay`, over four replicas: a well-formed execution in which replica `2` receives from the
  delivery at position `1`. That receipt delivers nothing, but it makes the update issued at `0`
  happen before the update issued at `3`, although no chain of direct precedence joins them; so
  causal delivery fails when replica `3` delivers the update issued at `3`.
* `early`: a receipt that names a later issue is a delivery of that update but adds no step to
  happened-before; delivering an update before the earlier update of the same replica breaks
  causal delivery.
-/

@[expose] public section

namespace Cslib.Distributed.Replication.CausalDeliveryTests

open LamportClock

/-- An execution with causal delivery. -/
def tr : List (Event (Fin 3)) :=
  [⟨0, none⟩, ⟨1, some 0⟩, ⟨1, none⟩, ⟨2, some 0⟩, ⟨2, some 2⟩, ⟨0, some 2⟩]

/-- `u` happened before `v`: `u` is delivered at replica `1`, which then issues `v`. -/
theorem hb02 : HappensBefore tr 0 2 :=
  .tail (b := 1) (.single ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩)
    ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩

example : CausalDelivery tr := by
  intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  have hlt := hhb.lt
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
  have hb : HappensBefore bad 0 2 :=
    .tail (b := 1) (.single ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩)
      ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩
  obtain ⟨k, hk, ek, hek, hp, -⟩ := h 3 0 2 _ _ _ rfl rfl rfl rfl rfl rfl hb
  rcases k with _ | _ | _ | k
  · simp [bad] at hek; subst hek; simp at hp
  · simp [bad] at hek; subst hek; simp at hp
  · simp [bad] at hek; subst hek; simp at hp
  · omega

/-- Concurrent updates delivered in different orders. -/
def conc : List (Event (Fin 3)) :=
  [⟨0, none⟩, ⟨1, none⟩, ⟨2, some 1⟩, ⟨2, some 0⟩, ⟨0, some 1⟩, ⟨1, some 0⟩]

/-- The two updates of `conc` are concurrent. -/
theorem not_hb01 : ¬ HappensBefore conc 0 1 ∧ ¬ HappensBefore conc 1 0 := by
  refine ⟨fun h => ?_, fun h => absurd h.lt (by decide)⟩
  cases h with
  | single hs =>
      obtain ⟨-, ei, ej, hi, hj, hp | hr⟩ := hs <;> simp [conc] at hi hj <;> subst hi hj <;>
        simp at *
  | tail h hs => have := HappensBefore.lt (tr := conc) h; have := hs.1; omega

example : CausalDelivery conc := by
  intro j i₁ i₂ ej e₁ e₂ hj hr h₂ hn₂ h₁ hn₁ hhb
  have hlt := hhb.lt
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [conc] at hj <;> subst hj <;>
    simp at hr <;> subst hr
  all_goals first
    | omega
    | (obtain rfl : i₁ = 0 := by omega
       exact absurd hhb not_hb01.1)

example : CausalDelivery ([] : List (Event (Fin 3))) := by
  intro j _ _ _ _ _ hj
  simp at hj

/-! ## Happened-before between updates, by delivery -/

/-- An update `a` directly precedes an update `b` when the replica issuing `b` has issued or
delivered `a` before; this is the relation of `happensBefore_iff_transGen_delivered`. -/
def DirectlyBefore {R : Type*} (tr : List (Event R)) (a b : ℕ) : Prop :=
  ∃ ea eb : Event R, tr[a]? = some ea ∧ ea.recvFrom = none ∧ tr[b]? = some eb ∧
    eb.recvFrom = none ∧ ∃ k < b, ∃ ek : Event R, tr[k]? = some ek ∧ ek.proc = eb.proc ∧
      (k = a ∨ ek.recvFrom = some a)

theorem tr_wellFormed : WellFormed tr := by
  intro j ej i hj hr
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [tr] at hj <;> subst hj <;> simp at hr <;>
    omega

theorem tr_receipts : ∀ (j i : ℕ) (ej : Event (Fin 3)), tr[j]? = some ej →
    ej.recvFrom = some i → ∃ ei : Event (Fin 3), tr[i]? = some ei ∧ ei.recvFrom = none := by
  intro j i ej hj hr
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [tr] at hj <;> subst hj <;> simp at hr <;>
    subst hr <;> exact ⟨_, rfl, rfl⟩

/-- Replica `1` delivers `u` before it issues `v`, so `u` happened before `v`. -/
example : HappensBefore tr 0 2 :=
  (happensBefore_iff_transGen_delivered tr_wellFormed tr_receipts (i₁ := 0) (i₂ := 2) rfl rfl rfl
    rfl).mpr (.single ⟨_, _, rfl, rfl, rfl, rfl, 1, by decide, _, rfl, rfl, Or.inr rfl⟩)

example : Relation.TransGen (DirectlyBefore tr) 0 2 :=
  (happensBefore_iff_transGen_delivered tr_wellFormed tr_receipts rfl rfl rfl rfl).mp hb02

/-! ## Unusual executions -/

/-- A well-formed execution in which replica `2` receives from the delivery at position `1`, and
replica `3` delivers the update issued at position `3`. -/
def relay : List (Event (Fin 4)) :=
  [⟨0, none⟩, ⟨1, some 0⟩, ⟨2, some 1⟩, ⟨2, none⟩, ⟨3, some 3⟩]

example : WellFormed relay := by
  intro j ej i hj hr
  rcases j with _ | _ | _ | _ | _ | j <;> simp [relay] at hj <;> subst hj <;> simp at hr <;>
    omega

/-- The receipt from the delivery at position `1` makes the issue at `0` happen before the issue
at `3`. -/
theorem relay_hb03 : HappensBefore relay 0 3 :=
  .tail (b := 2) (.tail (b := 1) (.single ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩)
    ⟨by decide, _, _, rfl, rfl, Or.inr rfl⟩) ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩

/-- No chain of direct precedence leads from the update issued at `0` to the one issued at `3`:
replica `2` never delivers the update issued at `0`. -/
example : ¬ Relation.TransGen (DirectlyBefore relay) 0 3 := by
  have h3 : ∀ b, ¬ DirectlyBefore relay b 3 := by
    rintro b ⟨ea, eb, ha, hna, hb, -, k, hk, ek, hek, hp, hkb⟩
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
  intro h
  cases h with
  | single h => exact h3 0 h
  | tail _ h => exact h3 _ h

/-- Causal delivery fails: replica `3` delivers the update issued at `3` without having delivered
the update issued at `0`. -/
example : ¬ CausalDelivery relay := by
  intro h
  obtain ⟨k, hk, ek, hek, hp, -⟩ := h 4 0 3 _ _ _ rfl rfl rfl rfl rfl rfl relay_hb03
  rcases k with _ | _ | _ | _ | k
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · simp [relay] at hek; subst hek; simp at hp
  · omega

/-- An execution that is not well formed: replica `1` delivers the update issued at position `2`
before it is issued, and replica `0` issues updates at positions `1` and `2`. -/
def early : List (Event (Fin 2)) :=
  [⟨1, some 2⟩, ⟨0, none⟩, ⟨0, none⟩]

example : ¬ WellFormed early := fun h => absurd (h 0 _ 2 rfl rfl) (by decide)

/-- The receipt at position `0` adds no step to happened-before. -/
example : ¬ HappensBefore early 2 0 := fun h => absurd h.lt (by decide)

/-- It is still a delivery: the update issued at `1` happened before the one issued at `2`, and
replica `1` has delivered nothing before position `0`. -/
example : ¬ CausalDelivery early := by
  intro h
  obtain ⟨k, hk, -⟩ := h 0 1 2 _ _ _ rfl rfl rfl rfl rfl rfl
    (.single ⟨by decide, _, _, rfl, rfl, Or.inl rfl⟩)
  omega

end Cslib.Distributed.Replication.CausalDeliveryTests
