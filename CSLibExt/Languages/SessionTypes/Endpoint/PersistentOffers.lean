/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ServiceTemplates

/-!
# Persistent guarded service offers survive actual canonical reduction

Syntax only: no typing, future trace, readiness or reduction-closure field.
Once-only AcceptIn is deliberately not claimed to be a persistent invariant.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Selection preserves persistent offers.**
Choice selection cannot discard a persistent SOURCE offer: sums do not expose
OfferedIn, and selecting an actual communicating guard exposes no persistent offer. -/
theorem offered_select {s : Nat} {p q : Proc} (h : Select p q) :
    OfferedIn s p → OfferedIn s q := by
  induction h with
  | refl => exact id
  | left => exact False.elim
  | right => exact False.elim
  | trans hp hq ihp ihq => exact fun h => ihq (ihp h)

/-- **Persistent service offers survive one reduction step.**
ALL5 canonical Step rules retain every actual persistent source service offer.
This is valid for arbitrary Pi syntax, WITHOUT a HasType premise. -/
theorem offered_step {s : Nat} {p q : Proc} (h : PiCalculus.Step p q) :
    OfferedIn s p → OfferedIn s q := by
  induction h with
  | commSelect hp hq =>
    intro ho
    rcases ho with ho | ho
    · exact False.elim (offered_select hp ho)
    · exact False.elim (offered_select hq ho)
  | parL hs ih => exact fun h => h.elim (fun ho => Or.inl (ih ho)) Or.inr
  | parR hs ih => exact fun h => h.elim Or.inl (fun ho => Or.inr (ih ho))
  | nu hs ih => exact ih
  | cong hp hs hq ih => exact fun h => (offered_cong hq).mp (ih ((offered_cong hp).mp h))

/-- **Declared signature offers survive one reduction step.**
Exact declared signature lookup plus an actual persistent offer is retained
by every canonical Step, at unchanged shared environment/signature. -/
theorem Offered.step {Γ : ServiceEnv} {s : Nat} {sig : ServiceSignature} {p q : Proc}
    (h : Offered Γ p s sig) (hs : PiCalculus.Step p q) : Offered Γ q s sig :=
  ⟨h.1, offered_step hs h.2⟩

/-- **Declared signature offers survive finite reduction.**
Every finite actual reduction preserves each SOURCE persistent signature offer.
No liveness, all-schedules fairness or eventual service invocation is asserted. -/
theorem Offered.reachable {Γ : ServiceEnv} {s : Nat} {sig : ServiceSignature} {p q : Proc}
    (h : Offered Γ p s sig) (hr : Relation.ReflTransGen PiCalculus.Step p q) :
    Offered Γ q s sig := by
  induction hr with
  | refl => exact h
  | tail hr hs ih => exact ih.step hs

/-- **Availability of all declared services.**
Every declared shared signature has an ACTUAL persistent offer in current syntax.
There is NO typing, Step, future trace, ready pair or step-closure field. -/
def Available (Γ : ServiceEnv) (p : Proc) : Prop :=
  ∀ s sig, Γ.lookup s = some sig → OfferedIn s p

/-- **Availability as offers of all declared signatures.**
Availability is exactly current declared signature lookup plus persistent syntax. -/
theorem available_iff_offered {Γ : ServiceEnv} {p : Proc} :
    Available Γ p ↔ ∀ s sig, Γ.lookup s = some sig → Offered Γ p s sig :=
  ⟨fun h s sig hs => ⟨hs, h s sig hs⟩, fun h s sig hs => (h s sig hs).2⟩

/-- **Structural congruence preserves service availability.**
All canonical structural laws preserve current syntactic availability. -/
theorem Available.cong_iff {Γ : ServiceEnv} {p q : Proc} (h : Cong p q) :
    Available Γ p ↔ Available Γ q :=
  ⟨fun hp s sig hs => (offered_cong h).mp (hp s sig hs),
    fun hq s sig hs => (offered_cong h).mpr (hq s sig hs)⟩

/-- **Service availability survives one reduction step.**
Strong actual syntactic availability survives ANY canonical Step. -/
theorem Available.step {Γ : ServiceEnv} {p q : Proc} (h : Available Γ p)
    (hs : PiCalculus.Step p q) : Available Γ q :=
  fun s sig hsig => offered_step hs (h s sig hsig)

/-- **Service availability survives finite reduction.**
Finite actual reductions preserve source syntactic availability; preservation
is PROVED here, not encoded into its definition. This is not a progress theorem. -/
theorem Available.reachable {Γ : ServiceEnv} {p q : Proc} (h : Available Γ p)
    (hr : Relation.ReflTransGen PiCalculus.Step p q) : Available Γ q := by
  induction hr with
  | refl => exact h
  | tail hr hs ih => exact ih.step hs

end Cslib.SessionTypes.Endpoint.Runtime
