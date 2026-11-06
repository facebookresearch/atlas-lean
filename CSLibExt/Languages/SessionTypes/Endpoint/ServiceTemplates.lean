/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.SharedEnvironment
public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Structural input-guarded shared service templates

The predicate reads actual syntax and declared constant names. Input stops
at its guard; separate typing checks its received-parameter body. No typing,
Cong, Step, readiness or future trace is a definition field.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Structural shared-service template.**
A template is a structural tree of declared shared inputs, never active outputs. -/
def ServiceTemplate (Γ : ServiceEnv) : Proc → Prop
  | .nil => True
  | .inp a _ => ∃ s, a = .const s ∧ s ∈ Γ
  | .par p q => ServiceTemplate Γ p ∧ ServiceTemplate Γ q
  | .nu p | .repl p => ServiceTemplate Γ p
  | .out .. | .sum .. => False

private theorem declared_lift (Γ : ServiceEnv) (k : Nat) (a : Name) :
    (∃ s, liftName k a = .const s ∧ s ∈ Γ) ↔ ∃ s, a = .const s ∧ s ∈ Γ := by
  constructor
  · rintro ⟨s, he, hs⟩
    exact ⟨s, liftName_injective k he, hs⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨s, rfl, hs⟩

private theorem declared_swap (Γ : ServiceEnv) (k : Nat) (a : Name) :
    (∃ s, swapNameAt k a = .const s ∧ s ∈ Γ) ↔ ∃ s, a = .const s ∧ s ∈ Γ := by
  constructor
  · rintro ⟨s, he, hs⟩
    exact ⟨s, swapNameAt_injective k he, hs⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨s, rfl, hs⟩

/-- **Service templates are invariant under lifting.**
Canonical lifting preserves literal shared constants through every structural wrapper. -/
theorem ServiceTemplate.lift_iff (Γ : ServiceEnv) (k : Nat) (p : Proc) :
    ServiceTemplate Γ (liftProc k p) ↔ ServiceTemplate Γ p := by
  induction p generalizing k <;> simp_all [ServiceTemplate, liftProc, declared_lift]

/-- **Service templates are invariant under binder swapping.**
Canonical swap preserves template guards, including wrappers under nested binders. -/
theorem ServiceTemplate.swap_iff (Γ : ServiceEnv) (k : Nat) (p : Proc) :
    ServiceTemplate Γ (swapProc k p) ↔ ServiceTemplate Γ p := by
  induction p generalizing k <;> simp_all [ServiceTemplate, swapProc, declared_swap]

/-- **Service templates are invariant under structural congruence.**
ALL16 canonical Cong constructors preserve structural guarded templates in BOTH directions. -/
theorem ServiceTemplate.cong_iff {Γ : ServiceEnv} {p q : Proc} (h : Cong p q) :
    ServiceTemplate Γ p ↔ ServiceTemplate Γ q := by
  induction h <;> simp_all [ServiceTemplate, ServiceTemplate.lift_iff,
    ServiceTemplate.swap_iff, and_assoc, and_comm]

/-- **Unguarded shared input on a given name.**
Actual unguarded shared input presence through structural wrappers; input stops here. -/
def AcceptIn (s : Nat) : Proc → Prop
  | .inp a _ => a = .const s
  | .par p q => AcceptIn s p ∨ AcceptIn s q
  | .nu p | .repl p => AcceptIn s p
  | .nil | .out .. | .sum .. => False

private theorem accept_lift (s k : Nat) (p : Proc) :
    AcceptIn s (liftProc k p) ↔ AcceptIn s p := by
  induction p generalizing k <;> simp_all only [AcceptIn, liftProc]
  constructor
  · exact fun h => liftName_injective k h
  · intro h
    rw [h]
    rfl

private theorem accept_swap (s k : Nat) (p : Proc) :
    AcceptIn s (swapProc k p) ↔ AcceptIn s p := by
  induction p generalizing k <;> simp_all only [AcceptIn, swapProc]
  constructor
  · exact fun h => swapNameAt_injective k h
  · intro h
    rw [h]
    rfl

/-- **Structural congruence preserves unguarded shared inputs.**
All canonical congruences preserve actual shared-input presence, not execution. -/
theorem accept_cong {s : Nat} {p q : Proc} (h : Cong p q) :
    AcceptIn s p ↔ AcceptIn s q := by
  induction h <;> simp_all [AcceptIn, accept_lift, accept_swap, or_assoc, or_comm]

/-- **Persistent service offer on a given name.**
Persistent services expose input leaves within actual replicated structural templates. -/
def OfferedIn (s : Nat) : Proc → Prop
  | .repl p => AcceptIn s p
  | .par p q => OfferedIn s p ∨ OfferedIn s q
  | .nu p => OfferedIn s p
  | .nil | .inp .. | .out .. | .sum .. => False

/-- **Offered services have an unguarded shared input.**
Every persistent offered service has an actual unguarded input leaf. -/
theorem offered_accept {s : Nat} {p : Proc} (h : OfferedIn s p) : AcceptIn s p := by
  induction p <;> simp_all only [OfferedIn, AcceptIn]
  case par p q ihp ihq => exact h.elim (fun hp => Or.inl (ihp hp)) (fun hq => Or.inr (ihq hq))

private theorem offered_lift (s k : Nat) (p : Proc) :
    OfferedIn s (liftProc k p) ↔ OfferedIn s p := by
  induction p generalizing k <;> simp_all [OfferedIn, liftProc, accept_lift]

private theorem offered_swap (s k : Nat) (p : Proc) :
    OfferedIn s (swapProc k p) ↔ OfferedIn s p := by
  induction p generalizing k <;> simp_all [OfferedIn, swapProc, accept_swap]

/-- **Structural congruence preserves persistent service offers.**
ALL16 actual Cong rules preserve persistent service offering, including wrappers
inside replication and actual replica unfolding. No closure constructor is used. -/
theorem offered_cong {s : Nat} {p q : Proc} (h : Cong p q) :
    OfferedIn s p ↔ OfferedIn s q := by
  induction h <;> simp_all only [OfferedIn, offered_lift, offered_swap,
    or_assoc, or_comm, false_or]
  case repl_cong h ih => exact accept_cong h
  case repl_unfold p =>
    constructor
    · exact Or.inl
    · exact fun h => h.elim id offered_accept

/-- **Declared persistent service offer.**
Declared signature plus actual persistent guarded service syntax, never execution data. -/
def Offered (Γ : ServiceEnv) (p : Proc) (s : Nat) (sig : ServiceSignature) : Prop :=
  Γ.lookup s = some sig ∧ OfferedIn s p

/-- **Idle process as a structural service template.**
Quiescent structural service templates include waiting declared inputs and wrappers. -/
def Idle (Γ : ServiceEnv) (p : Proc) : Prop := ServiceTemplate Γ p

/-- **Declared service offers are invariant under congruence.**
All canonical Cong constructors preserve each actual declared persistent offer. -/
theorem Offered.cong_iff {Γ : ServiceEnv} {p q : Proc} {s : Nat} {sig : ServiceSignature}
    (h : Cong p q) : Offered Γ p s sig ↔ Offered Γ q s sig :=
  and_congr Iff.rfl (offered_cong h)

/-- **Idleness is invariant under structural congruence.**
Idle is precisely structural guarded-template quiescence and is Cong-invariant. -/
theorem Idle.cong_iff {Γ : ServiceEnv} {p q : Proc} (h : Cong p q) :
    Idle Γ p ↔ Idle Γ q := ServiceTemplate.cong_iff h

end Cslib.SessionTypes.Endpoint.Runtime
