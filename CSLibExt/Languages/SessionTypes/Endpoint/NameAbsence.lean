/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Physical-name absence from all existing π process positions

This is syntactic occurrence information, including transmitted payloads and
binder-adjusted continuation names. It is not another scope predicate or a
stored transition, congruence, preservation or progress assumption.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Absence of a physical name from a process.**
The given physical name occurs in no subject, payload or continuation
position. Existing binders shift the tracked outer name with canonical lift. -/
def NameAbsent (a : Name) : Proc → Prop
  | .nil => True
  | .out b c p => a ≠ b ∧ a ≠ c ∧ NameAbsent a p
  | .inp b p => a ≠ b ∧ NameAbsent (liftName 0 a) p
  | .par p q | .sum p q => NameAbsent a p ∧ NameAbsent a q
  | .nu p => NameAbsent (liftName 0 a) p
  | .repl p => NameAbsent a p

/-- **An output payload name is not absent.**
A transmitted endpoint payload is an occurrence, even when completed. -/
theorem NameAbsent.out_payload {a b : Name} {p : Proc} :
    ¬ NameAbsent a (.out b a p) := by
  intro h
  exact h.2.1 rfl

private theorem inserted_name_ne_lift (k : Nat) (a : Name) :
    Name.var k ≠ liftName k a := by
  cases a with
  | const => intro h; cases h
  | var i =>
    by_cases hki : k ≤ i
    · simp only [liftName, hki, ↓reduceIte]
      intro h
      have hi := Name.var.inj h
      omega
    · simp only [liftName, hki, ↓reduceIte]
      intro h
      have hi := Name.var.inj h
      omega

/-- **The inserted name is absent from a lifted process.**
The inserted name is absent from every position of the actual lifted
π term, including payloads and all nested input/restriction binders. -/
theorem nameAbsent_fresh_lift (k : Nat) (p : Proc) :
    NameAbsent (.var k) (liftProc k p) := by
  induction p generalizing k with
  | nil => trivial
  | out a b p ih => exact ⟨inserted_name_ne_lift k a, inserted_name_ne_lift k b, ih k⟩
  | inp a p ih =>
    refine ⟨inserted_name_ne_lift k a, ?_⟩
    simpa only [liftName, Nat.zero_le, ↓reduceIte] using ih (k + 1)
  | par p q ihp ihq => exact ⟨ihp k, ihq k⟩
  | nu p ih =>
    change NameAbsent (liftName 0 (.var k)) (liftProc (k + 1) p)
    simpa only [liftName, Nat.zero_le, ↓reduceIte] using ih (k + 1)
  | repl p ih => exact ih k
  | sum p q ihp ihq => exact ⟨ihp k, ihq k⟩

end Cslib.SessionTypes.Endpoint
