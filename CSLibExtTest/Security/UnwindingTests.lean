/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Security.Unwinding

/-!
# Tests for the unwinding theorem

A two-register machine with a low and a high domain, where the low domain may interfere with the
high one but not conversely (the policy `≤` on `Bool`, with `false` low and `true` high). Writing
the low register into the high one is secure, which the unwinding theorem proves; writing the high
register into the low one is not, which shows that `Secure` is not vacuous.
-/

namespace Cslib.Security.DomainMachine.Tests

/-- Actions on a pair of registers (low, high). -/
inductive Act
  | writeLow (n : ℕ)
  | writeHigh (n : ℕ)
  | readLow
  | readHigh
  | copy
  deriving DecidableEq

open Act

/-- The domain of an action: `copy` belongs to the domain `copyDom`. -/
def dom (copyDom : Bool) : Act → Bool
  | writeLow _ => false
  | writeHigh _ => true
  | readLow => false
  | readHigh => true
  | copy => copyDom

/-- The register machine; `up` says whether `copy` writes the low register into the high one
(`true`) or the high register into the low one (`false`). -/
def machine (up copyDom : Bool) : DomainMachine (ℕ × ℕ) Act ℕ Bool where
  start := (0, 0)
  tr s
    | writeLow n => (n, s.2)
    | writeHigh n => (s.1, n)
    | readLow => s
    | readHigh => s
    | copy => if up then (s.1, s.1) else (s.2, s.2)
  output s
    | readLow => s.1
    | readHigh => s.2
    | _ => 0
  dom := dom copyDom

/-- The low domain sees the low register, the high domain sees both. -/
def view : Bool → Setoid (ℕ × ℕ)
  | false => Setoid.ker Prod.fst
  | true => Setoid.ker id

@[simp]
theorem view_apply (u : Bool) (s t : ℕ × ℕ) : view u s t ↔ if u then s = t else s.1 = t.1 := by
  cases u <;> exact Iff.rfl

/-- The secure machine: `copy` is a low action writing the low register into the high one. -/
abbrev secureMachine : DomainMachine (ℕ × ℕ) Act ℕ Bool := machine true false

/-- The leaky machine: `copy` is a high action writing the high register into the low one. -/
abbrev leakyMachine : DomainMachine (ℕ × ℕ) Act ℕ Bool := machine false true

/-! ### Purge -/

/-- Purging for the low domain keeps only the low actions. -/
example :
    secureMachine.purge (· ≤ ·) [writeHigh 3, writeLow 1, readHigh, copy, readLow] false =
      [writeLow 1, copy, readLow] := by
  decide

/-- Purging for the high domain keeps every action. -/
example :
    secureMachine.purge (· ≤ ·) [writeHigh 3, writeLow 1, readHigh, copy] true =
      [writeHigh 3, writeLow 1, readHigh, copy] := by
  decide

/-- The empty sequence purges to itself. -/
example (u : Bool) : secureMachine.purge (· ≤ ·) [] u = [] :=
  purge_nil _ u

/-- For the policy relating all domains, purging changes nothing, so every machine is secure. -/
example {S A O D : Type*} (M : DomainMachine S A O D) : M.Secure fun _ _ => True := by
  intro α a
  simp [purge]

/-! ### The secure machine, by unwinding -/

theorem secureMachine_outputConsistent : secureMachine.OutputConsistent view := by
  rintro (_ | _ | _ | _ | _) ⟨l, h⟩ ⟨l', h'⟩ hst <;> simp_all [machine, dom]

theorem secureMachine_stepConsistent : secureMachine.StepConsistent view := by
  rintro (_ | _) (_ | _ | _ | _ | _) ⟨l, h⟩ ⟨l', h'⟩ hst <;> simp_all [machine]

theorem secureMachine_locallyRespects : secureMachine.LocallyRespects (· ≤ ·) view := by
  rintro (_ | _) (_ | _ | _ | _ | _) ⟨l, h⟩ hdom <;> simp_all [machine, dom]

theorem secureMachine_secure : secureMachine.Secure (· ≤ ·) :=
  unwinding secureMachine_outputConsistent secureMachine_stepConsistent
    secureMachine_locallyRespects

/-- An instance of security: a low read after `[writeLow 2, writeHigh 5, copy]` gives the same
output as after its purge for the low domain, `[writeLow 2, copy]`. -/
example :
    secureMachine.output (secureMachine.mtr secureMachine.start [writeLow 2, writeHigh 5, copy])
        readLow =
      secureMachine.output (secureMachine.mtr secureMachine.start [writeLow 2, copy]) readLow :=
  secureMachine_secure [writeLow 2, writeHigh 5, copy] readLow

/-- The key lemma from states that are equivalent for the low domain but not equal. -/
example :
    view false (secureMachine.mtr (1, 7) [writeHigh 3, copy])
      (secureMachine.mtr (1, 9) (secureMachine.purge (· ≤ ·) [writeHigh 3, copy] false)) :=
  view_mtr_purge secureMachine_stepConsistent secureMachine_locallyRespects
    (by simp) _

/-! ### The leaky machine -/

/-- Copying the high register into the low one is not secure: after a high write and the copy,
a low read sees the high value, while after the purged (empty) sequence it sees `0`. -/
theorem leakyMachine_not_secure : ¬leakyMachine.Secure (· ≤ ·) := by
  intro h
  have := h [writeHigh 1, copy] readLow
  revert this
  decide

/-- Hence the leaky machine fails one of the unwinding conditions for every family of views. -/
example (view : Bool → Setoid (ℕ × ℕ)) :
    ¬(leakyMachine.OutputConsistent view ∧ leakyMachine.StepConsistent view ∧
      leakyMachine.LocallyRespects (· ≤ ·) view) :=
  fun ⟨hout, hstep, hloc⟩ => leakyMachine_not_secure (unwinding hout hstep hloc)

/-! ### A policy that is not reflexive -/

/-- For the empty policy, which is not reflexive, purging deletes every action, so security says
that every output after a run from the initial state is the output in the initial state. -/
example {S A O D : Type*} (M : DomainMachine S A O D) :
    M.Secure (fun _ _ => False) ↔ ∀ α a, M.output (M.mtr M.start α) a = M.output M.start a := by
  simp [Secure, purge]

/-- The register machine with outputs that ignore the state. -/
abbrev constantMachine : DomainMachine (ℕ × ℕ) Act ℕ Bool :=
  { secureMachine with output := fun _ _ => 0 }

/-- The unwinding theorem for the empty policy: with views that relate all states, the machine
whose outputs ignore the state is secure. -/
example : constantMachine.Secure fun _ _ => False :=
  unwinding (view := fun _ => Setoid.ker fun _ => ()) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    fun _ _ _ _ => rfl

/-- The secure machine is not secure for the empty policy: a low read after a low write sees the
written value, not the initial one. -/
example : ¬secureMachine.Secure fun _ _ => False := by
  intro h
  have := h [writeLow 1] readLow
  revert this
  decide

end Cslib.Security.DomainMachine.Tests
