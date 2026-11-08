/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Strengthening
import CSLibExt.Languages.SessionTypes.Endpoint.EndWeakening
import CSLibExtTest.Languages.SessionTypes.Endpoint.CompletedPayloadTests

/-!
# All-position absence strengthening and its completed-payload boundary
-/

namespace Cslib.SessionTypes.Endpoint.StrengtheningTests

open PiCalculus

def subject : Key := ⟨.const 0, .positive⟩
def unused : Key := ⟨.const 3, .negative⟩
def base : Context := Finmap.singleton subject ⟨0, .recvName .done⟩
def ownership : Context := base.insert unused ⟨7, .done⟩
def process : Proc := .inp subject.name .nil

/-- A real input binder is typed with a nonempty subject context. -/
theorem base_typed : HasType 0 base process := by
  apply HasType.inpName (e := subject) (c := ⟨0, .recvName .done⟩) (s := .done)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · change HasType 1 (Finmap.singleton subject ⟨0, .done⟩) .nil
    exact HasType.nil_singleton trivial

/-- Completed weakening supplies a populated unused role beside that input. -/
theorem ownership_typed : HasType 0 ownership process := by
  apply base_typed.weaken_completed
  · simp [base, subject, unused, Finmap.mem_singleton]
  · rfl
  · trivial

/-- The tracked name is absent both at the input subject and under its binder. -/
theorem unused_absent : NameAbsent unused.name process := by
  exact ⟨by decide, trivial⟩

/-- The general theorem erases precisely that unused role from the typed input. -/
theorem unused_erased_typed : HasType 0 (ownership.erase unused) process :=
  ownership_typed.erase_nameAbsent unused_absent

/-- The same literal completed-payload fixture as CompletedPayloadTests
fails the absence premise, independently of its private Lean declarations. -/
theorem used_completed_payload_not_absent :
    ¬ NameAbsent (.const 1) (.out (.const 0) (.const 1) .nil) :=
  NameAbsent.out_payload

/-- The GENERAL completion lemma sees the owned unused role in the
populated input context, rather than merely checking an empty nil fixture. -/
theorem owned_unused_completed :
    (⟨7, .done⟩ : Capability).protocol.unfold = .done := by
  exact ownership_typed.absent_lookup_completed
    (Finmap.lookup_insert _) unused_absent

/-- An active role cannot remain owned and absent throughout this input;
the completion conclusion would conflict with its declared send head. -/
theorem active_absent_role_typing_rejected :
    ¬ HasType 0 (base.insert unused ⟨7, .sendName .done⟩) process := by
  intro h
  have hc : Protocol.sendName .done = .done :=
    h.absent_lookup_completed (Finmap.lookup_insert _) unused_absent
  cases hc

end Cslib.SessionTypes.Endpoint.StrengtheningTests
