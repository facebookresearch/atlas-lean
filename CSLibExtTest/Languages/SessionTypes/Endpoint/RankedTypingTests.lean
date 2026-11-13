/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RankedTransport

/-!
# Repeated same-key actions and physical-name priority transport
-/

namespace Cslib.SessionTypes.Endpoint.RankedTypingTests

open PiCalculus

def key : Key := ⟨.const 4, .positive⟩
def cap : Capability := ⟨5, .sendName (.sendName .done)⟩
def ownership : Context := Finmap.singleton key cap
def repeated : Proc := .out key.name (.const 7) (.out key.name (.const 8) .nil)

/-- Repeated actions on EXACTLY the same polarized key are legal at rank5;
the exemption does not apply to the opposite role of that physical name. -/
theorem repeated_ranked : RankedType 0 ownership repeated := by
  apply RankedType.outName (e := key) (c := cap) (s := .sendName .done)
  · exact guardMin_singleton _ _
  · exact Finmap.lookup_singleton_eq
  · rfl
  · trivial
  · trivial
  · rw [ownership, Finmap.insert_singleton_eq]
    apply RankedType.outName (e := key) (c := ⟨5, .sendName .done⟩) (s := .done)
    · exact guardMin_singleton _ _
    · exact Finmap.lookup_singleton_eq
    · rfl
    · trivial
    · trivial
    · rw [Finmap.insert_singleton_eq]
      exact RankedType.nil_of_hasType (HasType.nil_singleton trivial)

/-- Forgetting the refinement keeps the exact same base ownership typing. -/
theorem repeated_base_typed : HasType 0 ownership repeated := repeated_ranked.hasType

/-- General rekeying changes the physical name while retaining role/rank/protocol. -/
theorem repeated_renamed : RankedType 0
    (Context.rekey (Key.mapName (fun _ => .const 9)) ownership (by
      intro x hx y hy _
      have hx' := (Finmap.mem_singleton _ _ _).mp hx
      have hy' := (Finmap.mem_singleton _ _ _).mp hy
      exact hx'.trans hy'.symm))
    (mapProc (fun _ => .const 9) repeated) := by
  apply repeated_ranked.rename
  intro a ha
  trivial

/-- Entering a binder transports the entire repeated-action refinement. -/
theorem repeated_lifted : RankedType 1 (Context.lift 0 ownership) (liftProc 0 repeated) :=
  repeated_ranked.lift 0

end Cslib.SessionTypes.Endpoint.RankedTypingTests
