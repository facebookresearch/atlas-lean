/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing

/-!
# Completed payload ownership is still required by delegation

This boundary does not refute completed weakening. It rules out erasing an
owned completed role without proving its actual absence from the syntax.
-/

namespace Cslib.SessionTypes.Endpoint.CompletedPayloadTests

open PiCalculus

def subject : Key := ⟨.const 0, .positive⟩
def payload : Key := ⟨.const 1, .positive⟩
def carrier : Capability := ⟨0, .sendEndpoint .positive 1 .done .done⟩
def ownership : Context := (Finmap.singleton subject carrier).insert payload ⟨1, .done⟩
def process : Proc := .out subject.name payload.name .nil

/-- A completed capability remains an actual owned endpoint payload. -/
theorem completed_payload_typed : HasType 0 ownership process := by
  apply HasType.outEndpoint (e := subject) (d := payload) (c := carrier)
    (k := 1) (t := .done) (s := .done)
  · change (Finmap.insert payload ⟨1, .done⟩
      (Finmap.singleton subject carrier) : Context).lookup subject = some carrier
    rw [Finmap.lookup_insert_of_ne _ (by decide : subject ≠ payload)]
    exact Finmap.lookup_singleton_eq
  · rfl
  · exact Finmap.lookup_insert _
  · decide
  · trivial
  · trivial
  · change HasType 0 (Finmap.singleton subject ⟨0, .done⟩) .nil
    exact HasType.nil_singleton trivial

/-- Erasing that completed payload breaks the same endpoint-sort output:
completion alone does not justify syntactic-resource strengthening. -/
theorem completed_payload_erasure_rejected :
    ¬ HasType 0 (ownership.erase payload) process := by
  change ¬ HasType 0 (Finmap.singleton subject carrier)
    (.out subject.name payload.name .nil)
  intro h
  obtain ⟨e, c, _, hc, hcase⟩ := h.out_inv
  have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
  subst e
  have hcc : c = carrier := Context.unique hc Finmap.lookup_singleton_eq
  subst c
  rcases hcase with ⟨s, hs, _⟩ | ⟨d, k, t, s, _, _, hd, hne, _⟩
  · change Protocol.sendEndpoint .positive 1 .done .done = .sendName s at hs
    cases hs
  · have hds := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hd)
    exact hne hds.symm

end Cslib.SessionTypes.Endpoint.CompletedPayloadTests
