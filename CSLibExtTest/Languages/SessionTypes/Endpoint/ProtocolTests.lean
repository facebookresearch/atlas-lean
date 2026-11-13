/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Protocol
import CSLibExt.Languages.SessionTypes.Endpoint.FiniteBridge

/-!
# Non-vacuous guarded recursive protocol consumers

These are protocol examples, not a proof of recursive process execution.
-/

namespace Cslib.SessionTypes.Endpoint.ProtocolTests

/-- A single graph state repeatedly sends passive data; every edge is guarded. -/
def sendingGraph : Graph := ⟨1, fun _ => .sendName ⟨0, by decide⟩⟩

/-- The recurring sender cursor. -/
def sendingLoop : Protocol := .regular sendingGraph ⟨0, by decide⟩ false

/-- Unfolding exposes a real guard and its recurring continuation. -/
theorem sendingLoop_unfold :
    sendingLoop.unfold = .sendName sendingLoop := rfl

/-- The dual cursor repeatedly receives, with the dual recurring tail. -/
theorem receivingLoop_unfold :
    sendingLoop.dual.unfold = .recvName sendingLoop.dual := rfl

/-- A guarded graph can carry a genuinely recursive endpoint payload. -/
def delegatingGraph : Graph :=
  ⟨1, fun _ => .sendEndpoint .negative 17 ⟨0, by decide⟩ false ⟨0, by decide⟩⟩

/-- Subject and payload share a graph cursor but have independent orientation. -/
def delegatingLoop : Protocol := .regular delegatingGraph ⟨0, by decide⟩ false

/-- Duality reverses the subject but does not reverse the delegated capability. -/
theorem delegated_payload_dual : delegatingLoop.dual.unfold =
    .recvEndpoint .negative 17 delegatingLoop delegatingLoop.dual := rfl

/-- Recursive protocols are not silently reported as finite passive ones. -/
theorem recursive_not_finite : sendingLoop.toFinite? = none := rfl

/-- Endpoint-value payloads are not silently decoded as finite passive data. -/
theorem endpoint_payload_not_passive :
    (Protocol.sendEndpoint .positive 1 (.sendName .done) .done).toFinite? = none := rfl

end Cslib.SessionTypes.Endpoint.ProtocolTests
