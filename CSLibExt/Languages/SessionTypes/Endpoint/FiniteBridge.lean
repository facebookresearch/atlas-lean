/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Protocol
public import CSLibExt.Languages.SessionTypes.Basic

/-!
# Lossless finite passive-protocol bridge

The existing finite protocol remains unchanged. Endpoint and recursive
payloads are additional cases, never silently treated as passive names.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- Embed the original finite passive-name protocol without changing actions. -/
def Protocol.ofFinite : SessionType → Protocol
  | .end => .done
  | .send s => .sendName (ofFinite s)
  | .recv s => .recvName (ofFinite s)

/-- The finite embedding preserves both protocol orientations. -/
theorem Protocol.ofFinite_dual (s : SessionType) :
    ofFinite s.dual = (ofFinite s).dual := by
  induction s <;> simp [ofFinite, SessionType.dual, dual, *]

/-- Recover a finite passive protocol; richer payloads and recursion are
not erased into a falsely finite protocol. -/
def Protocol.toFinite? : Protocol → Option SessionType
  | .done => some .end
  | .sendName s => s.toFinite?.map SessionType.send
  | .recvName s => s.toFinite?.map SessionType.recv
  | .sendEndpoint .. | .recvEndpoint .. | .regular .. => none

/-- The finite embedding has a literal left inverse. -/
@[simp] theorem Protocol.toFinite?_ofFinite (s : SessionType) :
    (ofFinite s).toFinite? = some s := by
  induction s <;> simp [ofFinite, toFinite?, *]

/-- Different finite protocols remain different in the richer representation. -/
theorem Protocol.ofFinite_injective : Function.Injective ofFinite := by
  intro s t h
  have hs := congrArg toFinite? h
  simpa only [toFinite?_ofFinite, Option.some.injEq] using hs

end Cslib.SessionTypes.Endpoint
