/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing
import CSLibExt.Languages.SessionTypes.Endpoint.Balance
import CSLibExt.Languages.SessionTypes.Endpoint.Priority
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant

/-!
# Delegating the peer role over one physical channel

Bare ownership may hold both roles. Its priority discipline must reject the
peer role as a distinct dependency even when the physical name coincides.
-/

namespace Cslib.SessionTypes.Endpoint.PeerDelegationTests

open PiCalculus

/-- The first state sends the peer capability; the second state has completed. -/
def graph : Graph := ⟨2, fun i => if i.val = 0 then
  .sendEndpoint .negative 0 ⟨0, by decide⟩ true ⟨1, by decide⟩ else .done⟩

/-- Positive carrier protocol, with its actual dual as the negative payload. -/
def carrier : Capability := ⟨0, .regular graph ⟨0, by decide⟩ false⟩

/-- A single physical-name output, whose two typing roles are distinct. -/
def process : Proc := .out (.var 0) (.var 0) .nil

/-- The graph really advertises its dual cursor as the peer endpoint payload. -/
theorem carrier_head : carrier.protocol.unfold =
    .sendEndpoint .negative 0 carrier.dual.protocol
      (.regular graph ⟨1, by decide⟩ false) := rfl

/-- Bare linear ownership permits delegating the actual peer role over
its carrier: same name, different keys, exact recursively advertised payload. -/
theorem process_typed : HasType 1 (Context.bind carrier ∅) process := by
  apply HasType.outEndpoint (e := ⟨.var 0, .positive⟩) (d := ⟨.var 0, .negative⟩)
    (c := carrier) (k := 0) (t := carrier.dual.protocol)
    (s := .regular graph ⟨1, by decide⟩ false)
  · exact Context.lookup_bind_positive carrier ∅
  · exact carrier_head
  · simpa [carrier, Capability.dual] using Context.lookup_bind_negative carrier ∅
  · decide
  · change 0 < 1
    decide
  · change 0 < 1
    decide
  · change HasType 1 (Finmap.singleton (⟨.var 0, .positive⟩ : Key)
      ⟨0, .regular graph ⟨1, by decide⟩ false⟩) .nil
    apply HasType.nil_singleton_completed
    · change 0 < 1
      decide
    · rfl

/-- The outer restriction supplies the two exact polarized capabilities. -/
theorem network_typed : HasType 0 ∅ (.nu process) :=
  HasType.nu (c := carrier) process_typed

/-- The active peer role has equal rank and is not the same-key exemption. -/
theorem peer_delegation_priority_rejected :
    ¬ GuardMin (Context.bind carrier ∅) (⟨.var 0, .positive⟩ : Key) 0 := by
  apply guardMin_rejects_peer (c := carrier.dual)
  · exact Context.lookup_bind_negative carrier ∅
  · change Protocol.recvEndpoint .negative 0 carrier.dual.protocol
      (.regular graph ⟨1, by decide⟩ true) ≠ .done
    intro h
    cases h

/-- There is no peer input anywhere in the closed process, and all
existing Step constructors (including Cong) require such a source guard. -/
theorem peer_delegation_stuck : ¬ ∃ q, Step (.nu process) q := by
  rintro ⟨q, hq⟩
  exact Cslib.SessionTypes.Endpoint.Step.source_hasUnguardedInput hq

end Cslib.SessionTypes.Endpoint.PeerDelegationTests
