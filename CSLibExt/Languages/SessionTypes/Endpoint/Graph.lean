/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Identity

/-!
# Guarded regular protocol graphs

Every successor is guarded by a communication. Bounded graph cursors exclude
undefined unfolding; there is no silent recursion-variable edge.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- **Node of a guarded protocol graph.**
A graph node: completion or a communication with a bounded continuation.
Endpoint payloads include their role, rank, cursor and protocol orientation. -/
inductive Node (size : Nat) where
  | done
  | sendName (next : Fin size)
  | recvName (next : Fin size)
  | sendEndpoint (role : Role) (rank : Nat) (payload : Fin size)
      (payloadReversed : Bool) (next : Fin size)
  | recvEndpoint (role : Role) (rank : Nat) (payload : Fin size)
      (payloadReversed : Bool) (next : Fin size)

/-- **Finite guarded regular protocol graph.**
Finite presentation of guarded equi-recursive protocols. An empty graph
has no cursor and therefore cannot denote a protocol. -/
structure Graph where
  size : Nat
  node : Fin size → Node size

end Cslib.SessionTypes.Endpoint
