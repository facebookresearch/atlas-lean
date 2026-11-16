/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.TestAndSetConsensus

@[expose] public section

/-- The initial state is reachable. -/
example : CReachable (fun i : Fin 2 => i)
    (⟨fun _ => .writeReg, fun _ => none, false, none, fun _ => none⟩ : CState (Fin 2)) :=
  Relation.ReflTransGen.refl

end
