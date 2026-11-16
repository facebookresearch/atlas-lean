/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.Peterson

@[expose] public section

/-- The initial state is reachable and not critical. -/
example : PReachable ⟨fun _ => .idle, fun _ => false, 0⟩ :=
  Relation.ReflTransGen.refl

end
