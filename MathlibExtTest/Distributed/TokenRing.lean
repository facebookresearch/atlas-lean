/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.TokenRing

@[expose] public section

/-- Boundary check: the constant-zero configuration on a
2-machine ring has a privileged machine (machine 0). -/
example : ∃ i, privileged ((fun _ => (0 : ZMod 3)) : ZMod 2 → ZMod 3) i :=
  exists_privileged ((fun _ => (0 : ZMod 3)) : ZMod 2 → ZMod 3)
