/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.LubyMIS

@[expose] public section

/-- With no active vertices, nothing is selected. -/
example (prio : Fin 2 → ℕ) (adj : Fin 2 → Finset (Fin 2)) :
    lubySelect prio adj ∅ = ∅ := by
  simp [lubySelect]

end
