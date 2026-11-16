/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.FoolingSet

@[expose] public section

/-- The empty set is a fooling set for any `f`. -/
example (f : Fin 2 × Fin 2 → Bool) : IsFooling f ∅ := by
  constructor
  · intro p hp
    simp at hp
  · intro p hp
    simp at hp

end
