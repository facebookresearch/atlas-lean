/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Relation.FiniteReachability

/-!
# Tests for finite reachability

Reachability along the successor relation on `Fin 4` (no wrap-around), decided by the kernel
through `Relation.transGenFin`, and transported to `Relation.TransGen` and `ReflTransGen`.
-/

@[expose] public section

namespace Relation.FiniteReachabilityTests

/-- The successor relation on `Fin 4`, without wrap-around. -/
def chain (i j : Fin 4) : Prop := j.val = i.val + 1

instance : DecidableRel chain := fun i j => inferInstanceAs (Decidable (j.val = i.val + 1))

example : (3 : Fin 4) ∈ transGenFin chain 0 := by decide

example : (0 : Fin 4) ∉ transGenFin chain 0 := by decide

example : (3 : Fin 4) ∈ transGenFinFrom chain {0, 2} := by decide

example : (0 : Fin 4) ∉ transGenFinFrom chain {1, 2} := by decide

example : TransGen chain 0 3 := mem_transGenFin.mp (by decide)

example : ¬ TransGen chain 2 1 := fun h => absurd (mem_transGenFin.mpr h) (by decide)

example : @decide (ReflTransGen chain 2 2) (decidableReflTransGen chain 2 2) = true := by
  decide +kernel

example : @decide (ReflTransGen chain 3 0) (decidableReflTransGen chain 3 0) = false := by
  decide +kernel

end Relation.FiniteReachabilityTests
