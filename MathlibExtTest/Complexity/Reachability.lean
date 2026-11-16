/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.Reachability

@[expose] public section

/-- The start vertex is reachable in zero steps. -/
example : (0 : Fin 2) ∈ reachFrom (fun _ _ => true) 0 0 := by
  rw [reachFrom]
  exact Finset.mem_singleton_self 0

end
