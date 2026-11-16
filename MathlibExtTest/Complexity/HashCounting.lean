/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.HashCounting

@[expose] public section

/-- For the singleton zero set in one coordinate, the doubled count is 4. -/
example : (2 * ∑ a : Fin 1 → ZMod 2,
    (({(0 : Fin 1 → ZMod 2)} : Finset (Fin 1 → ZMod 2)).filter
      (fun x => dotF2 a x = 0)).card) = 4 := by
  classical
  have h := hash_count_identity ({(0 : Fin 1 → ZMod 2)} : Finset (Fin 1 → ZMod 2))
  simpa using h

end
