/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.HashCounting
import Mathlib.Data.Fin.VecNotation

@[expose] public section

open MathlibExt.Complexity.HashCounting

/-- For the singleton zero set in one coordinate, the doubled count is 4. -/
example : (2 * ∑ a : Fin 1 → ZMod 2,
    (({(0 : Fin 1 → ZMod 2)} : Finset (Fin 1 → ZMod 2)).filter
      (fun x => a ⬝ᵥ x = 0)).card) = 4 := by
  rw [hash_count_identity]
  decide

/-- For the singleton nonzero set `{![1]}` in one coordinate, only the hash `a = 0`
annihilates `![1]`, so the doubled count is `2`. -/
example : (2 * ∑ a : Fin 1 → ZMod 2,
    (({![1]} : Finset (Fin 1 → ZMod 2)).filter (fun x => a ⬝ᵥ x = 0)).card) = 2 := by
  rw [hash_count_identity]
  decide

/-- For the mixed set `{0, ![1]}` in one coordinate, the zero vector is annihilated by
both hashes and `![1]` by one, so the doubled count is `2 * 3 = 6`. -/
example : (2 * ∑ a : Fin 1 → ZMod 2,
    (({0, ![1]} : Finset (Fin 1 → ZMod 2)).filter (fun x => a ⬝ᵥ x = 0)).card) = 6 := by
  rw [hash_count_identity]
  decide

end
