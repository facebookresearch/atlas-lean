/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.ShannonCounting

/-!
# Tests for Shannon counting

* The count `2 ^ (2 ^ 2) = 16` of two-variable Boolean functions.
* A one-descriptor class misses some two-variable function.
* Boundary case: every class of `15 = 16 - 1` descriptors misses some
  two-variable function.
-/

@[expose] public section

namespace MathlibExtTest.Complexity.ShannonCounting

open MathlibExt.Complexity.ShannonCounting

/-- There are `2 ^ (2 ^ 2) = 16` two-variable Boolean functions. -/
example : Fintype.card ((Fin 2 → Bool) → Bool) = 16 := card_bool_functions 2

/-- A one-descriptor class, whose descriptor evaluates to the constant `true`
function, misses some two-variable function. -/
example : ∃ f : (Fin 2 → Bool) → Bool,
    ∀ d : Fin 1, (fun _ : Fin 1 => fun _ : Fin 2 → Bool => true) d ≠ f :=
  exists_not_computed 2 (fun _ : Fin 1 => fun _ : Fin 2 → Bool => true)
    (by simp)

/-- Boundary case: any `15` descriptors miss one of the `16` two-variable
Boolean functions. -/
example (eval : Fin 15 → (Fin 2 → Bool) → Bool) : ∃ f, ∀ d, eval d ≠ f :=
  exists_not_computed 2 eval (by simp)

end MathlibExtTest.Complexity.ShannonCounting
