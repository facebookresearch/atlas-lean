/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.ShannonCounting

@[expose] public section

/-- There are `2 ^ (2 ^ 2) = 16` two-variable Boolean functions. -/
example : Fintype.card ((Fin 2 → Bool) → Bool) = 16 := card_bool_functions 2

/-- A one-element descriptor class misses some two-variable function. -/
example : ∃ f, ∀ d : Fin 1, (fun _ : Fin 1 => (fun _ => true)) d ≠ f :=
  exists_not_computed 2 (fun _ : Fin 1 => (fun _ => true)) (by norm_num [card_bool_functions])

end
