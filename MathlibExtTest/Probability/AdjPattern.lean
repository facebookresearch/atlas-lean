/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.AdjPattern
import Mathlib.Data.Fin.VecNotation

@[expose] public section

open MathlibExt.Probability.AdjPattern

/-- With one vertex and no prescribed entries, both adjacency
functions qualify. -/
example : (Finset.univ.filter
    (fun a : Fin 1 → Fin 1 → Bool => ∀ i : Fin 0, a 0 (Fin.elim0 i) = (fun _ => true) i)).card
    = 2 ^ (1 * 1 - 0) :=
  card_adj_pattern (n := 1) (k := 0) 0 (fun j => Fin.elim0 j)
    (Function.injective_of_subsingleton _) (fun _ => true)

/-- With two vertices, prescribing the single entry `a 0 1 = true` (target `1 ≠ 0`) leaves
the other three entries free: `2 ^ 3 = 8` of the `16` adjacency functions qualify. -/
example : (Finset.univ.filter
    (fun a : Fin 2 → Fin 2 → Bool => ∀ i : Fin 1, a 0 (![1] i) = ![true] i)).card = 8 := by
  rw [card_adj_pattern (n := 2) (k := 1) 0 ![1] (Function.injective_of_subsingleton _)
    ![true]]
  rfl

/-- A target may be `v` itself: with one vertex, prescribing the diagonal entry
`a 0 0 = true` forces the only entry, so exactly `2 ^ 0 = 1` adjacency function
qualifies. -/
example : (Finset.univ.filter
    (fun a : Fin 1 → Fin 1 → Bool => ∀ i : Fin 1, a 0 (![0] i) = ![true] i)).card = 1 := by
  rw [card_adj_pattern (n := 1) (k := 1) 0 ![0] (Function.injective_of_subsingleton _)
    ![true]]
  rfl

end
