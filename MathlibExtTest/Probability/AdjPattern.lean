/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.AdjPattern

@[expose] public section

/-- With one vertex and no prescribed entries, both adjacency
functions qualify. -/
example : (Finset.univ.filter
    (fun a : Fin 1 → Fin 1 → Bool => ∀ i : Fin 0, a 0 (Fin.elim0 i) = (fun j => true) i)).card
    = 2 ^ (1 * 1 - 0) :=
  card_adj_pattern (n := 1) (k := 0) 0 (fun j => Fin.elim0 j)
    (Function.injective_of_subsingleton _) (fun j => Fin.elim0 j) (fun _ => true)

end
