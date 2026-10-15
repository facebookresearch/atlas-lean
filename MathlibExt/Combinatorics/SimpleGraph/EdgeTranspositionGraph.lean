/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
/-!
# EdgeTranspositionGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 432
-/

@[expose] public section

-- Combinatorics 432: Edge-transposition graph
def edgeTranspositionGraph {n : ℕ} (T : Set (Equiv.Perm (Fin n))) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => Equiv.swap i j ∈ T)


abbrev swap : Equiv.Perm (Fin 3) := Equiv.swap 0 2


/-- Decidability of the relation defining the `(02)` transposition graph. -/
instance : DecidableRel
    (fun i j : Fin 3 => Equiv.swap i j ∈ ({swap} : Set (Equiv.Perm (Fin 3)))) :=
  fun i j => decidable_of_iff _ Set.mem_singleton_iff


/-- Decidability of adjacency in the `(02)` transposition graph: unfold to
    `fromRel` so Mathlib's decidability instance fires. -/
instance : DecidableRel (edgeTranspositionGraph {swap}).Adj := by
  unfold edgeTranspositionGraph
  infer_instance

example :
    let TG := edgeTranspositionGraph {swap}
    TG.edgeFinset.card = 1 ∧ TG.degree 1 = 0 := by
  decide

end
