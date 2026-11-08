/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.TransitiveClosure

open Cslib.Algorithms.Lean.TransitiveClosure

#check @transitiveClosureStages
#check @transitiveClosure
#check @transitiveClosureStages_zero_cell
#check @transitiveClosureStages_succ_cell
#check @transitiveClosure_initializations
#check @transitiveClosure_stage_assignments
#check @transitiveClosure_transition_assignments
#check @transitiveClosureStages_cell_eq_true_iff
#check @transitiveClosure_cell_eq_true_iff
#check @transitiveClosure_time
#check @transitiveClosure_time_zero
#check @transitiveClosure_time_one

example {n : Nat} (adjacency : Fin n → Fin n → Bool) (i j : Fin n) :
    (transitiveClosure adjacency).ret i j = true ↔
      Relation.ReflTransGen (fun a b => adjacency a b = true) i j :=
  transitiveClosure_cell_eq_true_iff adjacency i j

example {n : Nat} (adjacency : Fin n → Fin n → Bool) (k : Nat) (hk : k ≤ n)
    (i j : Fin n) :
    ((transitiveClosureStages adjacency k hk).ret.get i).get j = true ↔
      ∃ path, path.IsChainFromTo (fun a b => adjacency a b = true) i j ∧
        Cslib.Algorithms.Lean.FloydWarshall.InternalVerticesBelow k path :=
  transitiveClosureStages_cell_eq_true_iff adjacency k hk i j

example (adjacency : Fin 0 → Fin 0 → Bool) : (transitiveClosure adjacency).time = 0 :=
  transitiveClosure_time_zero adjacency

example (adjacency : Fin 1 → Fin 1 → Bool) : (transitiveClosure adjacency).time = 2 :=
  transitiveClosure_time_one adjacency

example {n : Nat} (adjacency : Fin n → Fin n → Bool) (i : Fin n) :
    (transitiveClosure adjacency).ret i i = true :=
  (transitiveClosure_cell_eq_true_iff adjacency i i).mpr .refl

example {n : Nat} (adjacency : Fin n → Fin n → Bool) :
    (transitiveClosure adjacency).time = n ^ 2 + n ^ 3 :=
  transitiveClosure_time adjacency
