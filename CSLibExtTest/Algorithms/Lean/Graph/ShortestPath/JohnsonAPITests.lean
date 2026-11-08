/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson

/-!
# Ordinary Johnson facade consumers

Each frozen public name is checked through ordinary imports, and the four theorems are applied
to their canonical path, cycle and cost specifications without private implementation access.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

#check Johnson.johnson
#check Johnson.johnson_eq_none_iff
#check Johnson.johnson_distance_spec
#check Johnson.johnson_time_of_success
#check Johnson.johnson_time_le

example {n : Nat} (edges : List (BellmanFord.Edge n)) :
    (Johnson.johnson edges).ret = none ↔
      ∃ source : Fin n, BellmanFord.HasReachableNegativeCycle edges source :=
  Johnson.johnson_eq_none_iff edges

example {n : Nat} (edges : List (BellmanFord.Edge n))
    (distance : Fin n → Fin n → WithTop Int)
    (run : (Johnson.johnson edges).ret = some distance) (source target : Fin n)
    (value : Int) (cell : distance source target = (value : WithTop Int)) :
    (∃ path, BellmanFord.IsWeightedPath edges source target path ∧
      BellmanFord.pathWeight path = value) ∧
        ∀ path, BellmanFord.IsWeightedPath edges source target path →
          value ≤ BellmanFord.pathWeight path :=
  (Johnson.johnson_distance_spec edges distance run source target).2 value cell

example {n : Nat} (edges : List (BellmanFord.Edge n))
    (distance : Fin n → Fin n → WithTop Int)
    (run : (Johnson.johnson edges).ret = some distance) :
    (Johnson.johnson edges).time = n^3 + n*edges.length + (n+1)*(edges.length+n) +
      2*n^2 + 4*edges.length + 5*n + 1 :=
  Johnson.johnson_time_of_success edges distance run

example {n : Nat} (edges : List (BellmanFord.Edge n)) :
    (Johnson.johnson edges).time ≤ n^3 + n*edges.length + (n+1)*(edges.length+n) +
      2*n^2 + 4*edges.length + 5*n + 1 + 3*(n+1) :=
  Johnson.johnson_time_le edges
