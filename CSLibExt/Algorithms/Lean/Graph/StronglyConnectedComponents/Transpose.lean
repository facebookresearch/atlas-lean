/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents

/-!
# Strong connectivity is invariant under edge reversal

Reversing every edge of a directed graph reverses reachability, so two vertices are
mutually reachable after the reversal exactly when they were before: a graph and its
transpose have the same strongly connected components. Kosaraju's algorithm relies on
this fact.

## Main results

* `mutual_reflTransGen_swap_iff`: for an arbitrary edge relation `E`, mutual
  reachability (`Relation.ReflTransGen`) under the reversed relation `Function.swap E`
  is mutual reachability under `E`.
* `stronglyConnected_transpose_iff`: the same statement for ordered directed graphs,
  using `DirectedAdjacency.transpose` and `StronglyConnected`.
* `stronglyConnectedSetoid_transpose`: a graph and its transpose have the same
  strongly connected components, as equivalence relations.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StronglyConnectedComponents

universe u

/-- Strong connectivity of an arbitrary edge relation is unchanged by reversing every
edge: `x` and `y` are mutually reachable under `Function.swap E` exactly when they are
mutually reachable under `E`. -/
theorem mutual_reflTransGen_swap_iff {V : Type u} {E : V → V → Prop} (x y : V) :
    (Relation.ReflTransGen (Function.swap E) x y ∧
        Relation.ReflTransGen (Function.swap E) y x) ↔
      (Relation.ReflTransGen E x y ∧ Relation.ReflTransGen E y x) := by
  constructor
  · rintro ⟨forward, backward⟩
    exact ⟨Relation.reflTransGen_swap.mp backward, Relation.reflTransGen_swap.mp forward⟩
  · rintro ⟨forward, backward⟩
    exact ⟨Relation.reflTransGen_swap.mpr backward, Relation.reflTransGen_swap.mpr forward⟩

/-- Two vertices are strongly connected in the transposed graph exactly when they are
strongly connected in the original graph. -/
theorem stronglyConnected_transpose_iff {V : Type u} [DecidableEq V]
    {graph : DirectedAdjacency V} {left right : V} :
    StronglyConnected graph.transpose left right ↔ StronglyConnected graph left right := by
  simp only [StronglyConnected, DirectedAdjacency.reachable_transpose_iff]
  exact And.comm

/-- A graph and its transpose have the same strongly connected components. -/
theorem stronglyConnectedSetoid_transpose {V : Type u} [DecidableEq V]
    (graph : DirectedAdjacency V) :
    stronglyConnectedSetoid graph.transpose = stronglyConnectedSetoid graph :=
  Setoid.ext fun _ _ => stronglyConnected_transpose_iff

end Cslib.Algorithms.Lean.StronglyConnectedComponents
