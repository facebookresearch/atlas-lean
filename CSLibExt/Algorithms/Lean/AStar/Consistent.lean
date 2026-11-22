/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra

/-!
# A* search with a consistent heuristic is optimal

A* (Hart, Nilsson and Raphael, *A formal basis for the heuristic determination of minimum cost
paths*, 1968) searches a weighted directed graph from a source, repeatedly expanding the open
vertex of least `f = g + h`, where `g` is the best path weight found so far and `h` a heuristic
estimate of the remaining distance to the goal. A heuristic is *consistent* (monotone) if
`h u ≤ weight u v + h v` on every edge (`Consistent`), and *admissible* for a goal if it never
overestimates the distance to the goal (`Admissible`); a consistent heuristic with `h goal = 0` is
admissible (`admissible_of_consistent`).

With a consistent heuristic the reduced weights `weight u v + h v - h u` (`reducedWeight`) are
honest natural numbers, and every path's reduced weight is its weight plus `h` of its end minus
`h` of its start (`pathWeight_reducedWeight`). A* with a consistent heuristic is Dijkstra's
algorithm on the reduced weights (Goldberg and Harrelson, *Computing the shortest path: A* search
meets graph theory*, SODA 2005, Section 3; Russell and Norvig, *Artificial Intelligence: A Modern
Approach*, fourth edition, Section 3.5.2): a path's reduced weight is its `g + h` at the end minus
the constant `h source`, so ordering by Dijkstra's keys is ordering by A*'s `f = g + h`. `aStar`
is defined that way: it runs CSLibExt's verified dense Dijkstra on the reduced weights and converts
the final keys back to path weights `g v = g' v + h source - h v`. What is proved about the keys is
the final identity `g v + h v = g' v + h source` (`aStar_key`); the selection order during the run
is not exposed (the Dijkstra module keeps its loop state private), so the correspondence of the
two expansion orders is the cited fact, not a theorem here.

Main results, for a consistent heuristic:

* `aStar_distance_realized`, `aStar_distance_minimal`: a finite `g v` is the weight of a path from
  the source to `v`, and no path is lighter; so for the goal, A* returns the optimal cost.
* `aStar_distance_eq_none_iff`: `g v` is infinite exactly when `v` is unreachable.
* `aStar_pathTo?_spec`: following predecessors gives a simple path of weight `g v`, an optimal
  path; `aStar_predecessor_spec`: each predecessor edge satisfies `g v = g u + weight u v`.

## Cost model

`aStar` has Dijkstra's dense cost (`DijkstraCost`): `n * n` vertex entries inspected by minimum
selection and every adjacency entry relaxed once (`aStar_time`); computing reduced weights and
converting keys back is free. The dense loop settles every reachable vertex; stopping when the goal
is selected, as A* does, would not change the goal's value but is not modeled.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AStar

open Cslib.Algorithms.Lean.DirectedAdjacency

variable {n : ℕ} (graph : DirectedAdjacency (Fin n)) (weight : Fin n → Fin n → ℕ) (h : Fin n → ℕ)

/-- A consistent (monotone) heuristic: `h u ≤ weight u v + h v` on every edge. -/
def Consistent : Prop := ∀ u v, graph.Edge u v → h u ≤ weight u v + h v

/-- An admissible heuristic for `goal`: it never overestimates the weight of a path to `goal`. -/
def Admissible (goal : Fin n) : Prop :=
  ∀ v d, HasPathWeight graph weight v goal d → h v ≤ d

/-- The reduced weight of an edge, `weight u v + h v - h u`. -/
def reducedWeight (u v : Fin n) : ℕ := weight u v + h v - h u

/-- The output of A*: the underlying search (keys `f - h source` and predecessor pointers) and
the path weights `g`, with `none` for infinity. -/
structure AStarResult (n : ℕ) where
  /-- The search on reduced weights: its distances are the keys `f v - h source`. -/
  search : DijkstraResult n
  /-- The best path weight `g v` from the source. -/
  g : Vector (Option ℕ) n

/-- Follow predecessors from `v` back to the source. -/
def AStarResult.pathTo? (r : AStarResult n) (v : Fin n) : Option (List (Fin n)) :=
  r.search.pathTo? v

/-- A* from `source` with heuristic `h`: Dijkstra on the reduced weights, whose keys are A*'s
`f = g + h` shifted by `h source`, with the keys converted back to path weights `g`. -/
def aStar (source : Fin n) : TimeM DijkstraCost (AStarResult n) := do
  let r ← dijkstra graph (reducedWeight weight h) source
  pure ⟨r, Vector.ofFn fun v => (r.distance.get v).map (· + h source - h v)⟩

variable {graph weight h}

/-- Along a path, the reduced weight is the weight plus `h` of the end minus `h` of the start. -/
theorem pathWeight_reducedWeight (hc : Consistent graph weight h) :
    ∀ (path : List (Fin n)) (u v : Fin n), path.IsChainFromTo graph.Edge u v →
      pathWeight (reducedWeight weight h) path + h u = pathWeight weight path + h v
  | [], _, _, hp => absurd rfl hp.ne_nil
  | [a], u, v, hp => by
      have hu := hp.head_eq
      have hv := hp.getLast_eq
      simp only [List.head_cons, List.getLast_singleton] at hu hv
      subst hu hv
      simp [pathWeight]
  | a :: b :: rest, u, v, hp => by
      have hu : a = u := hp.head_eq
      subst hu
      have hab : graph.Edge a b := (List.isChain_cons_cons.1 hp.isChain).1
      have ih := pathWeight_reducedWeight hc (b :: rest) b v hp.of_cons_cons
      have hcab := hc a b hab
      simp only [pathWeight, reducedWeight] at ih ⊢
      omega

/-- **A consistent heuristic that vanishes at the goal is admissible.** -/
theorem admissible_of_consistent (hc : Consistent graph weight h) {goal : Fin n}
    (hgoal : h goal = 0) : Admissible graph weight h goal := by
  rintro v d ⟨path, hp, rfl⟩
  have := pathWeight_reducedWeight hc path v goal hp
  omega

variable (source : Fin n)

theorem aStar_distance_get (v : Fin n) :
    (aStar graph weight h source).ret.g.get v =
      ((dijkstra graph (reducedWeight weight h) source).ret.distance.get v).map
        (· + h source - h v) := by
  simp only [aStar, TimeM.ret_bind, TimeM.ret_pure]
  change (Vector.ofFn fun w => ((dijkstra graph (reducedWeight weight h) source).ret.distance.get
    w).map (· + h source - h w))[v.1] = _
  rw [Vector.getElem_ofFn]

/-- **The final keys are A*'s `f`-values shifted by `h source`**: Dijkstra's final key `g'` on the
reduced weights satisfies `g v + h v = g' v + h source`. -/
theorem aStar_key (hc : Consistent graph weight h) {v : Fin n} {g : ℕ}
    (hv : (aStar graph weight h source).ret.g.get v = some g) :
    ∃ g', (dijkstra graph (reducedWeight weight h) source).ret.distance.get v = some g' ∧
      g + h v = g' + h source := by
  rw [aStar_distance_get] at hv
  cases hd : (dijkstra graph (reducedWeight weight h) source).ret.distance.get v with
  | none => simp [hd] at hv
  | some g' =>
      simp only [hd, Option.map_some, Option.some.injEq] at hv
      obtain ⟨path, hp, hw⟩ := dijkstra_distance_realized graph _ source v g' hd
      have := pathWeight_reducedWeight hc path source v hp
      exact ⟨g', rfl, by omega⟩

/-- A finite `g v` is the weight of a path from the source to `v`. -/
theorem aStar_distance_realized (hc : Consistent graph weight h) {v : Fin n} {g : ℕ}
    (hv : (aStar graph weight h source).ret.g.get v = some g) :
    HasPathWeight graph weight source v g := by
  rw [aStar_distance_get] at hv
  cases hd : (dijkstra graph (reducedWeight weight h) source).ret.distance.get v with
  | none => simp [hd] at hv
  | some g' =>
      simp only [hd, Option.map_some, Option.some.injEq] at hv
      obtain ⟨path, hp, hw⟩ := dijkstra_distance_realized graph _ source v g' hd
      have := pathWeight_reducedWeight hc path source v hp
      exact ⟨path, hp, by omega⟩

/-- **A* is optimal**: no path from the source to `v` is lighter than a finite `g v`. -/
theorem aStar_distance_minimal (hc : Consistent graph weight h) {v : Fin n} {g d : ℕ}
    (hv : (aStar graph weight h source).ret.g.get v = some g)
    (hpath : HasPathWeight graph weight source v d) : g ≤ d := by
  rw [aStar_distance_get] at hv
  cases hd : (dijkstra graph (reducedWeight weight h) source).ret.distance.get v with
  | none => simp [hd] at hv
  | some g' =>
      simp only [hd, Option.map_some, Option.some.injEq] at hv
      obtain ⟨path, hp, rfl⟩ := hpath
      have hmin := dijkstra_distance_minimal graph _ source v g' _ hd ⟨path, hp, rfl⟩
      have := pathWeight_reducedWeight hc path source v hp
      omega

/-- `g v` is infinite exactly when `v` is unreachable from the source. -/
theorem aStar_distance_eq_none_iff (v : Fin n) :
    (aStar graph weight h source).ret.g.get v = none ↔
      ¬graph.Reachable source v := by
  rw [aStar_distance_get, Option.map_eq_none_iff]
  exact dijkstra_distance_eq_none_iff graph _ source v

theorem aStar_pathTo?_eq (v : Fin n) :
    (aStar graph weight h source).ret.pathTo? v =
      (dijkstra graph (reducedWeight weight h) source).ret.pathTo? v := by
  simp only [aStar, TimeM.ret_bind, TimeM.ret_pure, AStarResult.pathTo?]

/-- Following predecessors gives a simple path from the source of weight `g v`: an optimal path. -/
theorem aStar_pathTo?_spec (hc : Consistent graph weight h) (v : Fin n) (path : List (Fin n))
    (hpath : (aStar graph weight h source).ret.pathTo? v = some path) :
    ∃ g, (aStar graph weight h source).ret.g.get v = some g ∧
      path.head? = some source ∧ path.getLast? = some v ∧
      path.IsChain graph.Edge ∧ path.Nodup ∧ pathWeight weight path = g := by
  rw [aStar_pathTo?_eq] at hpath
  obtain ⟨g', hd, hh, hl, hch, hnd, hw⟩ := dijkstra_pathTo?_spec graph _ source v path hpath
  have hne : path ≠ [] := by rintro rfl; simp at hh
  have hp : path.IsChainFromTo graph.Edge source v :=
    ⟨hch, hne, by rw [List.head?_eq_some_head hne] at hh; exact Option.some.inj hh,
      by rw [List.getLast?_eq_some_getLast hne] at hl; exact Option.some.inj hl⟩
  have := pathWeight_reducedWeight hc path source v hp
  refine ⟨pathWeight weight path, ?_, hh, hl, hch, hnd, rfl⟩
  rw [aStar_distance_get, hd, Option.map_some]
  congr 1
  omega

/-- Each predecessor edge `u → v` satisfies `g v = g u + weight u v`. -/
theorem aStar_predecessor_spec (hc : Consistent graph weight h) (v u : Fin n)
    (hpred : (aStar graph weight h source).ret.search.predecessor.get v = some u) :
    graph.Edge u v ∧ ∃ gu gv,
      (aStar graph weight h source).ret.g.get u = some gu ∧
      (aStar graph weight h source).ret.g.get v = some gv ∧ gv = gu + weight u v := by
  have hpred' :
      (dijkstra graph (reducedWeight weight h) source).ret.predecessor.get v = some u := by
    simpa [aStar] using hpred
  obtain ⟨he, du, dv, hu, hv, heq⟩ := dijkstra_predecessor_spec graph _ source v u hpred'
  obtain ⟨pu, hpu, hwu⟩ := dijkstra_distance_realized graph _ source u du hu
  have hku := pathWeight_reducedWeight hc pu source u hpu
  have hcuv := hc u v he
  refine ⟨he, du + h source - h u, dv + h source - h v, ?_, ?_, ?_⟩
  · rw [aStar_distance_get, hu, Option.map_some]
  · rw [aStar_distance_get, hv, Option.map_some]
  · simp only [reducedWeight] at heq
    omega

/-- **Cost**: Dijkstra's dense cost, `n * n` selection scans plus every adjacency entry. -/
theorem aStar_time :
    (aStar graph weight h source).time.total = n * n + adjacencyEntryCount graph := by
  have := dijkstra_time graph (reducedWeight weight h) source
  simpa [aStar] using this

end Cslib.Algorithms.Lean.AStar
