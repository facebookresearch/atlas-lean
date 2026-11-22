/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.AStar.Consistent
public meta import CSLibExt.Algorithms.Lean.AStar.Consistent
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation

/-!
# A* tests

Executed fixtures: each run checks that the heuristic is consistent, runs A*, and compares every `g
v` with brute-force shortest distances (Bellman-Ford relaxation for `n` rounds); it checks that
every reconstructed path starts at the source, ends at `v`, follows edges, and weighs `g v`, that
each key equals `g v + h v - h source`, and that the cost is `n * n` plus the adjacency entries; it
throws otherwise. Fixtures: a 5 × 5 grid with pseudo-random weights and the Manhattan heuristic, the
same grid with the zero heuristic (plain Dijkstra), a graph with unreachable vertices, and 30
pseudo-random sparse graphs with the heuristic `h v = ⌊d(v, goal) / 2⌋`, run when it is consistent.
An inconsistent heuristic shows the hypothesis is needed: A* then returns cost 3 where 2 is optimal.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AStar

open Cslib.Algorithms.Lean.DirectedAdjacency

private meta def mkGraph (n : ℕ) (adj : Fin n → List (Fin n)) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency := adj

/-- Shortest distances by `n` rounds of Bellman-Ford relaxation. -/
private meta def brute (n : ℕ) (adj : Fin n → List (Fin n)) (w : Fin n → Fin n → ℕ)
    (s : Fin n) : List (Option ℕ) := Id.run do
  let mut d : List (Option ℕ) := (List.finRange n).map fun v => if v = s then some 0 else none
  for _ in [0:n] do
    for u in List.finRange n do
      match d.getD u.val none with
      | none => pure ()
      | some du =>
        for v in adj u do
          let cand := du + w u v
          match d.getD v.val none with
          | some dv => if cand < dv then d := d.set v.val (some cand)
          | none => d := d.set v.val (some cand)
  return d

private meta def check (label : String) (n : ℕ) (adj : Fin n → List (Fin n))
    (w : Fin n → Fin n → ℕ) (h : Fin n → ℕ) (s goal : Fin n) (quiet : Bool := false) :
    IO Unit := do
  let G := mkGraph n adj
  unless (List.finRange n).all fun u => (adj u).all fun v => h u ≤ w u v + h v do
    throw (IO.userError s!"{label}: heuristic not consistent")
  let r := aStar G w h s
  let bf := brute n adj w s
  for v in List.finRange n do
    let g := r.ret.g.get v
    unless g == bf.getD v.val none do
      throw (IO.userError s!"{label}: g {v} = {g}, shortest {bf.getD v.val none}")
    match g with
    | none => unless (r.ret.pathTo? v).isNone do throw (IO.userError s!"{label}: path to {v}")
    | some gv =>
      unless r.ret.search.distance.get v == some (gv + h v - h s) do
        throw (IO.userError s!"{label}: key of {v} is not g + h - h source")
      match r.ret.pathTo? v with
      | none => throw (IO.userError s!"{label}: no path to reached {v}")
      | some p =>
        unless p.head? == some s && p.getLast? == some v && pathWeight w p == gv &&
            (p.zip p.tail).all (fun e => e.2 ∈ adj e.1) do
          throw (IO.userError s!"{label}: bad path {p} to {v}")
  unless r.time.total == n * n + ((List.finRange n).map fun u => (adj u).length).sum do
    throw (IO.userError s!"{label}: cost {r.time.total}")
  unless quiet do
    IO.println s!"{label}: g(goal) = {r.ret.g.get goal}, path {r.ret.pathTo? goal}; all \
      {n} vertices match Bellman-Ford; cost {r.time.total}"

/-- A `k × k` grid, 4-neighbour moves, pseudo-random weights in `[1, 9]`. -/
private meta def grid (k : ℕ) (u : Fin (k * k)) : List (Fin (k * k)) :=
  let r := u.val / k; let c := u.val % k
  ((if r > 0 then [u.val - k] else []) ++ (if r + 1 < k then [u.val + k] else []) ++
    (if c > 0 then [u.val - 1] else []) ++ (if c + 1 < k then [u.val + 1] else [])).filterMap
    fun i => if hi : i < k * k then some ⟨i, hi⟩ else none

private meta def gridW (u v : Fin 25) : ℕ := 1 + (u.val * 7 + v.val * 13 + u.val * v.val) % 9

private meta def manhattan (goal : ℕ) (u : Fin 25) : ℕ :=
  let a := u.val / 5; let b := u.val % 5; let x := goal / 5; let y := goal % 5
  (if a ≤ x then x - a else a - x) + (if b ≤ y then y - b else b - y)

#eval check "5x5 grid, Manhattan heuristic" 25 (grid 5) gridW (manhattan 24) 0 24
#eval check "5x5 grid, zero heuristic (Dijkstra)" 25 (grid 5) gridW (fun _ => 0) 0 24
#eval check "unreachable vertices" 5
  (fun u => if hu : u.val < 2 then [⟨u.val + 1, by omega⟩] else [])
  (fun _ _ => 2) (fun u => if u.val ≤ 2 then 2 * (2 - u.val) else 0) 0 2

-- Pseudo-random sparse graphs; the heuristic is the exact distance to the goal in the reverse
-- graph, halved and rounded down (consistent whenever the check accepts it).
#eval do
  let mut ran := 0
  for i in [0:30] do
    let seed := i * 7919 + 17
    let adj : Fin 9 → List (Fin 9) := fun u =>
      (List.finRange 9).filter fun v => u ≠ v && (seed + u.val * 31 + v.val * 17) % 4 == 0
    let w : Fin 9 → Fin 9 → ℕ := fun u v => (seed + u.val * 5 + v.val * 11) % 7
    let goal : Fin 9 := 8
    let radj : Fin 9 → List (Fin 9) := fun v => (List.finRange 9).filter fun u => v ∈ adj u
    let back := brute 9 radj (fun a b => w b a) goal
    let h : Fin 9 → ℕ := fun v => (back.getD v.val none).getD 0 / 2
    if (List.finRange 9).all fun u => (adj u).all fun v => h u ≤ w u v + h v then
      check s!"random {i}" 9 adj w h 0 goal (quiet := true)
      ran := ran + 1
  IO.println s!"pseudo-random sparse graphs: h consistent on {ran} of 30, A* matches Bellman-Ford \
    on all of those"

-- An inconsistent heuristic (`h a = 5 > weight a t + h t = 1`) breaks optimality.
#eval do
  let adj : Fin 3 → List (Fin 3) := ![[1, 2], [2], []]
  let w : Fin 3 → Fin 3 → ℕ := fun u v => if u = 0 ∧ v = 2 then 3 else 1
  let h : Fin 3 → ℕ := ![0, 5, 0]
  let r := aStar (mkGraph 3 adj) w h 0
  unless !((List.finRange 3).all fun u => (adj u).all fun v => h u ≤ w u v + h v) &&
      r.ret.g.get 2 == some 3 && (brute 3 adj w 0).getD 2 none == some 2 do
    throw (IO.userError "inconsistent-heuristic fixture no longer shows the failure")
  IO.println s!"inconsistent heuristic: A* returns {r.ret.g.get 2}, shortest is \
    {(brute 3 adj w 0).getD 2 none}"

/-! Closed checks -/

example {n : ℕ} (G : DirectedAdjacency (Fin n)) (w : Fin n → Fin n → ℕ) (h : Fin n → ℕ)
    (hc : Consistent G w h) (s v : Fin n) (g d : ℕ) (hv : (aStar G w h s).ret.g.get v = some g)
    (hp : HasPathWeight G w s v d) : g ≤ d :=
  aStar_distance_minimal s hc hv hp

#print axioms pathWeight_reducedWeight
#print axioms admissible_of_consistent
#print axioms aStar_key
#print axioms aStar_distance_realized
#print axioms aStar_distance_minimal
#print axioms aStar_distance_eq_none_iff
#print axioms aStar_pathTo?_spec
#print axioms aStar_predecessor_spec
#print axioms aStar_time

end Cslib.Algorithms.Lean.AStar
