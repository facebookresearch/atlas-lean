/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.WeightedVertexCover
public meta import CSLibExt.Algorithms.Lean.Approximation.WeightedVertexCover
public meta import Mathlib.Data.Finset.Sort

/-!
# Weighted vertex cover tests

Executed fixtures: each run computes the pricing cover, checks that it covers every edge,
computes the lightest vertex cover by brute force over all vertex subsets, checks the weight
against twice the optimum, and checks the cost `|E| + |V|`; it throws otherwise. Instances: a
star whose heavy center the pricing method avoids, a path, a weighted triangle, a graph with a
free vertex, and a pseudo-random weighted graph. Closed checks instantiate the bound, and the
vertex-cover property for a graph whose edges are listed in one orientation only.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

/-- The lightest vertex cover of the listed edges on `Fin n`, by brute force over bit masks. -/
private meta def bruteWeight (n : ℕ) (w : Fin n → ℚ) (edges : List (Fin n × Fin n)) : ℚ :=
  let covers := (List.range (2 ^ n)).filter fun m =>
    edges.all fun e => Nat.testBit m e.1.val || Nat.testBit m e.2.val
  (covers.map fun m => ((List.finRange n).filter fun v => Nat.testBit m v.val).map w |>.sum).foldl
    min ((List.finRange n).map w).sum

private meta def check (label : String) (n : ℕ) (w : Fin n → ℚ)
    (edges : List (Fin n × Fin n)) : IO Unit := do
  let r := pricingVertexCover w edges
  let C := r.ret
  let weight := (C.sort (· ≤ ·)).map w |>.sum
  let opt := bruteWeight n w edges
  let covers := edges.all fun e => e.1 ∈ C || e.2 ∈ C
  unless covers && weight ≤ 2 * opt && r.time == edges.length + n do
    throw (IO.userError s!"{label}: cover {(C.sort (· ≤ ·)).map (·.val)} weighs {weight}, \
      optimum {opt}, cost {r.time}")
  IO.println s!"{label}: cover {(C.sort (· ≤ ·)).map (·.val)} weighs {weight} ≤ 2 · {opt}, \
    cost {r.time} = |E| + |V|"

#eval check "star with a heavy center" 5 (fun v => if v.val = 0 then 10 else 1)
  [(0, 1), (0, 2), (0, 3), (0, 4)]
#eval check "path" 5 (fun v => (v.val + 1 : ℚ)) [(0, 1), (1, 2), (2, 3), (3, 4)]
#eval check "weighted triangle" 3 (fun v => [3, 4, 5][v.val]!) [(0, 1), (1, 2), (2, 0)]
#eval check "a free vertex" 4 (fun v => if v.val = 2 then 0 else 2) [(0, 2), (1, 2), (2, 3), (0, 1)]
#eval check "pseudo-random, 8 vertices" 8 (fun v => (((v.val * 7 + 3) % 5 + 1 : ℕ) : ℚ))
  ((List.range 14).map fun i => (Fin.ofNat 8 (i * i + 1), Fin.ofNat 8 (i * 3 + 2)))

/-- The bound on the star, against the cover by the center. -/
example : ∑ v ∈ (pricingVertexCover (fun v : Fin 5 => if v.val = 0 then (10 : ℚ) else 1)
      [(0, 1), (0, 2), (0, 3), (0, 4)]).ret, (if v.val = 0 then (10 : ℚ) else 1) ≤
    2 * ∑ v ∈ ({0} : Finset (Fin 5)), (if v.val = 0 then (10 : ℚ) else 1) :=
  pricingVertexCover_weight_le _ (fun v => by split_ifs <;> decide) _ {0} (by decide)

/-- The star's edges, each listed once. -/
private def starEdges : List (Fin 5 × Fin 5) := [(0, 1), (0, 2), (0, 3), (0, 4)]

/-- The vertex-cover property for the graph of an edge list that lists each edge in one
orientation only. -/
example : (SimpleGraph.fromRel fun u v : Fin 5 => (u, v) ∈ starEdges).IsVertexCover
    ↑(pricingVertexCover (fun v : Fin 5 => if v.val = 0 then (10 : ℚ) else 1) starEdges).ret :=
  pricingVertexCover_isVertexCover _ _ (fun v => by split_ifs <;> decide) starEdges
    fun u v h => ((SimpleGraph.fromRel_adj _ u v).1 h).2

#print axioms pricingVertexCover_weight_le
#print axioms pricingVertexCover_covers
#print axioms pricingVertexCover_isVertexCover
#print axioms pricingVertexCover_time

end Cslib.Algorithms.Lean.TimeM
