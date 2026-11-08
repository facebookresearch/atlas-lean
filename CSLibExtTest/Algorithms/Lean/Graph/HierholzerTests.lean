/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.Hierholzer
public meta import CSLibExt.Algorithms.Lean.Graph.Hierholzer

/-!
# Hierholzer tests

Executed fixtures on `Fin n` multigraphs: each run checks that the result starts and ends at the
start vertex, that its steps are a permutation of the edge occurrences (`List.isPerm`), and that
the cost is exactly `|E|`. Fixtures: two cycles sharing a vertex (the circuit must splice them),
parallel edges and a self-loop, the de Bruijn graph `B(2, 3)` (its Euler circuit spells a de
Bruijn sequence), and the complete digraph on 7 vertices. Two semi-balanced graphs (a single edge,
and `0 → 1 → 2 → 0 → 2`) give Euler paths instead. Closed checks evaluate `IsEulerCircuit`,
`IsEulerPath`, `IsBalanced` and `IsSemiBalanced` by `decide`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Hierholzer

private def finGraph (n : ℕ) (adj : Fin n → List (Fin n)) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency := adj

private def check {n : ℕ} (label : String) (adj : Fin n → List (Fin n)) (s : Fin n) :
    IO Unit := do
  let g := finGraph n adj
  let r := hierholzer g s
  let W := r.ret
  let ok := W.head? == some s && W.getLast? == some s && (walkEdges W).isPerm (edgeList g)
  unless ok && r.time == (edgeList g).length do
    throw (IO.userError s!"{label}: {W.map (·.val)}, time {r.time}")
  IO.println s!"{label}: {(edgeList g).length} edges, {r.time} traversals"
  if W.length ≤ 12 then IO.println s!"  circuit {W.map (·.val)}"

/-- Two triangles through vertex `0`. -/
private def figureEight : Fin 5 → List (Fin 5)
  | 0 => [1, 3]
  | 1 => [2]
  | 2 => [0]
  | 3 => [4]
  | 4 => [0]

/-- Parallel edges `0 ⇄ 1` (twice each way) and a self-loop at `0`. -/
private def parallel : Fin 2 → List (Fin 2)
  | 0 => [1, 0, 1]
  | 1 => [0, 0]

/-- The de Bruijn graph `B(2, 3)`: states are 2-bit words, `x → 2x + b mod 4`. -/
private def deBruijn : Fin 4 → List (Fin 4) := fun x => [2 * x, 2 * x + 1]

#eval check "figure eight" figureEight 0
#eval check "parallel edges and a self-loop" parallel 0
#eval check "de Bruijn B(2,3)" deBruijn 0
#eval check "complete digraph on 7 vertices"
  (fun (u : Fin 7) => (List.finRange 7).filter (· ≠ u)) 3

#eval
  let g := finGraph 2 fun | 0 => [1] | 1 => []
  let W := (hierholzer g 0).ret
  IO.println s!"single edge 0 → 1: result {W.map (·.val)}, closed: {W.getLast? == some 0}"

example : IsBalanced (finGraph 5 figureEight) := by decide
example : ¬ IsBalanced (finGraph 2 fun | 0 => [1] | 1 => []) := by decide
example : IsEulerCircuit (finGraph 5 figureEight) 0 [0, 3, 4, 0, 1, 2, 0] := by decide
example : IsEulerCircuit (finGraph 5 figureEight) 0 (hierholzer (finGraph 5 figureEight) 0).ret :=
  by decide +kernel

/-- An Euler path: `0 → 1 → 2 → 0 → 2`, from `0` (one extra out-edge) to `2` (one extra in-edge). -/
private def pathGraph : Fin 3 → List (Fin 3)
  | 0 => [1, 2]
  | 1 => [2]
  | 2 => [0]

#eval
  let g := finGraph 3 pathGraph
  let r := hierholzer g 0
  IO.println s!"Euler path: {r.ret.map (·.val)}, {r.time} traversals"

example : IsSemiBalanced (finGraph 3 pathGraph) 0 2 := by decide
example : IsEulerPath (finGraph 3 pathGraph) 0 2 (hierholzer (finGraph 3 pathGraph) 0).ret := by
  decide +kernel

example {V : Type} [DecidableEq V] (g : DirectedAdjacency V) (s : V) (hb : IsBalanced g)
    (hr : ∀ u w, g.Edge u w → g.Reachable s u) : IsEulerCircuit g s (hierholzer g s).ret :=
  hierholzer_isEulerCircuit g s hb hr

/-- The contract of the recursion, for a caller that runs it directly. -/
example {V : Type} [DecidableEq V] (g : DirectedAdjacency V) (fuel : ℕ) (v t : V)
    (R : V → List V) (acc : List V) (hfuel : (edgeListOf g R).length < fuel)
    (hbal : SemiBalancedEdges (edgeListOf g R) v t) :
    ∃ W, (visit fuel v R acc).ret.1 = W ++ acc ∧ W.head? = some v ∧ W.getLast? = some t ∧
      (edgeListOf g R).Perm (walkEdges W ++ edgeListOf g (visit fuel v R acc).ret.2) ∧
      BalancedEdges (edgeListOf g (visit fuel v R acc).ret.2) ∧
      (∀ x ∈ W, (visit fuel v R acc).ret.2 x = []) ∧
      (∀ x, (visit fuel v R acc).ret.2 x <:+ R x) ∧
      (visit fuel v R acc).time + (edgeListOf g (visit fuel v R acc).ret.2).length =
        (edgeListOf g R).length :=
  visit_spec g fuel v t R acc hfuel hbal

#print axioms visit_spec
#print axioms hierholzer_isEulerCircuit
#print axioms hierholzer_isEulerPath
#print axioms hierholzer_time
#print axioms hierholzer_trail
#print axioms isBalanced_of_isEulerCircuit
#print axioms isSemiBalanced_of_isEulerPath
#print axioms exists_isEulerCircuit_iff
#print axioms exists_isEulerPath_iff

end Cslib.Algorithms.Lean.Hierholzer
