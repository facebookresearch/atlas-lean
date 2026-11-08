/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected
public meta import CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected

/-!
# Undirected Hierholzer tests

Executed fixtures on edge lists over `Fin n`: each run checks the degree condition, then that the
result is an Euler path from `s` to `t` (`IsUEulerPath`, decided: steps as unordered pairs are a
permutation of the edges) and that the cost is exactly `|E|`. Fixtures: two triangles sharing a
vertex (the circuit must splice them), parallel edges and a loop, the complete graph `K₅` (all
degrees 4), a house with a diagonal (an Euler path between its two odd vertices), and a 4 × 4
torus grid.
Königsberg (four odd vertices) has no Euler path from any vertex: its degree condition fails
for every pair, so by `exists_isUEulerPath_iff` there is none. Closed checks evaluate
`IsUEulerPath` and `EvenExcept` by `decide`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Hierholzer

private def check {n : ℕ} (label : String) (E : List (Fin n × Fin n)) (s t : Fin n) :
    IO Unit := do
  unless decide (EvenExcept E s t) do
    throw (IO.userError s!"{label}: degree condition fails")
  let r := uhierholzer E s
  let W := r.ret
  unless decide (IsUEulerPath E s t W) && r.time == E.length do
    throw (IO.userError s!"{label}: {W.map (·.val)}, time {r.time}")
  IO.println s!"{label}: {E.length} edges, {r.time} traversals"
  if W.length ≤ 12 then IO.println s!"  walk {W.map (·.val)}"

/-- Two triangles through vertex `0`. -/
private def bowtie : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]

/-- A double edge `0 - 1`, a loop at `1`, and a triangle `1 - 2 - 3`. -/
private def multi : List (Fin 4 × Fin 4) := [(0, 1), (1, 0), (1, 1), (1, 2), (2, 3), (3, 1)]

/-- The complete graph on 5 vertices. -/
private def k5 : List (Fin 5 × Fin 5) :=
  (List.finRange 5).flatMap fun i => ((List.finRange 5).filter (i < ·)).map (i, ·)

/-- A house: the square `0 1 2 3`, the roof `2 - 4 - 3` and the diagonal `1 - 3`; vertices `1` and
`2` have odd degree. -/
private def house : List (Fin 5 × Fin 5) :=
  [(0, 1), (1, 2), (2, 3), (3, 0), (2, 4), (4, 3), (1, 3)]

/-- The 4 × 4 torus grid (every vertex has degree 4). -/
private def torus : List (Fin 16 × Fin 16) :=
  (List.finRange 16).flatMap fun v =>
    [(v, Fin.ofNat 16 ((v.val / 4) * 4 + (v.val % 4 + 1) % 4)),
      (v, Fin.ofNat 16 ((v.val + 4) % 16))]

/-- Königsberg: land masses `0` (island), `1`, `2`, `3`, seven bridges. -/
private def koenigsberg : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 1), (0, 2), (0, 2), (0, 3), (1, 3), (2, 3)]

#eval check "bowtie" bowtie 0 0
#eval check "parallel edges and a loop" multi 0 0
#eval check "K5" k5 0 0
#eval check "house, Euler path" house 1 2
#eval check "4 × 4 torus" torus 5 5
#eval do
  let ok := (List.finRange 4).all fun s => (List.finRange 4).all fun t =>
    !decide (EvenExcept koenigsberg s t)
  unless ok do throw (IO.userError "Königsberg: degree condition holds somewhere")
  IO.println "Königsberg: no pair (s, t) satisfies the degree condition"

example : IsUEulerPath bowtie 0 0 (uhierholzer bowtie 0).ret := by decide
example : IsUEulerPath house 1 2 (uhierholzer house 1).ret := by decide
example : ¬ EvenExcept koenigsberg 0 0 := by decide
example : ¬ ∃ W, IsUEulerPath koenigsberg 0 1 W := fun ⟨_, h⟩ =>
  absurd (evenExcept_of_isUEulerPath h) (by decide)

#print axioms uhierholzer_isUEulerPath
#print axioms uhierholzer_isUEulerCircuit
#print axioms uhierholzer_trail
#print axioms uhierholzer_time
#print axioms exists_isUEulerPath_iff
#print axioms evenExcept_of_isUEulerPath

end Cslib.Algorithms.Lean.Hierholzer
