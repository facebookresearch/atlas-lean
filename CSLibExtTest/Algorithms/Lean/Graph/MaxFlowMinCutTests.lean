/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.MaxFlowMinCut
public meta import CSLibExt.Algorithms.Lean.Graph.MaxFlowMinCut

/-!
# Edmonds-Karp / max-flow min-cut bridge tests

Executed fixtures: on 60 pseudo-random capacity matrices (3 to 6 vertices, capacities `0..4`),
the arc flow `arcFlow` of `edmondsKarp` respects the capacities and conserves flow at interior
vertices, its value equals the capacity of `residualCut`, which separates source and sink, and
that capacity is the minimum over all `2 ^ (n - 2)` source-sink cuts (brute force). Each run
throws on a violation. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Graph.MaxFlowMinCut

open Cslib.Algorithms.Lean.EdmondsKarp

#eval do
  let mut s := 29
  for _ in [0:60] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 7 % 4 + 3
    let mut rows : Array (Array ℕ) := #[]
    for _ in [0:n] do
      let mut row : Array ℕ := #[]
      for _ in [0:n] do
        s := (s * 1103515245 + 12345) % 2147483648
        row := row.push (if s / 11 % 3 == 0 then 0 else s / 13 % 5)
      rows := rows.push row
    let cap : Fin n → Fin n → ℕ := fun u v => (rows.getD u.val #[]).getD v.val 0
    let src : Fin n := ⟨0, by omega⟩
    let snk : Fin n := ⟨n - 1, by omega⟩
    let F := edmondsKarp cap src snk
    let tab := (List.finRange n).map fun u => (List.finRange n).map fun v => arcFlow F u v
    let a : Fin n → Fin n → ℕ := fun u v => (tab.getD u.val []).getD v.val 0
    for u in List.finRange n do
      for v in List.finRange n do
        unless a u v ≤ cap u v do throw (IO.userError "capacity violated")
    for v in List.finRange n do
      if v != src && v != snk then
        let inflow := (List.finRange n).foldl (fun acc u => acc + a u v) 0
        let outflow := (List.finRange n).foldl (fun acc w => acc + a v w) 0
        unless inflow == outflow do throw (IO.userError "conservation violated")
    let value : ℤ := (List.finRange n).foldl (fun acc w => acc + (a src w : ℤ) - (a w src : ℤ)) 0
    let S := residualCut cap F src
    unless src ∈ S && snk ∉ S do throw (IO.userError "residualCut is not an s-t cut")
    let capOf (T : Finset (Fin n)) : ℤ :=
      (List.finRange n).foldl (fun acc u => (List.finRange n).foldl (fun acc' v =>
        if u ∈ T ∧ v ∉ T then acc' + (cap u v : ℤ) else acc') acc) 0
    unless value == capOf S do throw (IO.userError s!"value {value} ≠ cut {capOf S}")
    -- brute-force minimum cut over subsets containing the source and not the sink
    let mut best : ℤ := capOf S
    for mask in [0:2 ^ (n - 2)] do
      let T : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter fun v =>
        v.val == 0 || (0 < v.val && v.val < n - 1 && (mask / 2 ^ (v.val - 1)) % 2 == 1)
      if capOf T < best then best := capOf T
    unless best == value do throw (IO.userError s!"min cut {best} ≠ flow {value}")
  IO.println "60 random networks: arc flow feasible, value = residual cut = brute-force min cut"

/-! Closed checks -/

example (cap : Fin 4 → Fin 4 → ℕ) : ∃ f : Fin 4 → Fin 4 → ℕ,
    MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow (realCap cap) 0 3
      (fun u v => (f u v : ℝ)) ∧
    ∀ g : Fin 4 → Fin 4 → ℝ,
      MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.IsFeasibleFlow (realCap cap) 0 3 g →
      MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue 0 g ≤
        MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted.flowValue 0 (fun u v => (f u v : ℝ)) :=
  exists_nat_max_flow cap (by decide)

#print axioms edmondsKarp_max_flow_min_cut
#print axioms exists_nat_max_flow

end Cslib.Algorithms.Lean.Graph.MaxFlowMinCut
