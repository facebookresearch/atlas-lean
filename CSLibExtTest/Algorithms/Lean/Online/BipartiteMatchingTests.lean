/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.BipartiteMatching
public meta import CSLibExt.Algorithms.Lean.Online.BipartiteMatching

/-!
# Online bipartite matching tests

Executed fixtures: on 100 pseudo-random bipartite graphs (up to 6 + 6 vertices), the greedy
online matching is maximal, both it and the maximum matching (`maxMatching` of
`Graph/BipartiteMatching.lean`) are valid (edges only, no left vertex matched twice), and the
maximum matching has at most twice as many edges; the worst ratio seen is printed.
On the tight example (left `0` adjacent to right `0, 1`, left `1` to right `0`) greedy matches one
edge and the maximum matching two, by `decide`. Each run throws on a violation. Closed checks
instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Online.BipartiteMatching

open Cslib.Algorithms.Lean.BipartiteMatching

/-- The tight example. -/
private def tight : Fin 2 → List (Fin 2) := fun i => if i = 0 then [0, 1] else [0]

example : (pairs (greedyAll tight)).card = 1 := by decide

example : (pairs (maxMatching tight)).card = 2 := by decide

#eval do
  let mut s := 4
  let mut worst : ℕ × ℕ := (1, 1)
  for _ in [0:100] do
    s := (s * 1103515245 + 12345) % 2147483648
    let a := s / 7 % 6 + 1
    s := (s * 1103515245 + 12345) % 2147483648
    let b := s / 7 % 6 + 1
    let mut rows : Array (List ℕ) := #[]
    for _ in [0:a] do
      let mut row : List ℕ := []
      for j in [0:b] do
        s := (s * 1103515245 + 12345) % 2147483648
        if s / 11 % 3 == 0 then row := row ++ [j]
      rows := rows.push row
    let adj : Fin a → List (Fin b) := fun i =>
      (rows.getD i.val []).filterMap fun j => if h : j < b then some ⟨j, h⟩ else none
    let g := greedyAll adj
    -- valid and maximal
    for i in List.finRange a do
      for j in adj i do
        unless g j != none || (List.finRange b).any (fun j' => g j' == some i) do
          throw (IO.userError "not maximal")
    let mx := maxMatching adj
    -- both partner arrays are matchings (`Valid`): edges, and no left vertex used twice
    let check (name : String) (mate : Fin b → Option (Fin a)) : IO Unit := do
      for j in List.finRange b do
        match mate j with
        | some i => unless j ∈ adj i do throw (IO.userError s!"{name}: not an edge")
        | none => pure ()
      unless ((List.finRange b).filterMap mate).Nodup do
        throw (IO.userError s!"{name}: a left vertex is matched twice")
    check "greedy" g
    check "maximum" mx
    let gc := (pairs g).card
    let mc := (pairs mx).card
    unless mc ≤ 2 * gc do throw (IO.userError s!"ratio fails: max {mc}, greedy {gc}")
    if 0 < mc && gc * worst.2 < worst.1 * mc then worst := (gc, mc)
  IO.println s!"100 random graphs: greedy and maximum valid, greedy maximal, max ≤ 2 greedy; worst \
    greedy/max = {worst.1}/{worst.2}"

/-! Closed checks -/

example {a b : ℕ} (adj : Fin a → List (Fin b)) :
    (pairs (maxMatching adj)).card ≤ 2 * (pairs (greedyAll adj)).card :=
  card_maxMatching_le adj

#print axioms card_le_two_mul_greedyAll
#print axioms greedyAll_maximal

end Cslib.Algorithms.Lean.Online.BipartiteMatching
