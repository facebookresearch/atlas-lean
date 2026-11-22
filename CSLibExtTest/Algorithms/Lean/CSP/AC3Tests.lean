/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.AC3
public meta import CSLibExt.Algorithms.Lean.CSP.AC3
public meta import Mathlib.Data.Finset.Sort

/-!
# AC-3 tests

Executed fixtures: each run computes AC-3's domains and checks that they are subsets of the input
domains, that every arc is consistent, that every solution found by brute force over all assignments
survives, and that the number of revisions is within `|arcs| + ∑ x, |dom x| · indeg x`; it throws
otherwise. Fixtures: the Australia map-colouring problem (Russell and Norvig, Figure 6.1) with full
domains, with `WA = red`, and with `WA = red, Q = green` (no solution; AC-3 empties domains), an
ordering chain `x < y < z < w` over `0..4`, two variables forced unequal with one value each (AC-3
empties a domain), three pairwise-different variables with two colours (arc consistent, yet no
solution: AC-3 is not complete), and 40 pseudo-random symmetric CSPs on 5 variables. Closed checks
instantiate the theorems.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ArcConsistency

/-- Arcs in both directions for each listed pair, all with the same symmetric relation. -/
private meta def sym {n : ℕ} (pairs : List (Fin n × Fin n)) (rel : Fin n → Fin n → ℕ → ℕ → Bool) :
    BinaryCSP (Fin n) ℕ :=
  ⟨pairs.flatMap fun e => [e, (e.2, e.1)], fun x y a b =>
    if (x, y) ∈ pairs then rel x y a b else if (y, x) ∈ pairs then rel y x b a else true⟩

private meta def assignments (n : ℕ) (vals : List ℕ) : List (Fin n → ℕ) :=
  (List.finRange n).foldl (fun acc v => acc.flatMap fun σ => vals.map fun a =>
    fun w => if w = v then a else σ w) [fun _ => 0]

private meta def check (label : String) {n : ℕ} (P : BinaryCSP (Fin n) ℕ)
    (dom : Fin n → Finset ℕ) (quiet : Bool := false) : IO Unit := do
  let r := ac3All P dom
  let R := r.ret
  let vals := ((List.finRange n).foldl (fun s v => s ∪ dom v) ∅).sort (· ≤ ·)
  unless (List.finRange n).all fun v => R v ⊆ dom v do
    throw (IO.userError s!"{label}: a domain grew")
  unless P.arcs.all fun e => (R e.1).sort (· ≤ ·) |>.all fun a =>
      (R e.2).sort (· ≤ ·) |>.any fun b => P.allowed e.1 e.2 a b do
    throw (IO.userError s!"{label}: an arc is not consistent")
  let sols := (assignments n vals).filter fun σ =>
    (List.finRange n).all (fun v => σ v ∈ dom v) &&
      P.arcs.all fun e => P.allowed e.1 e.2 (σ e.1) (σ e.2)
  unless sols.all fun σ => (List.finRange n).all fun v => σ v ∈ R v do
    throw (IO.userError s!"{label}: a solution was lost")
  let bound := P.arcs.length + ((List.finRange n).map fun v => (dom v).card * indeg P v).sum
  unless r.time ≤ bound do throw (IO.userError s!"{label}: {r.time} revisions > {bound}")
  unless quiet do
    IO.println s!"{label}: domains {(List.finRange n).map fun v => (R v).sort (· ≤ ·)}, \
      {sols.length} solutions, {r.time} revisions ≤ {bound}"

-- Australia: WA NT SA Q NSW V T = 0..6; colours red green blue = 0 1 2
private meta def australia : BinaryCSP (Fin 7) ℕ :=
  sym [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)] fun _ _ a b => a ≠ b

#eval check "Australia, full domains" australia fun _ => {0, 1, 2}
#eval check "Australia, WA = red" australia fun v => if v = 0 then {0} else {0, 1, 2}
#eval check "Australia, WA = red, Q = green (no solution)" australia
  fun v => if v = 0 then {0} else if v = 3 then {1} else {0, 1, 2}
#eval check "chain x < y < z < w" (sym [(0, 1), (1, 2), (2, 3)] fun _ _ a b => a < b)
  fun (_ : Fin 4) => {0, 1, 2, 3, 4}
#eval check "x ≠ y with one value each" (sym [(0, 1)] fun _ _ a b => a ≠ b)
  fun (_ : Fin 2) => {7}
#eval check "triangle, two colours" (sym [(0, 1), (1, 2), (0, 2)] fun _ _ a b => a ≠ b)
  fun (_ : Fin 3) => {0, 1}

#eval do
  for i in [0:40] do
    let seed := i * 7919 + 5
    let pairs := ((List.finRange 5).flatMap fun (x : Fin 5) => (List.finRange 5).filterMap
      fun (y : Fin 5) =>
      if x < y && (seed + x.val * 13 + y.val * 7) % 3 == 0 then some (x, y) else none)
    let rel : Fin 5 → Fin 5 → ℕ → ℕ → Bool := fun x y a b =>
      (seed + x.val * 3 + y.val * 5 + a * 11 + b * 17) % 5 < 3
    let dom : Fin 5 → Finset ℕ := fun v =>
      (Finset.range 4).filter fun a => (seed + v.val + a) % 7 != 0
    check s!"random {i}" (sym pairs rel) dom (quiet := true)
  IO.println "40 pseudo-random symmetric CSPs on 5 variables: all checks pass"

/-! Closed checks -/

example (P : BinaryCSP (Fin 3) ℕ) (dom : Fin 3 → Finset ℕ) (σ : Fin 3 → ℕ)
    (hσ : IsSolution P dom σ) (v : Fin 3) : σ v ∈ (ac3All P dom).ret v :=
  mem_ac3_of_isSolution P hσ v

#print axioms ac3_subset
#print axioms mem_ac3_of_isSolution
#print axioms not_isSolution_of_ac3_eq_empty
#print axioms arcConsistent_ac3
#print axioms ac3_time_le

end Cslib.Algorithms.Lean.ArcConsistency
