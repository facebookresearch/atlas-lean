/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.HeldKarp
public import Mathlib.Algebra.Order.Ring.Int
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.HeldKarp
public meta import Mathlib.Algebra.Order.Ring.Int

/-!
# Held–Karp tests

The first instance is the four-city example of Eppstein's notes (start city `3`, the other cities
`p, q, r` numbered `0, 1, 2`), whose optimal tour costs `67`; the closed examples check the table
values of the notes, the base case and the recurrence on it. The second instance has asymmetric
and negative costs. Executed fixtures run `solve` and compare its value and its two counters
with the expected ones and with the bounds `n² 2ⁿ` and `n 2ⁿ`; the step count for `m` other cities
is `m + Σ_{k=1}^{m} C(m, k) k max(1, k - 1)` and the entry count `Σ_{k=1}^{m} C(m, k) k`.
Abstract examples instantiate the main theorem, including the smallest case of two cities.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.HeldKarp

open MetricTSP

/-- Symmetric distances of Eppstein's example: `p q = 14`, `p r = 15`, `q r = 29`, `s p = 18`,
`s q = 21`, `s r = 17`, with `p, q, r, s` numbered `0, 1, 2, 3`. -/
private def eppstein (i j : Fin 4) : ℤ :=
  let rows : List (List ℤ) :=
    [[0, 14, 15, 18], [14, 0, 29, 21], [15, 29, 0, 17], [18, 21, 17, 0]]
  (rows.getD i.val []).getD j.val 0

/-- Asymmetric costs, some negative: `d i j = 3 i - 2 j + [i < j]`. A tour through `0, 1, 2, 3`
costs `0 + 1 + 2 + 3` plus its number of cyclic ascents, which is at least one, so the optimum
is `7`. -/
private def skew (i j : Fin 4) : ℤ :=
  3 * (i : ℤ) - 2 * (j : ℤ) + if i < j then 1 else 0

private meta def showCost : WithTop ℤ → String
  | ⊤ => "⊤"
  | (x : ℤ) => toString x

private meta def check (label : String) (d : Fin 4 → Fin 4 → ℤ) (s : Fin 4)
    (others : List (Fin 4)) (value : WithTop ℤ) (steps entries : ℕ) : IO Unit := do
  let res := solve d s others
  let n := others.length + 1
  unless res.ret == value && res.time == (steps, entries) &&
      steps ≤ n ^ 2 * 2 ^ n && entries ≤ n * 2 ^ n do
    throw (IO.userError
      s!"{label}: value {showCost res.ret}, {res.time.1} steps, {res.time.2} entries")
  IO.println s!"{label}: value {showCost res.ret}, {res.time.1} steps, {res.time.2} entries"

#eval check "Eppstein's example" eppstein 3 [0, 1, 2] (67 : ℤ) 18 12
#eval check "Eppstein's example, other order" eppstein 3 [2, 0, 1] (67 : ℤ) 18 12
#eval check "Eppstein's example, start p" eppstein 0 [1, 2, 3] (67 : ℤ) 18 12
#eval check "skew costs" skew 0 [1, 2, 3] (7 : ℤ) 18 12
#eval check "skew costs, start 2" skew 2 [3, 0, 1] (7 : ℤ) 18 12

/-! The table of Eppstein's notes and the optimal tour costs, evaluated from the definitions
by enumerating paths and tours. A path that leaves out the start city, or that must end at it
after visiting another city, does not exist. -/

private meta def checkValue (label : String) (actual expected : WithTop ℤ) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: {showCost actual}, expected {showCost expected}")
  IO.println s!"{label}: {showCost actual}"

#eval do
  checkValue "C({s, p}, p)" (minPathCost eppstein 3 {3, 0} 0) (18 : ℤ)
  checkValue "C({s, q}, q)" (minPathCost eppstein 3 {3, 1} 1) (21 : ℤ)
  checkValue "C({s, r}, r)" (minPathCost eppstein 3 {3, 2} 2) (17 : ℤ)
  checkValue "C({s, p, q}, p)" (minPathCost eppstein 3 {3, 0, 1} 0) (35 : ℤ)
  checkValue "C({s, p, q}, q)" (minPathCost eppstein 3 {3, 0, 1} 1) (32 : ℤ)
  checkValue "C({s, p, r}, p)" (minPathCost eppstein 3 {3, 0, 2} 0) (32 : ℤ)
  checkValue "C({s, p, r}, r)" (minPathCost eppstein 3 {3, 0, 2} 2) (33 : ℤ)
  checkValue "C({s, q, r}, q)" (minPathCost eppstein 3 {3, 1, 2} 1) (46 : ℤ)
  checkValue "C({s, q, r}, r)" (minPathCost eppstein 3 {3, 1, 2} 2) (50 : ℤ)
  checkValue "C(V, p)" (minPathCost eppstein 3 Finset.univ 0) (60 : ℤ)
  checkValue "C(V, q)" (minPathCost eppstein 3 Finset.univ 1) (46 : ℤ)
  checkValue "C(V, r)" (minPathCost eppstein 3 Finset.univ 2) (50 : ℤ)
  checkValue "optimal tour, Eppstein" (optimalTourCost eppstein) (67 : ℤ)
  checkValue "optimal tour, skew" (optimalTourCost skew) (7 : ℤ)
  checkValue "C({s, p}, s)" (minPathCost eppstein 3 {3, 0} 3) ⊤
  checkValue "C({p, q}, q)" (minPathCost eppstein 3 {0, 1} 1) ⊤
  checkValue "C({s, p, q}, r)" (minPathCost eppstein 3 {3, 0, 1} 2) ⊤

/-- The base case and one step of the recurrence, on Eppstein's example. -/
example : minPathCost eppstein 3 {3, 2} 2 = (eppstein 3 2 : WithTop ℤ) :=
  minPathCost_pair eppstein (by decide)

example : minPathCost eppstein 3 {3, 0, 1, 2} 0 =
    ({3, 0, 1, 2} \ {3, 0} : Finset (Fin 4)).inf
      fun i => minPathCost eppstein 3 (({3, 0, 1, 2} : Finset (Fin 4)).erase 0) i +
        (eppstein i 0 : WithTop ℤ) :=
  minPathCost_eq_inf eppstein (by decide) (by decide) (by decide)

/-- The exact counters of `solve` for three other cities. -/
example : (solve eppstein 3 [0, 1, 2]).time = (18, 12) := by
  rw [solve_time]
  decide

/-! The main theorem for arbitrary costs. -/

variable {α : Type} [DecidableEq α] [Fintype α]

example (d : α → α → ℤ) (s : α) (hn : 2 ≤ Fintype.card α) :
    optimalTourCost d =
      (Finset.univ.erase s).inf (fun j => minPathCost d s Finset.univ j + d j s) :=
  (heldKarp_correct d s hn).2.2.2.1

example (d : α → α → ℤ) (s : α) (hn : 2 ≤ Fintype.card α) (others : List α)
    (hothers : others.Nodup) (hs : s ∉ others) (hall : ∀ x, x ≠ s → x ∈ others) :
    (solve d s others).ret = optimalTourCost d :=
  ((heldKarp_correct d s hn).2.2.2.2 others hothers hs hall).1

/-- With two cities the only tour goes out and back. -/
example (d : Fin 2 → Fin 2 → ℤ) : optimalTourCost d = ((d 0 1 + d 1 0 : ℤ) : WithTop ℤ) := by
  rw [(heldKarp_correct d 0 (by simp)).2.2.2.1]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  have herase : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  rw [herase, Finset.inf_singleton, huniv, minPathCost_pair d (by decide)]
  exact (WithTop.coe_add _ _).symm

/-- When a path can exist, its least cost is finite. -/
example (d : α → α → ℤ) (s : α) (S : Finset α) (j : α) (hs : s ∈ S) (hj : j ∈ S)
    (hjs : j ≠ s) : minPathCost d s S j ≠ ⊤ := by
  obtain ⟨L, -, hL⟩ := (isLeast_minPathCost d hs hj hjs).1
  rw [← hL]
  exact WithTop.coe_ne_top

end Cslib.Algorithms.Lean.HeldKarp

#print axioms Cslib.Algorithms.Lean.HeldKarp.heldKarp_correct
#print axioms Cslib.Algorithms.Lean.HeldKarp.solve_time
