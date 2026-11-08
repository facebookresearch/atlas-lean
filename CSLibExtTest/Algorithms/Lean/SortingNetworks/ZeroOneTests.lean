/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne
public meta import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne
public import Mathlib.Data.Int.Order.Basic
public meta import Mathlib.Data.Int.Order.Basic

/-!
# Comparator network tests

Closed checks: Knuth's 5-comparator network on 4 wires and 9-comparator network on 5 wires pass
`sortsBool` by `decide`, so by the 0-1 principle they sort every input over `ℤ` (and any linear
order); `sortsBool_eq_true_iff` is used in both directions, including to show that the 4-wire
network without its last comparator does not sort all Boolean inputs. Executed fixtures: the two
networks sort pseudo-random integer inputs (the output equals the sorted input), while dropping
any one comparator from the 4-wire network makes `sortsBool` fail, exhibited by a Boolean input it
leaves unsorted. Each run throws on failure.
-/

namespace Cslib.Algorithms.Lean.SortingNetworks

/-- Knuth's optimal 4-wire network (5 comparators, depth 3). -/
private def net4 : Network 4 := [(0, 1), (2, 3), (0, 2), (1, 3), (1, 2)]

/-- Knuth's optimal 5-wire network (9 comparators). -/
private def net5 : Network 5 := [(0, 1), (3, 4), (2, 4), (2, 3), (0, 3), (0, 2), (1, 4), (1, 3),
  (1, 2)]

theorem net4_sorts : Sorts net4 ℤ := sorts_of_sortsBool (by decide) ℤ

theorem net5_sorts : Sorts net5 ℤ := sorts_of_sortsBool (by decide) ℤ

private meta def toList {n : ℕ} (v : Fin n → ℤ) : List ℤ := (List.finRange n).map v

private meta def checkSorts {n : ℕ} (label : String) (net : Network n) : IO Unit := do
  let mut s := 7
  for _ in [0:200] do
    let mut xs : List ℤ := []
    for _ in [0:n] do
      s := (s * 1103515245 + 12345) % 2147483648
      xs := xs ++ [((s / 7 % 41 : ℕ) : ℤ) - 20]
    let v : Fin n → ℤ := fun i => xs.getD i.val 0
    let out := toList (run net v)
    unless out == xs.mergeSort (· ≤ ·) do
      throw (IO.userError s!"{label}: {xs} gave {out}")
  IO.println s!"{label}: sorts 200 pseudo-random integer inputs (output = sorted input)"

#eval checkSorts "Knuth 4-wire network" net4
#eval checkSorts "Knuth 5-wire network" net5

-- every comparator of the 4-wire network is needed
#eval do
  for k in [0:5] do
    let net := net4.eraseIdx k
    if sortsBool net then throw (IO.userError s!"dropping comparator {k} still sorts")
    let bad := (List.range 16).find? fun (m : ℕ) =>
      let v : Fin 4 → Bool := fun i => m.testBit i.val
      !(List.finRange 3).all fun (i : Fin 3) => run net v i.castSucc ≤ run net v i.succ
    IO.println s!"without comparator {k}: sortsBool fails, e.g. on the Boolean input \
      with bits {bad}"

/-! Closed checks -/

example (v : Fin 4 → ℤ) : Monotone (run net4 v) := net4_sorts v

example (v : Fin 5 → ℤ) : ∃ σ : Equiv.Perm (Fin 5), run net5 v = v ∘ σ := run_perm net5 v

-- both directions of `sortsBool_eq_true_iff`: acceptance from sorting, rejection to non-sorting
example : sortsBool net4 = true := sortsBool_eq_true_iff.2 (sorts_of_sortsBool (by decide) Bool)

example : ¬ Sorts (net4.eraseIdx 4) Bool := fun h => by
  have := sortsBool_eq_true_iff.2 h
  revert this
  decide

#print axioms sorts_of_sorts_bool
#print axioms sorts_of_sortsBool
#print axioms sortsBool_eq_true_iff
#print axioms run_comp
#print axioms run_perm
#print axioms net5_sorts

end Cslib.Algorithms.Lean.SortingNetworks
