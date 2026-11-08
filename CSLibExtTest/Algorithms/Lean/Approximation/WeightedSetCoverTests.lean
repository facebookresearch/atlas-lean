/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.WeightedSetCover
public meta import CSLibExt.Algorithms.Lean.Approximation.WeightedSetCover
public meta import Mathlib.Data.Finset.Sort

/-!
# Weighted greedy set cover tests

Executed fixtures: each run computes the greedy cover, checks that it is drawn from the family
and covers the universe, computes the cheapest cover by brute force over all subfamilies, and
checks Chvátal's bound `cost ≤ H(d) · optimum` (`d` the largest set size); it throws otherwise.
Instances: one where the cheapest-per-element choice misleads greedy (`33/10` against `3`), unit
costs (the unweighted algorithm), a free set, and the classical instance where greedy pays `H(4)`
against an optimum of `1 + ε`. Closed checks instantiate the bound.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def show' (C : List (Finset ℕ)) : List (List ℕ) := C.map (·.sort (· ≤ ·))

/-- The cheapest cover of `U` by a subfamily of `F`, by brute force (`none` if there is none). -/
private meta def bruteCost (w : Finset ℕ → ℚ) (F : List (Finset ℕ)) (U : Finset ℕ) : Option ℚ :=
  let subs := F.sublists.filter fun C => (U.sort (· ≤ ·)).all fun x => C.any fun S => x ∈ S
  (subs.map fun C => (C.map w).sum).min?

private meta def check (label : String) (w : Finset ℕ → ℚ) (F : List (Finset ℕ))
    (U : Finset ℕ) : IO Unit := do
  let C := (weightedGreedySetCover w F U).ret
  let cost := (C.map w).sum
  let d := (F.map Finset.card).foldl max 0
  let H : ℚ := harmonic d
  let fromF := C.all fun S => F.contains S
  let covers := (U.sort (· ≤ ·)).all fun x => C.any fun S => x ∈ S
  match bruteCost w F U with
  | none => throw (IO.userError s!"{label}: no cover")
  | some opt =>
    unless fromF && covers && cost ≤ H * opt do
      throw (IO.userError s!"{label}: greedy {show' C} costs {cost}, optimum {opt}, H(d) = {H}")
    IO.println s!"{label}: greedy {show' C} costs {cost} ≤ H({d}) · {opt} = {H * opt}"

/-- Greedy takes `{0, 1}` first (cost `9/5`, `9/10` per element, against `1` for the whole set and
`3/2` for `{2}`), then has to pay `3/2` for `{2}`: `33/10` against the optimum `3`. -/
private meta def misled : List (Finset ℕ) := [{0, 1, 2}, {0, 1}, {2}]

private meta def misledCost (S : Finset ℕ) : ℚ :=
  if S = {0, 1, 2} then 3 else if S = {0, 1} then 9 / 5 else 3 / 2

#eval check "misleading ratio" misledCost misled {0, 1, 2}
#eval check "unit costs" (fun _ => 1)
  [{0, 1, 2, 3}, {0, 4}, {1, 5}, {2, 3}, {4, 5}] {0, 1, 2, 3, 4, 5}
#eval check "a free set" (fun S => if S = {3, 4} then 0 else 1)
  [{0, 1}, {1, 2}, {3, 4}, {2, 3}] {0, 1, 2, 3, 4}
-- The classical bad instance: singletons `{i}` cost `1 / (i + 1)`, the whole set costs `1 + ε`;
-- greedy pays `H(4) = 25/12` against `1 + ε`.
#eval check "H(n) instance"
  (fun S => if S.card = 1 then 1 / ((S.sum id : ℕ) + 1 : ℚ) else 101 / 100)
  [{0, 1, 2, 3}, {0}, {1}, {2}, {3}] {0, 1, 2, 3}

/-- Chvátal's bound on the misleading instance, with the whole set as the comparison cover. -/
example : totalCost misledCost (weightedGreedySetCover misledCost misled {0, 1, 2}).ret ≤
    harmonic 3 * totalCost misledCost [{0, 1, 2}] := by
  refine weightedGreedySetCover_approx _ misled {0, 1, 2} ?_ ?_ [{0, 1, 2}] ?_ ?_
  · intro S _; unfold misledCost; split_ifs <;> norm_num
  · intro S hS; simp only [misled, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl <;> decide
  · simp [misled]
  · intro x hx; exact ⟨{0, 1, 2}, by simp, hx⟩

#print axioms weightedGreedySetCover_approx
#print axioms weightedGreedySetCover_cost_le_sum_harmonic
#print axioms weightedGreedySetCover_covers
#print axioms weightedGreedySetCover_mem
#print axioms weightedGreedySetCover_time_le

end Cslib.Algorithms.Lean.TimeM
