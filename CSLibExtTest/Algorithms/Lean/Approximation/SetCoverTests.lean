/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.SetCover
public meta import CSLibExt.Algorithms.Lean.Approximation.SetCover
public meta import Mathlib.Data.Finset.Sort

/-!
# Greedy set cover tests

Executed fixtures check the chosen sets, in order, and the cost (every search, including the
final unsuccessful one, costs `|F| + ∑ |S|`) on an instance where greedy uses
three sets against an optimum of two, on ties, on an element no set covers (greedy stops without
covering it), and on the empty universe. The harmonic bound is instantiated on the first instance
with its optimal cover.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

private meta def show' (C : List (Finset ℕ)) : List (List ℕ) := C.map (·.sort (· ≤ ·))

private meta def check (label : String) (F : List (Finset ℕ)) (U : Finset ℕ)
    (expected : List (List ℕ)) (cost : ℕ) : IO Unit := do
  let r := greedySetCover F U
  unless show' r.ret == expected && r.time == cost do
    throw (IO.userError s!"{label}: got {show' r.ret} with cost {r.time}")
  IO.println s!"{label}: {show' r.ret}, cost {r.time}"

/-- Greedy takes the big set first and then needs two more; `{1, 2, 5}, {3, 4, 6}` suffice. -/
private def bait : List (Finset ℕ) := [{1, 2, 3, 4}, {1, 2, 5}, {3, 4, 6}]

#eval check "greedy 3 vs optimum 2" bait {1, 2, 3, 4, 5, 6} [[1, 2, 3, 4], [1, 2, 5], [3, 4, 6]] 52
#eval check "empty universe" bait ∅ [] 13
#eval check "tie goes to the first set" [{1, 2}, {2, 3}, {3}] {1, 2, 3} [[1, 2], [2, 3]] 24
#eval check "uncoverable element is left" [{1, 2}] {1, 2, 3} [[1, 2]] 6
#eval check "no sets" [] {1} [] 0
#eval check "only empty sets: every set is visited" [∅, ∅, ∅] {1} [] 3
#eval check "one set covers all" [{1}, {1, 2, 3}, {2}] {1, 2, 3} [[1, 2, 3]] 16

example : ∀ x ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
    ∃ S ∈ (greedySetCover bait {1, 2, 3, 4, 5, 6}).ret, x ∈ S :=
  greedySetCover_covers _ _ (by decide)

/-- The harmonic bound on the first instance: `3 ≤ 2 * H(4) = 25/6`. -/
example : ((greedySetCover bait {1, 2, 3, 4, 5, 6}).ret.length : ℚ) ≤ 2 * harmonic 4 := by
  have := greedySetCover_approx bait {1, 2, 3, 4, 5, 6} (d := 4) (by decide)
    [{1, 2, 5}, {3, 4, 6}] (by decide) (by decide)
  simpa using this

example : harmonic 4 = 25 / 12 := by simp [harmonic]; norm_num

universe u

example {α : Type u} [DecidableEq α] (F : List (Finset α)) (U : Finset α) :
    (greedySetCover F U).time ≤ (U.card + 1) * (F.length + (F.map Finset.card).sum) :=
  greedySetCover_time_le F U

#print axioms greedySetCover
#print axioms greedySetCover_mem
#print axioms greedySetCover_covers
#print axioms greedySetCover_length_le_sum_harmonic
#print axioms greedySetCover_approx
#print axioms greedySetCover_approx_card
#print axioms greedySetCover_approx_log
#print axioms greedySetCover_time_le

end Cslib.Algorithms.Lean.TimeM
