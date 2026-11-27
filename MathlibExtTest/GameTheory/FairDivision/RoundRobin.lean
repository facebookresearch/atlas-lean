/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GameTheory.FairDivision.RoundRobin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for round-robin allocation -/

namespace MathlibExtTest.GameTheory.FairDivision.RoundRobin

open MathlibExt.GameTheory.FairDivision.Indivisible

-- Agent 1 picks first. Agent 0 values good 0 at five, and each other good at one.
private def order : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
private def v (a : Fin 2) (g : Fin 3) : ℝ :=
  if a = 0 then (if g = 0 then 5 else 1) else (if g = 1 then 1 else 3)

private def picks := Equiv.refl (Fin 3)
private def otherPicks : Equiv.Perm (Fin 3) := Equiv.swap 1 2

-- At the second turn, either good 1 or good 2 is a favourite.
private theorem greedy : IsRoundRobinDraft order v picks := by
  intro t u h
  fin_cases t <;> fin_cases u <;>
    norm_num [order, v, picks, Fin.ofNat, Equiv.swap_apply_def] at *

example : IsRoundRobinDraft order v otherPicks := by
  intro t u h
  fin_cases t <;> fin_cases u <;>
    norm_num [order, v, otherPicks, Fin.ofNat, Equiv.swap_apply_def] at *

example : roundRobinAllocation order picks 1 = 0 ∧
    roundRobinAllocation order otherPicks 1 = 1 := by decide

-- Starting with good 2 is legal, but taking good 1 next leaves the preferred good 0 unused.
example : ¬ IsRoundRobinDraft order v (Equiv.swap (0 : Fin 3) 2) := by
  intro h
  have := h 1 2 (by decide)
  norm_num [order, v, Fin.ofNat, Equiv.swap_apply_def] at this

private theorem laterBundle : bundle (roundRobinAllocation order picks) 0 = {1} := by decide
private theorem firstBundle : bundle (roundRobinAllocation order picks) 1 = {0, 2} := by decide

-- Three goods, two agents: the first picker gets the only turn in the last round.
-- To the later picker the bundles are worth one and six. Only removing good 0 works.
example : value v (roundRobinAllocation order picks) 0 = 1 ∧
    bundleValue v 0 (bundle (roundRobinAllocation order picks) 1) = 6 ∧
    bundleValue v 0 ((bundle (roundRobinAllocation order picks) 1).erase 0) = 1 ∧
    bundleValue v 0 ((bundle (roundRobinAllocation order picks) 1).erase 2) = 5 := by
  norm_num [value, laterBundle, firstBundle, bundleValue, v]

example : ¬ IsEF v (roundRobinAllocation order picks) := by
  intro h
  have := h 0 1
  norm_num [value, laterBundle, firstBundle, bundleValue, v] at this

example : IsEF1 v (roundRobinAllocation order picks) := by
  apply greedy.isEF1
  intro a g
  unfold v
  split_ifs <;> norm_num

-- No goods: there is a complete run, and even the first agent receives the empty bundle.
example : ∃ p : Fin 0 ≃ Fin 0, IsRoundRobinDraft order (fun _ _ => 0) p ∧
    bundle (roundRobinAllocation order p) 1 = ∅ := by
  exact ⟨Equiv.refl _, fun t => Fin.elim0 t, by decide⟩

end MathlibExtTest.GameTheory.FairDivision.RoundRobin
