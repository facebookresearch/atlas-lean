/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Hall.Fractional
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.Hall.Fractional`

* `finiteRelationHall_of_fractionalWeights` for the identity weights on `Fin 3`.
* `finiteSubset_card_lt_of_fractionalWeights_of_target_slack`: one source sending all its weight
  to target `0` among targets `{0, 1}` gives `1 < 2`.
-/

@[expose] public section


namespace MathlibExtTest.StatMech.Combinatorics.Hall.Fractional

example : ∀ sources : Finset (Fin 3), sources.card ≤
    (Finset.univ.filter fun target => ∃ source ∈ sources, source = target).card := by
  have h := finiteRelationHall_of_fractionalWeights (Source := Fin 3) (Target := Fin 3) (· = ·) (fun s t => if s = t then 1 else 0)
      (fun s t => by split <;> norm_num) (fun s t h => by simp [h]) (fun s => by simp)
      (fun t => by simp)
  convert h

example : ({0} : Finset (Fin 1)).card < ({0, 1} : Finset (Fin 2)).card :=
  finiteSubset_card_lt_of_fractionalWeights_of_target_slack
    (fun _ t => if t = 0 then (1 : ℝ) else 0) {0} {0, 1} (fun _ _ => by simp)
    (fun t _ => by split <;> simp) 1 (by simp) (by simp)

end MathlibExtTest.StatMech.Combinatorics.Hall.Fractional
