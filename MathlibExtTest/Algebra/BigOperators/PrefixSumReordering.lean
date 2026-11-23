/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.BigOperators.PrefixSumReordering
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # Tests for reordering prefix sums -/

namespace MetaMathlibExt

-- The empty family admits the empty prefix.
example (x y : Fin 0 → ℝ) :
    ∃ σ : Equiv.Perm (Fin 0), ∀ s ≤ 0,
      ∑ i ∈ Finset.univ.filter (fun i : Fin 0 => i.val < s), x (σ i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin 0 => i.val < s), y (σ i) :=
  exists_perm_prefix_sum_le x y (by simp)

-- For (1, -1) against (0, 0), the totals agree but the first prefix forces a swap.
example :
    ∃ σ : Equiv.Perm (Fin 2), σ 0 ≠ 0 ∧ ∀ s ≤ 2,
      (∑ i ∈ Finset.univ.filter (fun i : Fin 2 => i.val < s),
        if σ i = 0 then (1 : ℝ) else -1) ≤ 0 := by
  let x (i : Fin 2) : ℝ := if i = 0 then 1 else -1
  obtain ⟨σ, hσ⟩ := exists_perm_prefix_sum_le x (fun _ => 0) (by norm_num [x, Fin.sum_univ_two])
  refine ⟨σ, ?_, fun s hs => by simpa [x] using hσ s hs⟩
  intro hzero
  have hfirst := hσ 1 (by decide)
  have hone : Finset.univ.filter (fun i : Fin 2 => i.val < 1) = {0} := by decide
  rw [hone, Finset.sum_singleton, Finset.sum_singleton] at hfirst
  norm_num [x, hzero] at hfirst

end MetaMathlibExt
