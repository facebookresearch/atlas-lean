/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.UnionFreeCentralBinomial
import Mathlib.Data.Fintype.Powerset
import Mathlib.Topology.Order.Basic

open MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted
open Finset Filter

-- Every middle layer is an admissible family, including on the empty ground set.
private theorem middle_le_max (n : ℕ) : n.choose (n / 2) ≤ maxUnionFreeSize n := by
  let L := (univ : Finset (Fin n)).powersetCard (n / 2)
  have hL : IsUnionFree L := by
    intro A hA B _ C hC _ hAC _ hU
    apply hAC
    refine eq_of_subset_of_card_le (hU ▸ subset_union_left (s₂ := B)) ?_
    exact (mem_powersetCard.mp hC).2.trans_le (mem_powersetCard.mp hA).2.ge
  refine le_csSup ⟨Fintype.card (Finset (Fin n)), ?_⟩ ⟨L, hL, ?_⟩
  · rintro k ⟨F, -, rfl⟩
    exact card_le_univ F
  · simp [L]

-- The upper bound is asymptotically sharp in both parities.
example : Tendsto (fun n : ℕ => (maxUnionFreeSize n : ℝ) / n.choose (n / 2)) atTop (nhds 1) := by
  have hpos (n : ℕ) : (0 : ℝ) < n.choose (n / 2) := by
    exact_mod_cast Nat.choose_pos (Nat.div_le_self n 2)
  refine tendsto_order.mpr ⟨fun x hx => Eventually.of_forall fun n => ?_, fun x hx => ?_⟩
  · apply hx.trans_le
    apply (le_div_iff₀ (hpos n)).mpr
    rw [one_mul]
    exact_mod_cast middle_le_max n
  · filter_upwards [maxUnionFreeSizeCentralBinomial_holds ((x - 1) / 2) (by linarith)] with n hn
    apply (div_lt_iff₀ (hpos n)).mpr
    exact hn.trans_lt (mul_lt_mul_of_pos_right (by linarith) (hpos n))
