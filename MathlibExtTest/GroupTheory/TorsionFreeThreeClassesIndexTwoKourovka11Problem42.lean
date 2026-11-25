/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TorsionFreeThreeClassesIndexTwoKourovka11Problem42
import Mathlib.GroupTheory.IndexNormal

open MathlibExt.GroupTheory.TorsionFreeThreeClassesIndexTwoKourovka11Problem42Wanted

-- An index-two subgroup makes the example nontrivial, so torsion-freeness forces it to be infinite.
example : ∃ (G : Type) (_ : Group G) (H : Subgroup G),
    Infinite G ∧ Finite (ConjClasses G) ∧ H.Normal ∧ H.index = 2 := by
  obtain ⟨G, inst, ht, hc, H, hi⟩ := torsionFreeThreeClassesIndexTwo_holds
  refine ⟨G, inst, H, ?_, Nat.finite_of_card_ne_zero (by omega), H.normal_of_index_eq_two hi, hi⟩
  by_contra h
  have := Finite.of_not_infinite h
  have htop : H = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x = 1
    · exact hx ▸ H.one_mem
    · exact (ht x hx (isOfFinOrder_of_finite x)).elim
  simp [htop] at hi
