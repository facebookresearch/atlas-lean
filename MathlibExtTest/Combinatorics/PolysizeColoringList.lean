/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PolysizeColoringList
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.NormNum

namespace MathlibExt.Combinatorics.PolysizeColoringListWanted

-- Two columns with identical coefficients can cancel in the minimum over colourings.
example : discrepancyOn (fun (_ : Fin 1) (_ : Fin 2) => 1) Finset.univ = 0 := by
  classical
  unfold discrepancyOn
  rw [Set.image_univ]
  apply le_antisymm
  · apply (csInf_le (Set.finite_range _).bddBelow
      (Set.mem_range_self (fun j : Fin 2 => decide (j = 0)))).trans_eq
    norm_num [ciSup_unique, Fin.sum_univ_two]
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨ε, rfl⟩
    simpa only [ciSup_unique] using abs_nonneg (∑ j : Fin 2, 1 * (if ε j then (1 : ℝ) else -1))

-- The maximum over column sets detects the nonzero coefficient of a singleton.
example : hereditaryDisc (fun (_ : Fin 1) (_ : Fin 1) => 1) = 1 := by
  classical
  have hS (S : Finset (Fin 1)) : S = ∅ ∨ S = {0} :=
    Finset.subset_singleton_iff.mp fun j _ => Finset.mem_singleton.mpr (Subsingleton.elim j 0)
  have hEmpty : discrepancyOn (fun (_ : Fin 1) (_ : Fin 1) => 1) ∅ = 0 := by
    simp [discrepancyOn, ciSup_unique, Set.image_univ]
  have hSingle : discrepancyOn (fun (_ : Fin 1) (_ : Fin 1) => 1) {0} = 1 := by
    unfold discrepancyOn
    simp only [ciSup_unique, Finset.sum_singleton, one_mul]
    have (ε : Fin 1 → Bool) : |(if ε 0 then (1 : ℝ) else -1)| = 1 := by
      split <;> simp
    simp [this, Set.image_univ]
  apply le_antisymm
  · apply ciSup_le
    intro S
    rcases hS S with rfl | rfl <;> simp [hEmpty, hSingle]
  · exact hSingle.ge.trans (le_ciSup (Set.finite_range _).bddAbove ({0} : Finset (Fin 1)))

-- The discrepancy convention for matrices with no rows gives zero for every set.
example {m : ℕ} (A : Fin 0 → Fin m → ℝ) (S : Finset (Fin m)) :
    discrepancyOn A S = 0 := by
  simp [discrepancyOn, iSup_of_empty', Real.sSup_empty, Set.image_univ]

end MathlibExt.Combinatorics.PolysizeColoringListWanted
