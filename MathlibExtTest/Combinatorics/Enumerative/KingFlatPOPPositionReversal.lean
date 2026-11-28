/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import MathlibExt.Combinatorics.Enumerative.KingFlatPOPPositionReversal

/-! # Tests for position reversal of king permutations -/

namespace MetaMathlibExt

-- The empty king permutation avoids both patterns and contributes the constant monomial 1.
example : PowerSeries.coeff 0 (kingFlatPOPBelowGF 2) = 1 ∧
    PowerSeries.coeff 0
      (PowerSeries.map (MvPolynomial.rename
        ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
          (kingFlatPOPBelowGF 1)) = 1 := by
  classical
  have coeff_zero (j : Fin 4) : PowerSeries.coeff 0 (kingFlatPOPBelowGF j) = 1 := by
    rw [coeff_kingFlatPOPBelowGF, Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
    · have ha : permAscentCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      have hd : permDescentCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      have hl : permLeftToRightMaxCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      have hr : permRightToLeftMaxCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      simp [ha, hd, hl, hr]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isKingPerm_iff,
        containsFlatPOPBelow_iff]
      exact ⟨fun i => i.elim0, fun ⟨f, _⟩ => (f 0).elim0⟩
    · intro τ _ hτ
      exact (hτ (Subsingleton.elim τ 1)).elim
  exact ⟨coeff_zero 2, by rw [PowerSeries.coeff_map, coeff_zero, map_one]⟩

-- In one-based notation this king is 42531. Both pairs of statistics have unequal counts.
private def sampleKing : Equiv.Perm (Fin 5) :=
  ⟨![3, 1, 4, 2, 0], ![4, 1, 3, 0, 2], by decide, by decide⟩

private def reversedSampleKing : Equiv.Perm (Fin 5) := Fin.revPerm.trans sampleKing

example : IsKingPerm sampleKing ∧ IsKingPerm reversedSampleKing := by
  simp only [isKingPerm_iff]
  decide

example :
    (permAscentCount sampleKing, permDescentCount sampleKing,
      permLeftToRightMaxCount sampleKing, permRightToLeftMaxCount sampleKing) = (1, 3, 2, 3) ∧
    (permAscentCount reversedSampleKing, permDescentCount reversedSampleKing,
      permLeftToRightMaxCount reversedSampleKing, permRightToLeftMaxCount reversedSampleKing) =
        (3, 1, 3, 2) := by decide

-- The first four entries witness P₂; the last four entries of the reverse witness P₃.
example : ContainsFlatPOPBelow sampleKing 1 ∧ ContainsFlatPOPBelow reversedSampleKing 2 := by
  simp only [containsFlatPOPBelow_iff]
  constructor
  · exact ⟨OrderEmbedding.ofStrictMono (fun i : Fin 4 => ⟨i, i.isLt.trans (by decide)⟩)
      (fun _ _ h => h), by decide⟩
  · exact ⟨OrderEmbedding.ofStrictMono Fin.succ (fun _ _ h => Nat.succ_lt_succ h), by decide⟩

end MetaMathlibExt
