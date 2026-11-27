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
import all MathlibExt.Combinatorics.Enumerative.KingFlatPOPPositionReversal

/-! # Tests for position reversal of king permutations -/

namespace MetaMathlibExt

-- The empty king permutation avoids both patterns and contributes the constant monomial 1.
example : PowerSeries.coeff 0 (kingFlatPOPBelowGF 2) = 1 ∧
    PowerSeries.coeff 0
      (PowerSeries.map (MvPolynomial.rename
        ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
          (kingFlatPOPBelowGF 1)) = 1 := by
  suffices h : PowerSeries.coeff 0 (kingFlatPOPBelowGF 2) = 1 from
    ⟨h, kingFlatPOPBelowGF_two_eq_rename ▸ h⟩
  classical
  rw [kingFlatPOPBelowGF, PowerSeries.coeff_mk,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMaxCount, permRightToLeftMaxCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun ⟨f, _⟩ => (f 0).elim0⟩
  · intro τ _ hτ
    exact (hτ (Subsingleton.elim τ 1)).elim

-- In one-based notation this king is 42531. Both pairs of statistics have unequal counts.
private def sampleKing : Equiv.Perm (Fin 5) :=
  ⟨![3, 1, 4, 2, 0], ![4, 1, 3, 0, 2], by decide, by decide⟩

example : IsKingPerm (positionReverse sampleKing) ∧
    permAscentCount (positionReverse sampleKing) = 3 ∧
    permDescentCount (positionReverse sampleKing) = 1 ∧
    permLeftToRightMaxCount (positionReverse sampleKing) = 3 ∧
    permRightToLeftMaxCount (positionReverse sampleKing) = 2 := by
  rw [isKingPerm_positionReverse, permAscentCount_positionReverse,
    permDescentCount_positionReverse, permLeftToRightMaxCount_positionReverse,
    permRightToLeftMaxCount_positionReverse]
  unfold IsKingPerm
  decide

-- The first four entries witness P₂; the reversed last four entries witness P₃.
example : ContainsFlatPOPBelow (positionReverse sampleKing) 2 := by
  rw [containsFlatPOPBelow_positionReverse]
  change ContainsFlatPOPBelow sampleKing 1
  refine ⟨OrderEmbedding.ofStrictMono (fun i : Fin 4 => ⟨i, i.isLt.trans (by decide)⟩)
    (fun _ _ h => h), ?_⟩
  change ∀ m : Fin 4, m ≠ 1 → sampleKing 1 < sampleKing ⟨m, m.isLt.trans (by decide)⟩
  decide

end MetaMathlibExt
