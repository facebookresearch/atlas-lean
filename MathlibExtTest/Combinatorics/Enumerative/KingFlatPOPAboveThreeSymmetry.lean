/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import MathlibExt.Combinatorics.Enumerative.KingFlatPOPAboveThreeSymmetry

/-! # Tests for the king generating function avoiding $Q_3$ -/

namespace MetaMathlibExt

-- The empty permutation contributes 1, and this coefficient is unchanged by the rename.
example : PowerSeries.coeff 0 (kingFlatPOPAboveGF 2) = 1 := by
  rw [kingFlatPOPAboveGF_two_eq_rename, PowerSeries.coeff_map]
  suffices h : PowerSeries.coeff 0 (kingFlatPOPBelowGF 1) = 1 by rw [h, map_one]
  classical
  rw [kingFlatPOPBelowGF, PowerSeries.coeff_mk,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMaxCount, permRightToLeftMaxCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun ⟨f, _⟩ => (f 0).elim0⟩
  · intro σ _ hσ
    exact (hσ (Subsingleton.elim σ 1)).elim

-- The one-line permutation 13524 has unequal ascent/descent and left/right maximum counts.
private def sigma : Equiv.Perm (Fin 5) :=
  ⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩

private def tau : Equiv.Perm (Fin 5) := (Fin.revPerm.trans sigma).trans Fin.revPerm

example : IsKingPerm sigma ∧ IsKingPerm tau := by
  unfold IsKingPerm
  decide

-- Reversal followed by complement keeps the ascent and descent exponents at 3 and 1,
-- and switches the left/right record exponents from 3 and 2 to 2 and 3.
example : permAscentCount sigma = 3 ∧ permDescentCount sigma = 1 ∧
    permLeftToRightMaxCount sigma = 3 ∧ permRightToLeftMaxCount sigma = 2 ∧
    permAscentCount tau = 3 ∧ permDescentCount tau = 1 ∧
    permLeftToRightMinCount tau = 2 ∧ permRightToLeftMinCount tau = 3 := by
  decide

end MetaMathlibExt
