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
import MathlibExt.Combinatorics.Enumerative.KingFlatPOPSymmetry

namespace MetaMathlibExt

-- The empty king permutation avoids both patterns and contributes the constant monomial 1.
example : PowerSeries.coeff 0 (kingFlatPOPAboveGF 0) = 1 ∧
    PowerSeries.coeff 0
      (PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 0)) = 1 := by
  suffices h : PowerSeries.coeff 0 (kingFlatPOPAboveGF 0) = 1 from
    ⟨h, kingFlatPOPAboveGF_zero_eq_rename ▸ h⟩
  classical
  rw [kingFlatPOPAboveGF, PowerSeries.coeff_mk,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMinCount, permRightToLeftMinCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun ⟨f, _⟩ => (f 0).elim0⟩
  · intro σ _ hσ
    exact (hσ (Subsingleton.elim σ 1)).elim

-- In one-based notation these are 53142 and its value complement 13524.
private def σ : Equiv.Perm (Fin 5) :=
  ⟨![4, 2, 0, 3, 1], ![2, 4, 1, 3, 0], by decide, by decide⟩

private def τ : Equiv.Perm (Fin 5) := σ.trans Fin.revPerm

example : IsKingPerm σ ∧ IsKingPerm τ := by
  unfold IsKingPerm
  decide

-- Unequal ascent/descent and left/right counts distinguish complement from position reversal.
example : permAscentCount σ = 1 ∧ permDescentCount σ = 3 ∧
    permLeftToRightMaxCount σ = 1 ∧ permRightToLeftMaxCount σ = 3 ∧
    permAscentCount τ = 3 ∧ permDescentCount τ = 1 ∧
    permLeftToRightMinCount τ = 1 ∧ permRightToLeftMinCount τ = 3 := by
  decide

-- A four-position subsequence starts either at position 0 (the maximum of σ) or
-- at position 1 with position 2 (the minimum of σ) next. For τ the extrema are opposite.
example : ¬ ContainsFlatPOPBelow σ 0 ∧ ¬ ContainsFlatPOPAbove τ 0 := by
  have h₀ : ∀ i, ¬ σ 0 < σ i ∧ ¬ τ i < τ 0 := by decide
  have h₂ : ∀ i, ¬ σ i < σ 2 ∧ ¬ τ 2 < τ i := by decide
  have obstruction (f : Fin 4 ↪o Fin 5) :
      ¬ σ (f 0) < σ (f 1) ∧ ¬ τ (f 1) < τ (f 0) := by
    by_cases h : (f 0 : ℕ) = 0
    · rw [show f 0 = 0 from Fin.ext h]
      exact h₀ _
    · have ha : (f 0 : ℕ) < f 1 := f.strictMono (by decide : (0 : Fin 4) < 1)
      have hb : (f 1 : ℕ) < f 2 := f.strictMono (by decide : (1 : Fin 4) < 2)
      have hc : (f 2 : ℕ) < f 3 := f.strictMono (by decide : (2 : Fin 4) < 3)
      have hd := (f 3).isLt
      rw [show f 1 = 2 from Fin.ext (by omega)]
      exact h₂ _
  constructor
  · rintro ⟨f, hf⟩
    exact (obstruction f).1 (hf 1 (by decide))
  · rintro ⟨f, hf⟩
    exact (obstruction f).2 (hf 1 (by decide))

end MetaMathlibExt
