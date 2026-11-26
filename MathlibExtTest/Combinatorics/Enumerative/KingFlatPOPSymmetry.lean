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

-- There is one empty permutation, which avoids the pattern vacuously and contributes 1.
example : PowerSeries.coeff 0 (kingFlatPOPAboveGF 1) = 1 ∧
    PowerSeries.coeff 0
      (PowerSeries.map (MvPolynomial.rename ⇑(Equiv.swap (0 : Fin 4) 1)).toRingHom
        (kingFlatPOPBelowGF 1)) = 1 := by
  suffices h : PowerSeries.coeff 0 (kingFlatPOPAboveGF 1) = 1 from
    ⟨h, kingFlatPOPAboveGF_one_eq_rename ▸ h⟩
  classical
  rw [kingFlatPOPAboveGF, PowerSeries.coeff_mk,
    Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
  · simp [permAscentCount, permDescentCount, permLeftToRightMinCount, permRightToLeftMinCount]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i => i.elim0, fun ⟨f, _⟩ => (f 0).elim0⟩
  · intro σ _ hσ
    exact (hσ (Subsingleton.elim σ 1)).elim

-- In one-based notation these are 13524 and its value complement 53142.
private def σ : Equiv.Perm (Fin 5) :=
  ⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩

private def τ : Equiv.Perm (Fin 5) := σ.trans Fin.revPerm

example : IsKingPerm σ ∧ IsKingPerm τ := by
  unfold IsKingPerm
  decide

-- Unequal ascent/descent and left/right counts distinguish the variable swap from reversal.
example : permAscentCount σ = 3 ∧ permDescentCount σ = 1 ∧
    permLeftToRightMaxCount σ = 3 ∧ permRightToLeftMaxCount σ = 2 ∧
    permAscentCount τ = 1 ∧ permDescentCount τ = 3 ∧
    permLeftToRightMinCount τ = 3 ∧ permRightToLeftMinCount τ = 2 := by
  decide

example : ¬ ContainsFlatPOPBelow σ 1 ∧ ¬ ContainsFlatPOPAbove τ 1 := by
  have second : ∀ f : Fin 4 ↪o Fin 5, (f 1 : ℕ) ≤ 2 := by
    intro f
    have h₁ : (f 1 : ℕ) < f 2 := f.strictMono (by decide : (1 : Fin 4) < 2)
    have h₂ : (f 2 : ℕ) < f 3 := f.strictMono (by decide : (2 : Fin 4) < 3)
    have h₃ := (f 3).isLt
    omega
  have firstTwo : ∀ a b : Fin 5, a < b → (b : ℕ) ≤ 2 → σ a < σ b ∧ τ b < τ a := by
    decide
  constructor
  · rintro ⟨f, hf⟩
    exact (firstTwo _ _ (f.strictMono (by decide)) (second f)).1.not_gt (hf 0 (by decide))
  · rintro ⟨f, hf⟩
    exact (firstTwo _ _ (f.strictMono (by decide)) (second f)).2.not_gt (hf 0 (by decide))

end MetaMathlibExt
