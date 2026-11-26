/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.GaloisField
import MathlibExt.FieldTheory.Finite.PowerSumCriterion

/-!
# Tests for the finite-field power-sum criterion
-/

namespace MetaMathlibExt.PowerSumCriterionTest

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- In the smallest field the only lower moment is the zeroth, including the zero entry.
example :
    let a := (Fintype.equivFin (ZMod 2)).symm
    (∑ i, a i ^ (0 : ℕ)) = 0 ∧ (∑ i, a i ^ (1 : ℕ)) = -1 := by
  let e := (Fintype.equivFin (ZMod 2)).symm
  obtain ⟨hlower, htop⟩ := (injective_iff_sum_pow_eq e).mp e.injective
  exact ⟨hlower 0 (by simp [ZMod.card]), by simpa [ZMod.card] using htop⟩

-- Compute the moments directly for a reordered enumeration of the field with three elements.
example : Function.Injective
    ((![2, 0, 1] : Fin 3 → ZMod 3) ∘ finCongr (ZMod.card 3)) := by
  let b : Fin 3 → ZMod 3 := ![2, 0, 1]
  let e := finCongr (ZMod.card 3)
  apply (injective_iff_sum_pow_eq (b ∘ e)).mpr
  have hsum (t : ℕ) : (∑ i, (b ∘ e) i ^ t) = ∑ i, b i ^ t :=
    e.sum_comp (fun i => b i ^ t)
  constructor
  · intro t ht
    rw [ZMod.card] at ht
    have h : t = 0 ∨ t = 1 := by omega
    rcases h with rfl | rfl <;> rw [hsum] <;> decide
  · rw [hsum, ZMod.card]
    decide

noncomputable local instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

-- The endpoint uses the field size four, not the characteristic two.
example :
    let a := (Fintype.equivFin (GaloisField 2 2)).symm
    (∀ t : ℕ, t < 3 → ∑ i, a i ^ t = 0) ∧ (∑ i, a i ^ (3 : ℕ)) = -1 := by
  let e := (Fintype.equivFin (GaloisField 2 2)).symm
  have hcard : Fintype.card (GaloisField 2 2) - 1 = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
    decide
  simpa only [hcard] using (injective_iff_sum_pow_eq e).mp e.injective

end MetaMathlibExt.PowerSumCriterionTest
