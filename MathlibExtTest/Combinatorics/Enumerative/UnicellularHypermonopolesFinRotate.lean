/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.UnicellularHypermonopolesFinRotate

open MetaMathlibExt

-- On three points exactly one permutation with one cycle leaves a single face.
example : Fintype.card {α : Equiv.Perm (Fin 3) //
    cycleQuotientCount (α⁻¹ * finRotate 3) = 1 ∧ cycleQuotientCount α = 1} = 1 := by
  rw [card_unicellular_hypermonopoles_finRotate]
  decide

-- The value `H(4, 2) = 5` from the table of the source.
example : Fintype.card {α : Equiv.Perm (Fin 4) //
    cycleQuotientCount (α⁻¹ * finRotate 4) = 1 ∧ cycleQuotientCount α = 2} = 5 := by
  rw [card_unicellular_hypermonopoles_finRotate]
  decide

-- On five points the counts add up to the `4! = 24` permutations with one cycle.
example : ∑ k ∈ Finset.range 6, Fintype.card {α : Equiv.Perm (Fin 5) //
    cycleQuotientCount (α⁻¹ * finRotate 5) = 1 ∧ cycleQuotientCount α = k} = 24 := by
  simp only [card_unicellular_hypermonopoles_finRotate]
  decide

-- With `n ≥ 1` points only the identity has `n` cycles, and it leaves a single face.
example (n : ℕ) (hn : 1 ≤ n) : Fintype.card {α : Equiv.Perm (Fin n) //
    cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ cycleQuotientCount α = n} = 1 := by
  rw [card_unicellular_hypermonopoles_finRotate, cyclicProductNumber,
    ite_eq_left ⟨n, rfl⟩, Nat.stirlingFirst_succ_self_left,
    Nat.div_self (Nat.choose_pos (by omega))]

-- The number of cycles has the parity of the number of points.
example : Fintype.card {α : Equiv.Perm (Fin 4) //
    cycleQuotientCount (α⁻¹ * finRotate 4) = 1 ∧ cycleQuotientCount α = 1} = 0 := by
  rw [card_unicellular_hypermonopoles_finRotate]
  decide

-- At size zero no permutation leaves a single face, whatever `k` is.
example (k : ℕ) : Fintype.card {α : Equiv.Perm (Fin 0) //
    cycleQuotientCount (α⁻¹ * finRotate 0) = 1 ∧ cycleQuotientCount α = k} = 0 := by
  rw [card_unicellular_hypermonopoles_finRotate]
  simp [cyclicProductNumber]

-- More cycles than points: the count vanishes even when `n + k` is even.
example : Fintype.card {α : Equiv.Perm (Fin 3) //
    cycleQuotientCount (α⁻¹ * finRotate 3) = 1 ∧ cycleQuotientCount α = 5} = 0 := by
  rw [card_unicellular_hypermonopoles_finRotate]
  decide

open Polynomial

-- The generating identity includes the convention at size zero.
example : ∑ k ∈ Finset.range 1, C (cyclicProductNumber 0 k : ℚ) * X ^ k = 0 := by
  rw [sum_cyclicProductNumber_mul_X_pow 0]
  simp

-- At size three only the odd powers occur, with coefficients 1 and 1.
example : C (((3 + 1 : ℚ) * 3)⁻¹) * (ascPochhammer ℚ 4 - descPochhammer ℚ 4) = X + X ^ 3 := by
  have hpoly := (sum_cyclicProductNumber_mul_X_pow 3).symm
  simp only [Nat.cast_ofNat, Nat.reduceAdd] at hpoly
  rw [hpoly]
  have h : cyclicProductNumber 3 0 = 0 ∧ cyclicProductNumber 3 1 = 1 ∧
      cyclicProductNumber 3 2 = 0 ∧ cyclicProductNumber 3 3 = 1 := by decide
  simp [Finset.sum_range_succ, h.1, h.2.1, h.2.2.1, h.2.2.2]

-- At size four only the positive even powers occur, with coefficients 5 and 1.
example : C (((4 + 1 : ℚ) * 4)⁻¹) * (ascPochhammer ℚ 5 - descPochhammer ℚ 5) =
    5 * X ^ 2 + X ^ 4 := by
  have hpoly := (sum_cyclicProductNumber_mul_X_pow 4).symm
  simp only [Nat.cast_ofNat, Nat.reduceAdd] at hpoly
  rw [hpoly]
  have h : cyclicProductNumber 4 0 = 0 ∧ cyclicProductNumber 4 1 = 0 ∧
      cyclicProductNumber 4 2 = 5 ∧ cyclicProductNumber 4 3 = 0 ∧
      cyclicProductNumber 4 4 = 1 := by decide
  simp [Finset.sum_range_succ, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]
