/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopolesGenusBounds

open MetaMathlibExt Equiv.Perm

private theorem cycleCount_finRotate {n : ℕ} (hn : 2 ≤ n) :
    cycleQuotientCount (finRotate n) = 1 := by
  rw [cycleQuotientCount_eq, card_fixedPoints, Fintype.card_fin, cycleType_finRotate_of_le hn]
  simp

private theorem cycleCount_inv {n : ℕ} (π : Equiv.Perm (Fin n)) :
    cycleQuotientCount π⁻¹ = cycleQuotientCount π := by
  simp only [cycleQuotientCount_eq, card_fixedPoints, cycleType_inv]

-- The inverse rotation on three points attains the genus-one lower bound.
example : 2 * 1 + 1 ≤ 3 ∧ 3 ≤ 4 * 1 := by
  let σ := finRotate 3
  have hσ : cycleQuotientCount σ = 1 := cycleCount_finRotate (by decide)
  have hα : cycleQuotientCount σ⁻¹ = 1 := (cycleCount_inv σ).trans hσ
  have hface : (σ⁻¹)⁻¹ * σ = σ⁻¹ := Equiv.ext (by decide)
  exact genus_bounds_of_reduced_unicellular_hypermonopole σ σ⁻¹ hσ
    (by rw [hface, hα]) (by decide) (by rw [hσ, hα, hface, hα])

-- Two disjoint transpositions on four points attain the genus-one upper bound.
example : 2 * 1 + 1 ≤ 4 ∧ 4 ≤ 4 * 1 := by
  let σ := finRotate 4
  let α : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  have hσ : cycleQuotientCount σ = 1 := cycleCount_finRotate (by decide)
  have hα : cycleQuotientCount α = 2 := by
    have ht : α.cycleType = {2, 2} := cycleType_swap_mul_swap_of_nodup (by decide)
    rw [cycleQuotientCount_eq, card_fixedPoints, Fintype.card_fin, ht]
    decide
  have hface : α⁻¹ * σ = σ⁻¹ := Equiv.ext (by decide)
  have hfaceCount : cycleQuotientCount (α⁻¹ * σ) = 1 := by rw [hface, cycleCount_inv, hσ]
  exact genus_bounds_of_reduced_unicellular_hypermonopole σ α hσ hfaceCount
    (by decide) (by rw [hσ, hα, hfaceCount])
