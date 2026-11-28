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

private def genusSet (g : ℕ) : Set (Σ n : ℕ, Equiv.Perm (Fin n)) :=
  {p | cycleQuotientCount (finRotate p.1) = 1 ∧
    cycleQuotientCount (p.2⁻¹ * finRotate p.1) = 1 ∧ (∀ i, p.2 i ≠ i) ∧
    p.1 + 2 = cycleQuotientCount (finRotate p.1) + cycleQuotientCount p.2 +
      cycleQuotientCount (p.2⁻¹ * finRotate p.1) + 2 * g}

-- The empty summation interval rules out genus-zero reduced unicellular hypermonopoles.
example : genusSet 0 = ∅ := by
  obtain ⟨hfinite, hcard⟩ := reduced_unicellular_hypermonopoles_of_genus_count 0
  exact (Set.ncard_eq_zero hfinite).mp (by simpa using hcard)

-- In genus one, the sum consists of the three-point and four-point fibers.
example : (genusSet 1).ncard =
    Fintype.card {α : Equiv.Perm (Fin 3) //
      cycleQuotientCount (α⁻¹ * finRotate 3) = 1 ∧ (∀ i, α i ≠ i) ∧ cycleQuotientCount α = 1} +
    Fintype.card {α : Equiv.Perm (Fin 4) //
      cycleQuotientCount (α⁻¹ * finRotate 4) = 1 ∧ (∀ i, α i ≠ i) ∧ cycleQuotientCount α = 2} := by
  have h := (reduced_unicellular_hypermonopoles_of_genus_count 1).2
  change (genusSet 1).ncard = ∑ n ∈ Finset.Icc 3 4,
    Fintype.card {α : Equiv.Perm (Fin n) //
      cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = n - 2} at h
  rw [show Finset.Icc (3 : ℕ) 4 = {3, 4} by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton] at h
  exact h
