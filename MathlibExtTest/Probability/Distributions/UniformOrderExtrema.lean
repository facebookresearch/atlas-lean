/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.UniformOrderExtrema

/-! # Tests for extrema of uniform random orders -/

open MeasureTheory MeasureTheory.Measure MetaMathlibExt
open scoped ENNReal

private abbrev pair : Finset (Fin 3) := {0, 2}
private abbrev a : Fin 3 := 0
private abbrev b : Fin 3 := 2

private abbrev transport := orderMinFibersEquiv (β := Fin 3) (s := pair)
  (x := a) (y := b) (by decide) (by decide)

private def minAtA : {σ : Fin 3 ≃ Fin 3 // ∀ z ∈ pair, z ≠ a → σ a < σ z} :=
  ⟨Equiv.swap 0 1, by decide⟩

-- The input ranks are [1, 0, 2]; swapping the two domain positions produces [2, 0, 1].
-- In particular the rank at the position outside the subset is unchanged.
private theorem transport_forward : (transport minAtA).1 0 = 2 ∧
    (transport minAtA).1 1 = 0 ∧ (transport minAtA).1 2 = 1 := by decide

private def minAtB : {σ : Fin 3 ≃ Fin 3 // ∀ z ∈ pair, z ≠ b → σ b < σ z} :=
  ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), by decide⟩

-- A separate input to the inverse has ranks [1, 2, 0].
private theorem transport_backward : (transport.symm minAtB).1 0 = 0 ∧
    (transport.symm minAtB).1 1 = 2 ∧ (transport.symm minAtB).1 2 = 1 := by decide

local instance : MeasurableSpace (Fin 3 ≃ Fin 3) := ⊤

private theorem pair_minimum : uniformOfFinset (Finset.univ : Finset (Fin 3 ≃ Fin 3))
    {σ | ∀ y ∈ pair, y ≠ a → σ a < σ y} = (2 : ℝ≥0∞)⁻¹ := by
  have hc : pair.card = 2 := by decide
  simpa only [hc, Nat.cast_ofNat] using
    (uniformOfFinset_orderMin_eq (β := Fin 3) rfl (s := pair) (x := a) (by decide))

private theorem pair_maximum : uniformOfFinset (Finset.univ : Finset (Fin 3 ≃ Fin 3))
    {σ | ∀ y ∈ pair, y ≠ a → σ y < σ a} = (2 : ℝ≥0∞)⁻¹ := by
  have hc : pair.card = 2 := by decide
  simpa only [hc, Nat.cast_ofNat] using
    (uniformOfFinset_orderMax_eq (β := Fin 3) rfl (s := pair) (x := a) (by decide))

-- For a singleton, the strict comparison excludes its only member, so the event is the whole space.
private theorem singleton_minimum : uniformOfFinset (Finset.univ : Finset (Fin 3 ≃ Fin 3))
    {σ | ∀ y ∈ ({1} : Finset (Fin 3)), y ≠ 1 → σ 1 < σ y} = 1 := by
  classical
  rw [uniformOfFinset_apply]
  simp [ENNReal.div_self]
