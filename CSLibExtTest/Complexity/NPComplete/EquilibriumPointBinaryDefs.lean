/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EquilibriumPointBinaryDefs

namespace MetaMathlibExt.Complexity.NPComplete.EquilibriumPointBinary

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.GameTheory.StrategicGame (isNash_iff_update_le)
open EquilibriumPoint (EquilibriumPointInstance EquilibriumPointFeasible MonomialTerm Strategy game
  payoffPoly productPoly factorPoly assignment rangeSet)

/-- The range-set `{0, 1}`. -/
private abbrev binary : List (ℕ × ℕ) := [(0, 0), (1, 0)]

/-- The single factor `1 - x₀ - x₁ + 2 x₀ x₁`: `1` when `x₀ = x₁` and `0` otherwise on `{0, 1}`. -/
private abbrev agree : List MonomialTerm :=
  [((1, 0), []), ((0, 1), [0]), ((0, 1), [1]), ((2, 0), [0, 1])]

/-- The single factor `x₀ + x₁ - 2 x₀ x₁`: `1` when `x₀ ≠ x₁` and `0` otherwise on `{0, 1}`. -/
private abbrev differ : List MonomialTerm := [((1, 0), [0]), ((1, 0), [1]), ((0, 2), [0, 1])]

/-- A coordination game: both players are paid for matching. -/
private abbrev coordination : EquilibriumPointInstance := (2, [[agree], [agree]], [binary, binary])

/-- Matching pennies: player `0` is paid for matching, player `1` for differing. -/
private abbrev pennies : EquilibriumPointInstance := (2, [[agree], [differ]], [binary, binary])

private theorem pennies_mem (k : ℕ) (z : ℤ) (h : z ∈ rangeSet pennies k) : z = 0 ∨ z = 1 := by
  rcases k with _ | _ | k <;> simp [rangeSet] at h ⊢ <;> omega

private theorem coordination_mem (k : ℕ) (z : ℤ) (h : z ∈ rangeSet coordination k) :
    z = 0 ∨ z = 1 := by
  rcases k with _ | _ | k <;> simp [rangeSet] at h ⊢ <;> omega

private theorem pennies_payoff0 (hne : ∀ i, Nonempty (Strategy pennies i))
    (τ : ∀ i, Strategy pennies i) : (game pennies hne).payoff 0 τ =
      ((1 + (-(τ 0).1 + (-(τ 1).1 + 2 * ((τ 0).1 * (τ 1).1))) : ℤ) : ℝ) := by
  simp [game, payoffPoly, productPoly, factorPoly, assignment]

private theorem pennies_payoff1 (hne : ∀ i, Nonempty (Strategy pennies i))
    (τ : ∀ i, Strategy pennies i) : (game pennies hne).payoff 1 τ =
      (((τ 0).1 + ((τ 1).1 + -(2 * ((τ 0).1 * (τ 1).1)))  : ℤ) : ℝ) := by
  simp [game, payoffPoly, productPoly, factorPoly, assignment]

private theorem coordination_payoff0 (hne : ∀ i, Nonempty (Strategy coordination i))
    (τ : ∀ i, Strategy coordination i) : (game coordination hne).payoff 0 τ =
      ((1 + (-(τ 0).1 + (-(τ 1).1 + 2 * ((τ 0).1 * (τ 1).1))) : ℤ) : ℝ) := by
  simp [game, payoffPoly, productPoly, factorPoly, assignment]

private theorem coordination_payoff1 (hne : ∀ i, Nonempty (Strategy coordination i))
    (τ : ∀ i, Strategy coordination i) : (game coordination hne).payoff 1 τ =
      ((1 + (-(τ 0).1 + (-(τ 1).1 + 2 * ((τ 0).1 * (τ 1).1))) : ℤ) : ℝ) := by
  simp [game, payoffPoly, productPoly, factorPoly, assignment]

private theorem ne01 : (0 : Fin 2) ≠ 1 := by decide

/-- Matching pennies has no pure equilibrium: at a matching profile player `1` gains by
switching, and at a differing profile player `0` gains by switching. -/
private theorem pennies_infeasible : ¬ EquilibriumPointFeasible pennies := by
  rintro ⟨σ, hN⟩
  rw [isNash_iff_update_le] at hN
  rcases pennies_mem _ _ (σ 0).2 with h0 | h0 <;> rcases pennies_mem _ _ (σ 1).2 with h1 | h1
  · have := hN 1 ⟨1, by decide⟩
    rw [pennies_payoff1, pennies_payoff1, Function.update_self,
      Function.update_of_ne ne01, Int.cast_le] at this
    simp [h0, h1] at this
  · have := hN 0 ⟨1, by decide⟩
    rw [pennies_payoff0, pennies_payoff0, Function.update_self,
      Function.update_of_ne ne01.symm, Int.cast_le] at this
    simp [h0, h1] at this
  · have := hN 0 ⟨0, by decide⟩
    rw [pennies_payoff0, pennies_payoff0, Function.update_self,
      Function.update_of_ne ne01.symm, Int.cast_le] at this
    simp [h0, h1] at this
  · have := hN 1 ⟨0, by decide⟩
    rw [pennies_payoff1, pennies_payoff1, Function.update_self,
      Function.update_of_ne ne01, Int.cast_le] at this
    simp [h0, h1] at this

private theorem one_mem : ∀ k < 2, (1 : ℤ) ∈ rangeSet coordination k := by decide

/-- Both players choosing `1` is a pure equilibrium of the coordination game. -/
private theorem coordination_feasible : EquilibriumPointFeasible coordination := by
  refine ⟨fun i => ⟨1, one_mem i i.2⟩, ?_⟩
  rw [isNash_iff_update_le]
  intro i t
  have hi : i = 0 ∨ i = 1 := by
    rcases i with ⟨_ | _ | k, hk⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hk (by simp)
  rcases hi with rfl | rfl
  · rw [coordination_payoff0, coordination_payoff0, Function.update_self,
      Function.update_of_ne ne01.symm, Int.cast_le]
    rcases coordination_mem _ _ t.2 with ht | ht <;> simp [ht]
  · rw [coordination_payoff1, coordination_payoff1, Function.update_self,
      Function.update_of_ne ne01, Int.cast_le]
    rcases coordination_mem _ _ t.2 with ht | ht <;> simp [ht]

/-- Every range-set of a two-player instance with range-sets `binary` is `{0, 1}`. -/
private theorem binary_ranges (F : List (List (List MonomialTerm))) :
    ∀ i < 2, ∀ z : ℤ, z ∈ rangeSet ((2, F, [binary, binary]) : EquilibriumPointInstance) i ↔
      z = 0 ∨ z = 1 := by
  intro i hi z
  rcases i with _ | _ | k
  · simp [rangeSet]
  · simp [rangeSet]
  · omega

private theorem wellFormed_coordination : WellFormed coordination :=
  ⟨by unfold EquilibriumPoint.WellFormed; decide, binary_ranges _⟩

private theorem wellFormed_pennies : WellFormed pennies :=
  ⟨by unfold EquilibriumPoint.WellFormed; decide, binary_ranges _⟩

/-- The decision problem accepts the coordination game, with the equilibrium `(1, 1)`. -/
example : equilibriumPointBinaryDec (bitEncode coordination) = true := by
  simp [equilibriumPointBinaryDec, bitDecode_bitEncode, wellFormed_coordination,
    coordination_feasible]

/-- The decision problem rejects the well-formed matching-pennies instance. -/
example : WellFormed pennies ∧ equilibriumPointBinaryDec (bitEncode pennies) = false :=
  ⟨wellFormed_pennies,
    by simp [equilibriumPointBinaryDec, bitDecode_bitEncode, pennies_infeasible]⟩

/-- One player with payoff `x₀` and range-set `{0, 2}`. -/
private abbrev twoValued : EquilibriumPointInstance := (1, [[[((1, 0), [0])]]], [[(0, 0), (2, 0)]])

private theorem twoValued_mem (z : ℤ) (h : z ∈ rangeSet twoValued 0) : z = 0 ∨ z = 2 := by
  simpa [rangeSet] using h

private theorem twoValued_payoff (hne : ∀ i, Nonempty (Strategy twoValued i))
    (τ : ∀ i, Strategy twoValued i) : (game twoValued hne).payoff 0 τ = (((τ 0).1 : ℤ) : ℝ) := by
  simp [game, payoffPoly, productPoly, factorPoly, assignment]

/-- The binary range-sets matter: `twoValued` is a well-formed EQUILIBRIUM POINT instance with
the equilibrium `2`, yet this decision problem rejects it. -/
example :
    EquilibriumPoint.WellFormed twoValued ∧ EquilibriumPointFeasible twoValued ∧
      equilibriumPointBinaryDec (bitEncode twoValued) = false := by
  have hw : ¬ WellFormed twoValued := fun h => by
    have := (h.2 0 (by decide) 2).1 (by decide)
    simp at this
  have two_mem : ∀ k < 1, (2 : ℤ) ∈ rangeSet twoValued k := by decide
  refine ⟨by unfold EquilibriumPoint.WellFormed; decide, ⟨fun i => ⟨2, two_mem i i.2⟩, ?_⟩,
    by simp [equilibriumPointBinaryDec, bitDecode_bitEncode, hw]⟩
  rw [isNash_iff_update_le]
  intro i t
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [twoValued_payoff, twoValued_payoff, Function.update_self, Int.cast_le]
  rcases twoValued_mem _ t.2 with ht | ht <;> simp [ht]

/-- A lone continuation bit is a truncated instance encoding. -/
example : equilibriumPointBinaryDec [true] = false := by
  have h : bitDecode (α := EquilibriumPointInstance) [true] = none := rfl
  simp [equilibriumPointBinaryDec, h]

end MetaMathlibExt.Complexity.NPComplete.EquilibriumPointBinary
