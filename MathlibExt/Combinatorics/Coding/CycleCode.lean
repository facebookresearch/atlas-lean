/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.ZMod.Defs

/-!
# Independent modular cycle codes and their capacity

Two words are confusable exactly when every coordinate difference is `-1`, `0`, or `1`.
For positive odd moduli this is the strong-power cycle model. This file carries only the
generic-modulus API. The seven-cycle specialization (`IsC7Code`, the attained independence
number, and the `C₉` capacity supremum) lives with its OpenConjectures entry in
`OpenConjectures/Combinatorics/Green080CapSet/Helper/CycleCode.lean`; it was not promoted
into this reusable layer.

Source: Optimization Problems, constant 9a; the modular difference formulation is the
GREEN-080 source formulation. Known numerical and construction bounds are not assumed here.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- Positive block lengths. -/
abbrev PositiveNat := {n : ℕ // 1 ≤ n}

/-- The actual independent-code condition for a modular cycle. The source uses odd `q ≥ 7`. -/
def IsCycleCode (q : ℕ) {n : ℕ} (A : Finset (Fin n → ZMod q)) : Prop :=
  ∀ (x : Fin n → ZMod q),
    (∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ - a₂ = x) →
    (∀ i : Fin n, x i = -1 ∨ x i = 0 ∨ x i = 1) →
    x = 0

/-- A finite independent code in the modular strong-power model. -/
abbrev CycleCode (q n : ℕ) := {A : Finset (Fin n → ZMod q) // IsCycleCode q A}

/-- For a nonzero modulus, the code type at each fixed length is finite. -/
theorem cycleCode_finite (q n : ℕ) [NeZero q] : Finite (CycleCode q n) := by
  infer_instance

/-- The rate supplied by a concrete independent code. -/
noncomputable def cycleCodeRate (q : ℕ) (n : PositiveNat) (A : CycleCode q n.1) : ENNReal :=
  ENNReal.rpow (A.1.card : ENNReal) ((n.1 : ℝ)⁻¹)

/-- The supremum over all concrete positive-length independent-code rates. -/
noncomputable def shannonCapacityCycle (q : ℕ) : ENNReal :=
  ⨆ (n : PositiveNat) (A : CycleCode q n.1), cycleCodeRate q n A

/-- Every concrete code rate is at most its modular cycle capacity. -/
theorem cycleCodeRate_le_shannonCapacity (q : ℕ) (n : PositiveNat)
    (A : CycleCode q n.1) :
    cycleCodeRate q n A ≤ shannonCapacityCycle q :=
  le_iSup_of_le n (le_iSup (cycleCodeRate q n) A)

/-- An actual finite construction yields its corresponding root-rate lower bound. -/
theorem cycleConstruction_implies_lowerBound (q n M : ℕ) (hn : 1 ≤ n) :
    (∃ A : Finset (Fin n → ZMod q), IsCycleCode q A ∧ A.card = M) →
      ENNReal.rpow (M : ENNReal) ((n : ℝ)⁻¹) ≤ shannonCapacityCycle q := by
  rintro ⟨A, hA, rfl⟩
  simpa [cycleCodeRate] using
    cycleCodeRate_le_shannonCapacity q ⟨n, hn⟩ ⟨A, hA⟩

end MathlibExt.Combinatorics.Coding.CycleGraphCode
