/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.PrincipalUnitsTorsion
import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

open IsLocalRing

/-- Consumer with the original binders: a torsion principal unit of a
discrete valuation ring, deeper than the maximal-ideal exponent of its
order, is trivial. -/
example {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} {e : ℕ} (hne : Ideal.span {(n : R)} = maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {ζ : Rˣ} (hζ : ζ ∈ principalUnits R k)
    (hζn : ζ ^ n = 1) : ζ = 1 :=
  IsDiscreteValuationRing.eq_one_of_pow_eq_one_of_mem_principalUnits
    hne hk hζ hζn

/-- Higher-universe consumer of the same statement. -/
example {R : Type 1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} {e : ℕ} (hne : Ideal.span {(n : R)} = maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {ζ : Rˣ} (hζ : ζ ∈ principalUnits R k)
    (hζn : ζ ^ n = 1) : ζ = 1 :=
  IsDiscreteValuationRing.eq_one_of_pow_eq_one_of_mem_principalUnits
    hne hk hζ hζn

/-- Boundary: without the depth hypothesis `e < k` the conclusion fails.
In `ℤ_[2]` the unit `-1` satisfies `(-1) ^ 2 = 1` and lies in
`principalUnits ℤ_[2] 0 = ⊤`, but `-1 ≠ 1`. -/
example : (-1 : ℤ_[2]ˣ) ∈ principalUnits ℤ_[2] 0 ∧
    (-1 : ℤ_[2]ˣ) ^ 2 = 1 ∧ (-1 : ℤ_[2]ˣ) ≠ 1 := by
  refine ⟨?_, by simp, ?_⟩
  · rw [principalUnits_zero]
    exact Subgroup.mem_top _
  · intro h
    have hval := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at hval
    have h2 : ((2 : ℕ) : ℤ_[2]) = 0 := by
      push_cast
      linear_combination -hval
    exact absurd h2 (Nat.cast_ne_zero.mpr (by norm_num))
