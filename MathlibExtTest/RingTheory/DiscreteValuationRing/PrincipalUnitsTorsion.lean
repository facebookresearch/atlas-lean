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

/-- Consumer with the original binders: if `Ideal.span {(n : R)} = maximalIdeal R ^ e`,
`e < k`, `ζ ∈ principalUnits R k` and `ζ ^ n = 1`, then `ζ = 1`. -/
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

/-- Sharpness: the statement fails once `e < k` is weakened to `e ≤ k`. In `ℤ_[2]` take
`n = 2`, so `Ideal.span {(2 : ℤ_[2])} = maximalIdeal ℤ_[2] ^ 1` and `e = 1`, and `ζ = -1`:
`(-1) ^ 2 = 1` and `-1 - 1 = -2`, so `-1 ∈ principalUnits ℤ_[2] 1` and `k = 1`, but `-1 ≠ 1`. -/
example : ¬ ∀ {n e k : ℕ} {ζ : ℤ_[2]ˣ}, Ideal.span {(n : ℤ_[2])} = maximalIdeal ℤ_[2] ^ e →
    e ≤ k → ζ ∈ principalUnits ℤ_[2] k → ζ ^ n = 1 → ζ = 1 := by
  intro h
  have hspan : Ideal.span {((2 : ℕ) : ℤ_[2])} = maximalIdeal ℤ_[2] ^ 1 := by
    rw [pow_one, PadicInt.maximalIdeal_eq_span_p]
  have hmem : (-1 : ℤ_[2]ˣ) ∈ principalUnits ℤ_[2] 1 := by
    rw [mem_principalUnits_iff, pow_one, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
    exact ⟨-1, by push_cast; ring⟩
  have hne : (-1 : ℤ_[2]ˣ) ≠ 1 := by
    intro h1
    have hval := congrArg Units.val h1
    simp only [Units.val_neg, Units.val_one] at hval
    have h2 : ((2 : ℕ) : ℤ_[2]) = 0 := by
      push_cast
      linear_combination -hval
    exact absurd h2 (Nat.cast_ne_zero.mpr (by norm_num))
  exact hne (h hspan le_rfl hmem (by simp))
