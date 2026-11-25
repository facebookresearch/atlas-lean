/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.InitialFormEval
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

open IsLocalRing MvPowerSeries

universe u v

-- Consumer with the original binders, restating the conclusion with the
-- explicit finite sum from the source.
example
    (W : Type u) [CommRing W] (M : Type v) [CommRing M] [IsLocalRing M]
    (Φ : MvPowerSeries (Fin 2) W →+* M) (ρ : W →+* M)
    (hC : ∀ w : W, Φ (MvPowerSeries.C w) = ρ w)
    (v α β : M) (p₀ p₁ : W)
    (hX0 : Φ (MvPowerSeries.X 0) = v * α) (hX1 : Φ (MvPowerSeries.X 1) = v * β)
    (hv : v ∈ maximalIdeal M)
    (hα : α - ρ p₀ ∈ maximalIdeal M) (hβ : β - ρ p₁ ∈ maximalIdeal M)
    (d : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W),
      MvPowerSeries.X 1}) ^ d) :
    ∃ r ∈ maximalIdeal M,
      Φ g = v ^ d * (ρ (∑ i ∈ Finset.range (d + 1),
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
          Finsupp.single (1 : Fin 2) (d - i)) g * p₀ ^ i * p₁ ^ (d - i)) + r) := by
  obtain ⟨r, hr, h⟩ :=
    MvPowerSeries.exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul
      W M Φ ρ hC v α β p₀ p₁ hX0 hX1 hv hα hβ d g hg
  exact ⟨r, hr, by rwa [MvPowerSeries.initialForm_eq_sum] at h⟩

-- Higher-universe consumer: coefficient ring in `Type 1`, target in `Type 2`.
example
    (W : Type 1) [CommRing W] (M : Type 2) [CommRing M] [IsLocalRing M]
    (Φ : MvPowerSeries (Fin 2) W →+* M) (ρ : W →+* M)
    (hC : ∀ w : W, Φ (MvPowerSeries.C w) = ρ w)
    (v α β : M) (p₀ p₁ : W)
    (hX0 : Φ (MvPowerSeries.X 0) = v * α) (hX1 : Φ (MvPowerSeries.X 1) = v * β)
    (hv : v ∈ maximalIdeal M)
    (hα : α - ρ p₀ ∈ maximalIdeal M) (hβ : β - ρ p₁ ∈ maximalIdeal M)
    (d : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W),
      MvPowerSeries.X 1}) ^ d) :
    ∃ r ∈ maximalIdeal M,
      Φ g = v ^ d * (ρ (MvPowerSeries.initialForm d g p₀ p₁) + r) :=
  MvPowerSeries.exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul
    W M Φ ρ hC v α β p₀ p₁ hX0 hX1 hv hα hβ d g hg

-- The membership hypothesis matters: for `g = 1` and `d = 1` over the field
-- `ℚ` with the constant-coefficient map, the conclusion would force `1 = 0`.
example :
    ¬ ∃ r ∈ maximalIdeal ℚ,
      MvPowerSeries.constantCoeff (1 : MvPowerSeries (Fin 2) ℚ) =
        (0 : ℚ) ^ 1 * (MvPowerSeries.initialForm 1 (1 : MvPowerSeries (Fin 2) ℚ) 0 0 + r) := by
  rintro ⟨r, hr, h⟩
  have hr0 : r = 0 := by
    have hmax : maximalIdeal ℚ = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hmax] at hr
    simpa using hr
  have h1 : (1 : ℚ) = 0 := by simpa [hr0] using h
  exact one_ne_zero h1
