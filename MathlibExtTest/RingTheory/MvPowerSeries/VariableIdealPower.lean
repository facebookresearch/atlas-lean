/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.VariableIdealPower

@[expose] public section

universe u v

open MvPowerSeries

/-- Consumer with the original binders. -/
example {σ : Type u} {R : Type v} [Finite σ] [CommRing R] (k : ℕ)
    (φ : MvPowerSeries σ R)
    (hφ : ∀ m : σ →₀ ℕ, m.degree < k → MvPowerSeries.coeff m φ = 0) :
    φ ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ k :=
  MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero k φ hφ

/-- Higher-universe consumer. -/
example {σ : Type (u + 1)} {R : Type (v + 1)} [Finite σ] [CommRing R] (k : ℕ)
    (φ : MvPowerSeries σ R)
    (hφ : ∀ m : σ →₀ ℕ, m.degree < k → MvPowerSeries.coeff m φ = 0) :
    φ ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ k :=
  MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero k φ hφ

/-- Boundary: the constant series `1` does not satisfy the hypothesis at
`k = 1`, since its degree-zero coefficient is nonzero. -/
example : ¬ (∀ m : Fin 1 →₀ ℕ, m.degree < 1 →
    MvPowerSeries.coeff m (1 : MvPowerSeries (Fin 1) ℤ) = 0) := by
  intro h
  have h0 := h 0 (by simp)
  simp at h0
