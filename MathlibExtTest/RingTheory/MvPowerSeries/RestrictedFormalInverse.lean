/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.RestrictedFormalInverse

@[expose] public section

universe u

open MvPowerSeries

/-- Consumer with the original binders. -/
example {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ}
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvPowerSeries.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
      (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hJ : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), 2 ≤ m.degree →
      ((m j : ℕ) : 𝓞) * (φ i).coeff m ∈ Ideal.span {(p : 𝓞)})
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
    (χ : Fin d → MvPolynomial (Fin d) 𝓞)
    (hχ0 : ∀ i, MvPolynomial.constantCoeff (χ i) = 0)
    (hχ : ∀ (i : Fin d) (m : Fin d →₀ ℕ),
      (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) (φ i)).coeff m -
        (X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) :
    ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
      (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N} :=
  MvPowerSeries.eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod
    p φ ψ hφ0 hφ1 hφT hJ hψφ χ hχ0 hχ

/-- Higher-universe consumer for the coefficient ring. -/
example {𝓞 : Type (u + 1)} [CommRing 𝓞] (p : ℕ) {d : ℕ}
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvPowerSeries.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
      (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hJ : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), 2 ≤ m.degree →
      ((m j : ℕ) : 𝓞) * (φ i).coeff m ∈ Ideal.span {(p : 𝓞)})
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
    (χ : Fin d → MvPolynomial (Fin d) 𝓞)
    (hχ0 : ∀ i, MvPolynomial.constantCoeff (χ i) = 0)
    (hχ : ∀ (i : Fin d) (m : Fin d →₀ ℕ),
      (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) (φ i)).coeff m -
        (X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) :
    ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite,
      (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N} :=
  MvPowerSeries.eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod
    p φ ψ hφ0 hφ1 hφT hJ hψφ χ hχ0 hχ

/-- The linear part of the variable family is the identity matrix. -/
example {R : Type*} [CommRing R] {d : ℕ} :
    MvPowerSeries.linearPart (fun i => (X i : MvPowerSeries (Fin d) R)) = 1 := by
  ext i j
  rw [MvPowerSeries.linearPart_apply, coeff_index_single_X]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]
