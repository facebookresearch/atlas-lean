/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.MvPowerSeries.CoefficientOperator
import Mathlib.Algebra.Polynomial.Derivation

/-! # Tests for formal coefficient operators -/

open MvPowerSeries

example (i : Fin 2) : coeff (Finsupp.single i 1)
    (coefficientOperator (fun _ : Fin 2 => LinearMap.id : Fin 2 → ℚ →ₗ[ℚ] ℚ) (C 2)) = 2 := by
  classical
  simp

example : constantCoeff
    (coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 2)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

example (i : Fin 2) : coeff (Finsupp.single i 1)
    ((coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))^[2] (C 2)) = 0 :=
  coeff_iterate_coefficientOperator_eq_zero _ _ (by simp [Finsupp.degree_single])

example (i : ℕ) : coeff (Finsupp.single i 1)
    (coefficientOperator (fun j : ℕ => (j + 1 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (C 1)) =
      (i + 1 : ℚ) := by
  classical
  simp

example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    ((coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))^[2] (C 2)) = 4 := by
  classical
  change coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (coefficientOperator _ (coefficientOperator _ (C 2))) = 4
  rw [coeff_coefficientOperator]
  have hs : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1).support = {0, 1} := by
    simp [Finsupp.support_add_eq_union]
  rw [hs]
  norm_num

example (i : Fin 2) : coeff (Finsupp.single i 1)
    (coefficientOperator (fun _ : Fin 2 => (Polynomial.derivative' (R := ℚ)).toLinearMap)
      (C (Polynomial.X ^ 2))) = 2 * (Polynomial.X : Polynomial ℚ) := by
  classical
  norm_num [Polynomial.derivative'_apply, Polynomial.C_ofNat]

example (f : MvPowerSeries (Fin 2) ℚ) :
    coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) f =
      (∑ i : Fin 2, (X i : MvPowerSeries (Fin 2) ℚ)) * f := by
  classical
  ext d
  rw [coeff_coefficientOperator_eq_sum _ f (Finset.subset_univ _)]
  have h : id (α := MvPowerSeries (Fin 2) ℚ)
      ((LinearMap.id : ℚ →ₗ[ℚ] ℚ).compLeft ((Fin 2) →₀ ℕ) f) = f := rfl
  rw [h, Finset.sum_mul]

section SourceBridges

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

-- The source's two function-valued constructors are exactly the canonical maps.
example (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    coefficientOperator O f = fun d =>
      ∑ i ∈ d.support, O i (coeff (d - Finsupp.single i 1) f) := by
  ext d
  exact coeff_coefficientOperator O f d

example (D : A →ₗ[ℚ] A) (f : MvPowerSeries σ A) :
    D.compLeft (σ →₀ ℕ) f = fun d => D (coeff d f) := rfl

-- The source's Low property is exactly the natural order lower bound.
example (n : ℕ) (f : MvPowerSeries σ A) :
    (∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0) ↔ (n : ℕ∞) ≤ f.order := by
  constructor
  · exact nat_le_order
  · intro h d hd
    exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)

example (D : Derivation ℚ A A) (a b : A) :
    D.toLinearMap (a * b) = a * D.toLinearMap b + D.toLinearMap a * b := by
  change D (a * b) = a * D b + D a * b
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b]

example (O : σ → A →ₗ[ℚ] A) (f g : MvPowerSeries σ A) (q : ℚ) :
    coefficientOperator O (q • f + g) = q • coefficientOperator O f +
      coefficientOperator O g := by
  rw [map_add, map_smul]

example (O : Empty → A →ₗ[ℚ] A) : coefficientOperator O = 0 := by
  ext f d
  have hd : d = 0 := by
    ext i
    exact isEmptyElim i
  subst d
  simp

example : coefficientOperator (fun _ : σ => (0 : A →ₗ[ℚ] A)) = 0 := by
  ext f d
  simp

example {i j : ℕ} {f g : MvPowerSeries σ A}
    (hf : ∀ d : σ →₀ ℕ, d.degree < i → coeff d f = 0)
    (hg : ∀ d : σ →₀ ℕ, d.degree < j → coeff d g = 0) :
    ∀ d : σ →₀ ℕ, d.degree < i + j → coeff d (f * g) = 0 := by
  have horder := (add_le_add (nat_le_order hf) (nat_le_order hg)).trans le_order_mul
  intro d hd
  exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) horder)

end SourceBridges

private noncomputable def polynomialDerivations (i : Fin 2) :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  if i = 0 then Polynomial.derivative' else
    (Polynomial.X : Polynomial ℚ) • (Polynomial.derivative' (R := ℚ))

-- These two coefficient derivations do not commute.
example : polynomialDerivations 0 (polynomialDerivations 1 Polynomial.X) = 1 := by
  simp [polynomialDerivations, Derivation.smul_apply, Polynomial.derivative'_apply,
    smul_eq_mul]

example : polynomialDerivations 1 (polynomialDerivations 0 Polynomial.X) = 0 := by
  simp [polynomialDerivations, Polynomial.derivative'_apply]


-- The product rule applies to this noncommuting family on nonconstant coefficients.
example : coefficientOperator (fun i => (polynomialDerivations i).toLinearMap)
    ((C Polynomial.X : MvPowerSeries (Fin 2) (Polynomial ℚ)) * C Polynomial.X) =
      C Polynomial.X * coefficientOperator
        (fun i => (polynomialDerivations i).toLinearMap) (C Polynomial.X) +
      coefficientOperator (fun i => (polynomialDerivations i).toLinearMap)
        (C Polynomial.X) * C Polynomial.X :=
  coefficientOperator_mul polynomialDerivations _ _

example : coeff (Finsupp.single (1 : Fin 2) 1)
    (coefficientOperator (fun i => (polynomialDerivations i).toLinearMap)
      (C (Polynomial.X ^ 2))) = 2 * (Polynomial.X : Polynomial ℚ) ^ 2 := by
  classical
  norm_num [polynomialDerivations, Polynomial.derivative'_apply, Polynomial.C_ofNat,
    Derivation.smul_apply, smul_eq_mul]
  ring

example : pderiv (0 : Fin 2)
    (coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (X 0 * X 1)) =
      coefficientOperator (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) (X 1) + X 0 * X 1 := by
  have h : pderiv (0 : Fin 2) (X 0 * X 1 : MvPowerSeries (Fin 2) ℚ) = X 1 := by
    simp [Derivation.leibniz, smul_eq_mul]
  rw [pderiv_coefficientOperator, h]
  rfl

example (i : ℕ) :
    (Polynomial.derivative' (R := ℚ)).toLinearMap.compLeft (ℕ →₀ ℕ)
        (coefficientOperator (fun _ : ℕ => (Polynomial.derivative' (R := ℚ)).toLinearMap)
          (C (Polynomial.X ^ 2))) =
      coefficientOperator (fun _ : ℕ => (Polynomial.derivative' (R := ℚ)).toLinearMap)
        ((Polynomial.derivative' (R := ℚ)).toLinearMap.compLeft (ℕ →₀ ℕ)
          (C (Polynomial.X ^ 2))) :=
  compLeft_coefficientOperator
    (O := fun _ : ℕ => (Polynomial.derivative' (R := ℚ)).toLinearMap)
    (fun _ _ _ => rfl) i _

example : pderiv (0 : ℕ)
    ((Polynomial.derivative' (R := ℚ)).toLinearMap.compLeft (ℕ →₀ ℕ)
      (monomial (Finsupp.single (0 : ℕ) 2) (Polynomial.X ^ 2))) =
    (Polynomial.derivative' (R := ℚ)).toLinearMap.compLeft (ℕ →₀ ℕ)
      (pderiv (0 : ℕ) (monomial (Finsupp.single (0 : ℕ) 2) (Polynomial.X ^ 2))) :=
  pderiv_compLeft _ _ _

example : (3 : ℕ∞) ≤ (coefficientOperator
    (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    (monomial (Finsupp.single (0 : Fin 2) 2) 1)).order := by
  apply add_one_le_order_coefficientOperator (n := 2)
  rw [order_monomial_of_ne_zero (by norm_num), Finsupp.degree_single]

example : (4 : ℕ∞) ≤ ((coefficientOperator
    (fun _ : Fin 2 => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)))^[2]
    (monomial (Finsupp.single (0 : Fin 2) 2) 1)).order := by
  apply add_le_order_iterate_coefficientOperator _ (d := 2) (n := 2)
  rw [order_monomial_of_ne_zero (by norm_num), Finsupp.degree_single]
