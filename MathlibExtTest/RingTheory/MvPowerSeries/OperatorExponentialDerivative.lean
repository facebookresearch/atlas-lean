/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.MvPowerSeries.OperatorExponentialDerivative
import Mathlib.Algebra.Polynomial.Derivation

/-! # Clients for derivatives of formal coefficient-operator exponentials -/

open MvPowerSeries

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

example {O : σ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : σ) (n : ℕ) (f : MvPowerSeries σ A) :
    (O i).compLeft (σ →₀ ℕ) ((coefficientOperator O)^[n] f) =
      (coefficientOperator O)^[n] ((O i).compLeft (σ →₀ ℕ) f) :=
  compLeft_iterate_coefficientOperator hc i n f

example {O : σ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : σ) (n : ℕ) (f : MvPowerSeries σ A) :
    pderiv i ((coefficientOperator O)^[n + 1] f) =
      (coefficientOperator O)^[n + 1] (pderiv i f) +
        (n + 1) • (coefficientOperator O)^[n] ((O i).compLeft (σ →₀ ℕ) f) :=
  pderiv_iterate_coefficientOperator hc i n f

example {O : σ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : σ) (N : ℕ) (f : MvPowerSeries σ A) :
    pderiv i (expOperatorPartial O (N + 1) f) =
      expOperatorPartial O (N + 1) (pderiv i f) +
        expOperatorPartial O N ((O i).compLeft (σ →₀ ℕ) f) :=
  pderiv_expOperatorPartial hc i N f

example {O : σ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : σ) (f : MvPowerSeries σ A) :
    pderiv i (expOperator O f) =
      expOperator O (pderiv i f) +
        expOperator O ((O i).compLeft (σ →₀ ℕ) f) :=
  pderiv_expOperator hc i f

example {D : σ → Derivation ℚ A A} (hc : ∀ i j a, D i (D j a) = D j (D i a))
    (i : σ) (f : MvPowerSeries σ A) :
    pderiv i (expOperator (fun j => (D j).toLinearMap) f) =
      expOperator (fun j => (D j).toLinearMap) (pderiv i f) +
        expOperator (fun j => (D j).toLinearMap)
          ((D i).toLinearMap.compLeft (σ →₀ ℕ) f) :=
  pderiv_expOperator_derivation hc i f

-- The first genuinely higher case has three differentiated operator factors.
example {O : σ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : σ) (f : MvPowerSeries σ A) :
    pderiv i ((coefficientOperator O)^[3] f) =
      (coefficientOperator O)^[3] (pderiv i f) +
        3 • (coefficientOperator O)^[2] ((O i).compLeft (σ →₀ ℕ) f) := by
  simpa using pderiv_iterate_coefficientOperator hc i 2 f

-- At `N = 0`, the correction partial sum is empty.
example {O : σ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : σ) (f : MvPowerSeries σ A) :
    pderiv i (expOperatorPartial O 1 f) =
      expOperatorPartial O 1 (pderiv i f) +
        expOperatorPartial O 0 ((O i).compLeft (σ →₀ ℕ) f) := by
  simpa using pderiv_expOperatorPartial hc i 0 f

-- The result does not require a finite variable family.
example {O : ℕ → A →ₗ[ℚ] A} (hc : ∀ i j a, O i (O j a) = O j (O i a))
    (i : ℕ) (f : MvPowerSeries ℕ A) :
    pderiv i (expOperator O f) =
      expOperator O (pderiv i f) +
        expOperator O ((O i).compLeft (ℕ →₀ ℕ) f) :=
  pderiv_expOperator hc i f

section RationalMaps

private noncomputable def scaledOperators (i : Fin 2) : ℚ →ₗ[ℚ] ℚ :=
  if i = 0 then LinearMap.id else 2 • LinearMap.id

private theorem scaledOperators_commute (i j : Fin 2) (a : ℚ) :
    scaledOperators i (scaledOperators j a) =
      scaledOperators j (scaledOperators i a) := by
  fin_cases i <;> fin_cases j <;> simp [scaledOperators]

-- The input has nonzero constant coefficient, so the gradient law has no hidden zero premise.
example : constantCoeff (pderiv 0 (expOperator scaledOperators (C 3))) = 3 := by
  rw [pderiv_expOperator scaledOperators_commute]
  simp only [pderiv_C, map_zero, zero_add]
  let g : MvPowerSeries (Fin 2) ℚ :=
    (scaledOperators 0).compLeft (Fin 2 →₀ ℕ) (C 3)
  change constantCoeff (expOperator scaledOperators g) = 3
  rw [constantCoeff_expOperator]
  change scaledOperators 0 3 = 3
  norm_num [scaledOperators]

example : constantCoeff (pderiv 1 (expOperator scaledOperators (C 3))) = 6 := by
  rw [pderiv_expOperator scaledOperators_commute]
  simp only [pderiv_C, map_zero, zero_add]
  let g : MvPowerSeries (Fin 2) ℚ :=
    (scaledOperators 1).compLeft (Fin 2 →₀ ℕ) (C 3)
  change constantCoeff (expOperator scaledOperators g) = 6
  rw [constantCoeff_expOperator]
  change scaledOperators 1 3 = 6
  norm_num [scaledOperators]

private theorem sub_scaled_first (n m : ℕ) :
    (Finsupp.single (0 : Fin 2) (n + 1) + Finsupp.single 1 m) -
        Finsupp.single 0 1 =
      Finsupp.single 0 n + Finsupp.single 1 m := by
  ext i
  fin_cases i <;> simp

private theorem sub_scaled_second (n m : ℕ) :
    (Finsupp.single (0 : Fin 2) n + Finsupp.single 1 (m + 1)) -
        Finsupp.single 1 1 =
      Finsupp.single 0 n + Finsupp.single 1 m := by
  ext i
  fin_cases i <;> simp

private theorem mixed_add_first :
    Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 + Finsupp.single 0 1 =
      Finsupp.single 0 2 + Finsupp.single 1 1 := by
  ext i
  fin_cases i <;> simp

private theorem mixed_add_second :
    Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 + Finsupp.single 1 1 =
      Finsupp.single 0 1 + Finsupp.single 1 2 := by
  ext i
  fin_cases i <;> simp

example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (pderiv 0 (expOperator scaledOperators (C 3))) = 6 := by
  rw [coeff_pderiv, mixed_add_first, coeff_expOperator_def,
    expOperatorPartial_apply]
  norm_num [Function.iterate_succ_apply', coeff_coefficientOperator, scaledOperators,
    Finset.sum_range_succ, Finsupp.support_add_eq_union, sub_scaled_first,
    sub_scaled_second, ← Finsupp.single_tsub, coeff_C, coeff_one, Nat.factorial]

example : coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)
    (pderiv 1 (expOperator scaledOperators (C 3))) = 12 := by
  rw [coeff_pderiv, mixed_add_second, coeff_expOperator_def,
    expOperatorPartial_apply]
  norm_num [Function.iterate_succ_apply', coeff_coefficientOperator, scaledOperators,
    Finset.sum_range_succ, Finsupp.support_add_eq_union, sub_scaled_first,
    sub_scaled_second, ← Finsupp.single_tsub, coeff_C, coeff_one, Nat.factorial]

end RationalMaps

section PolynomialDerivations

private noncomputable def polynomialDerivations (i : Fin 2) :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  if i = 0 then Polynomial.derivative' else 2 • Polynomial.derivative'

private theorem polynomialDerivations_commute (i j : Fin 2) (p : Polynomial ℚ) :
    polynomialDerivations i (polynomialDerivations j p) =
      polynomialDerivations j (polynomialDerivations i p) := by
  fin_cases i <;> fin_cases j <;>
    simp [polynomialDerivations, Derivation.smul_apply, Polynomial.derivative'_apply]

example : constantCoeff (pderiv 0
    (expOperator (fun i => (polynomialDerivations i).toLinearMap) (C Polynomial.X))) =
      1 := by
  rw [pderiv_expOperator_derivation polynomialDerivations_commute]
  simp only [pderiv_C, map_zero, zero_add]
  let g : MvPowerSeries (Fin 2) (Polynomial ℚ) :=
    (polynomialDerivations 0).toLinearMap.compLeft (Fin 2 →₀ ℕ) (C Polynomial.X)
  change constantCoeff
    (expOperator (fun i => (polynomialDerivations i).toLinearMap) g) = 1
  rw [constantCoeff_expOperator]
  change polynomialDerivations 0 Polynomial.X = 1
  simp [polynomialDerivations, Polynomial.derivative'_apply]

example : constantCoeff (pderiv 1
    (expOperator (fun i => (polynomialDerivations i).toLinearMap) (C Polynomial.X))) =
      2 := by
  rw [pderiv_expOperator_derivation polynomialDerivations_commute]
  simp only [pderiv_C, map_zero, zero_add]
  let g : MvPowerSeries (Fin 2) (Polynomial ℚ) :=
    (polynomialDerivations 1).toLinearMap.compLeft (Fin 2 →₀ ℕ) (C Polynomial.X)
  change constantCoeff
    (expOperator (fun i => (polynomialDerivations i).toLinearMap) g) = 2
  rw [constantCoeff_expOperator]
  change polynomialDerivations 1 Polynomial.X = 2
  norm_num [polynomialDerivations, Derivation.smul_apply, Polynomial.derivative'_apply]

private noncomputable def noncommutingPolynomialDerivations (i : Fin 2) :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  if i = 0 then Polynomial.derivative' else
    (Polynomial.X : Polynomial ℚ) • Polynomial.derivative'

example : noncommutingPolynomialDerivations 0
    (noncommutingPolynomialDerivations 1 Polynomial.X) = 1 := by
  simp [noncommutingPolynomialDerivations, Derivation.smul_apply,
    Polynomial.derivative'_apply, smul_eq_mul]

example : noncommutingPolynomialDerivations 1
    (noncommutingPolynomialDerivations 0 Polynomial.X) = 0 := by
  simp [noncommutingPolynomialDerivations, Polynomial.derivative'_apply]

end PolynomialDerivations
