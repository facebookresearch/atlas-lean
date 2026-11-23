/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/PDeriv.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
use canonical coefficient lifting and formal coefficient-operator exponentials.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.OperatorExponential

/-! # Derivatives of formal coefficient-operator exponentials

Partial differentiation of an operator exponential splits into the derivative of the input
and the coefficientwise lift of the corresponding coefficient map. The coefficient maps need
only commute pairwise; they need not be derivations, and the variable family may be infinite.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

private theorem inv_cast_factorial_succ_mul (n : ℕ) :
    (((n + 1).factorial : ℚ)⁻¹) * ((n + 1 : ℕ) : ℚ) = (n.factorial : ℚ)⁻¹ := by
  rw [Nat.factorial_succ]
  push_cast
  have h : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ h, mul_one]

/-- A lifted coefficient map commutes with every coefficient-operator iterate when the
coefficient maps commute pairwise. -/
theorem compLeft_iterate_coefficientOperator {O : σ → A →ₗ[ℚ] A}
    (hc : ∀ i j a, O i (O j a) = O j (O i a)) (i : σ) (n : ℕ)
    (f : MvPowerSeries σ A) :
    (O i).compLeft (σ →₀ ℕ) ((coefficientOperator O)^[n] f) =
      (coefficientOperator O)^[n] ((O i).compLeft (σ →₀ ℕ) f) := by
  have hcomm : Function.Commute
      (fun g : MvPowerSeries σ A => (O i).compLeft (σ →₀ ℕ) g)
      (coefficientOperator O) :=
    fun g => compLeft_coefficientOperator hc i g
  exact hcomm.iterate_right n f

/-- The partial derivative of the `(n + 1)`st coefficient-operator iterate is the
iterate of the partial derivative plus `(n + 1)` copies of the lifted coefficient map. -/
theorem pderiv_iterate_coefficientOperator {O : σ → A →ₗ[ℚ] A}
    (hc : ∀ i j a, O i (O j a) = O j (O i a)) (i : σ) (n : ℕ)
    (f : MvPowerSeries σ A) :
    pderiv i ((coefficientOperator O)^[n + 1] f) =
      (coefficientOperator O)^[n + 1] (pderiv i f) +
        (n + 1) • (coefficientOperator O)^[n] ((O i).compLeft (σ →₀ ℕ) f) := by
  let g : MvPowerSeries σ A := (O i).compLeft (σ →₀ ℕ) f
  change pderiv i ((coefficientOperator O)^[n + 1] f) =
    (coefficientOperator O)^[n + 1] (pderiv i f) +
      (n + 1) • (coefficientOperator O)^[n] g
  induction n with
  | zero =>
    simpa [Function.iterate_one, Function.iterate_zero, g] using
      pderiv_coefficientOperator O i f
  | succ n ih =>
    rw [Function.iterate_succ_apply', pderiv_coefficientOperator, ih, map_add,
      map_nsmul, compLeft_iterate_coefficientOperator hc]
    rw [show ((O i).compLeft (σ →₀ ℕ) f : MvPowerSeries σ A) = g from rfl]
    simp only [id_eq]
    rw [
      ← Function.iterate_succ_apply' (coefficientOperator O),
      ← Function.iterate_succ_apply' (coefficientOperator O), add_assoc, ← succ_nsmul]

/-- The partial derivative of the first `N + 1` exponential terms is the corresponding
partial sum on the derivative plus the first `N` terms on the lifted coefficient map. -/
theorem pderiv_expOperatorPartial {O : σ → A →ₗ[ℚ] A}
    (hc : ∀ i j a, O i (O j a) = O j (O i a)) (i : σ) (N : ℕ)
    (f : MvPowerSeries σ A) :
    pderiv i (expOperatorPartial O (N + 1) f) =
      expOperatorPartial O (N + 1) (pderiv i f) +
        expOperatorPartial O N ((O i).compLeft (σ →₀ ℕ) f) := by
  let g : MvPowerSeries σ A := (O i).compLeft (σ →₀ ℕ) f
  change pderiv i (expOperatorPartial O (N + 1) f) =
    expOperatorPartial O (N + 1) (pderiv i f) + expOperatorPartial O N g
  rw [expOperatorPartial_apply, expOperatorPartial_apply, expOperatorPartial_apply]
  rw [Finset.sum_range_succ',
    Finset.sum_range_succ' (fun n => (n.factorial : ℚ)⁻¹ •
      (coefficientOperator O)^[n] (pderiv i f)), map_add, map_sum,
    add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    rw [Derivation.map_smul_of_tower, pderiv_iterate_coefficientOperator hc,
      smul_add, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    rw [show ((O i).compLeft (σ →₀ ℕ) f : MvPowerSeries σ A) = g from rfl,
      inv_cast_factorial_succ_mul]
  · rw [Derivation.map_smul_of_tower]
    rfl

/-- The partial derivative of a formal coefficient-operator exponential is the exponential
of the input derivative plus the exponential of the lifted coefficient map. -/
theorem pderiv_expOperator {O : σ → A →ₗ[ℚ] A}
    (hc : ∀ i j a, O i (O j a) = O j (O i a)) (i : σ)
    (f : MvPowerSeries σ A) :
    pderiv i (expOperator O f) =
      expOperator O (pderiv i f) +
        expOperator O ((O i).compLeft (σ →₀ ℕ) f) := by
  let g : MvPowerSeries σ A := (O i).compLeft (σ →₀ ℕ) f
  change pderiv i (expOperator O f) =
    expOperator O (pderiv i f) + expOperator O g
  ext d
  have hdegree : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  rw [coeff_pderiv,
    coeff_expOperator O f (N := d.degree + 2) (by rw [hdegree]; omega),
    ← coeff_pderiv, pderiv_expOperatorPartial hc, map_add, map_add,
    ← coeff_expOperator O _ (by omega)]
  rw [show ((O i).compLeft (σ →₀ ℕ) f : MvPowerSeries σ A) = g from rfl,
    ← coeff_expOperator O _ (by omega)]

/-- The exponential gradient law specialized to a pairwise commuting family of coefficient
derivations, using their canonical rational linear maps. -/
theorem pderiv_expOperator_derivation {D : σ → Derivation ℚ A A}
    (hc : ∀ i j a, D i (D j a) = D j (D i a)) (i : σ)
    (f : MvPowerSeries σ A) :
    pderiv i (expOperator (fun j => (D j).toLinearMap) f) =
      expOperator (fun j => (D j).toLinearMap) (pderiv i f) +
        expOperator (fun j => (D j).toLinearMap)
          ((D i).toLinearMap.compLeft (σ →₀ ℕ) f) :=
  pderiv_expOperator (O := fun j => (D j).toLinearMap) hc i f

end MvPowerSeries
