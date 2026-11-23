/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.

Modifications adapt GeneralPieces/GenF/Taylor.lean from anthropics/formal-math,
commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5, to canonical linear maps.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.CoefficientOperator

/-! # The formal exponential of a coefficient operator

Each coefficient uses a finite exponential sum because the operator raises total degree.
The coefficient maps need not commute, and the variable family may be infinite.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

/-- The first `N` operator iterates, `∑ n < N, 𝒪ⁿ / n!`, acting on the full input series. -/
noncomputable def expOperatorPartial (O : σ → A →ₗ[ℚ] A) (N : ℕ) :
    MvPowerSeries σ A →ₗ[ℚ] MvPowerSeries σ A :=
  ∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ • coefficientOperator O ^ n

/-- The finite exponential sum agrees with the source's function-iterate formula. -/
theorem expOperatorPartial_apply (O : σ → A →ₗ[ℚ] A) (N : ℕ)
    (f : MvPowerSeries σ A) :
    expOperatorPartial O N f =
      ∑ n ∈ Finset.range N, (n.factorial : ℚ)⁻¹ • (coefficientOperator O)^[n] f := by
  simp [expOperatorPartial, LinearMap.sum_apply, Module.End.coe_pow]

/-- The formal exponential: coefficient `d` uses operator iterates `n ≤ d.degree`. -/
noncomputable def expOperator (O : σ → A →ₗ[ℚ] A) :
    MvPowerSeries σ A →ₗ[ℚ] MvPowerSeries σ A :=
  LinearMap.pi fun d => (LinearMap.proj d).comp (expOperatorPartial O (d.degree + 1))

/-- The defining iteration bound is exactly the source constructor's bound. -/
@[simp] theorem coeff_expOperator_def (O : σ → A →ₗ[ℚ] A)
    (f : MvPowerSeries σ A) (d : σ →₀ ℕ) :
    coeff d (expOperator O f) = coeff d (expOperatorPartial O (d.degree + 1) f) := rfl

/-- For `d.degree < N`, the first `N` operator iterates determine coefficient `d`. -/
theorem coeff_expOperator (O : σ → A →ₗ[ℚ] A) (f : MvPowerSeries σ A)
    {d : σ →₀ ℕ} {N : ℕ} (hd : d.degree < N) :
    coeff d (expOperator O f) = coeff d (expOperatorPartial O N f) := by
  classical
  rw [coeff_expOperator_def, expOperatorPartial_apply, expOperatorPartial_apply]
  rw [map_sum, map_sum]
  apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
  intro n _ hn
  have hz := coeff_iterate_coefficientOperator_eq_zero O f
    (d := d) (n := n) (by simpa using hn)
  change (n.factorial : ℚ)⁻¹ • coeff d ((coefficientOperator O)^[n] f) = 0
  rw [hz, smul_zero]

/-- The formal exponential preserves every constant coefficient, including nonzero ones. -/
@[simp] theorem constantCoeff_expOperator (O : σ → A →ₗ[ℚ] A)
    (f : MvPowerSeries σ A) : constantCoeff (expOperator O f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_expOperator_def]
  simp [expOperatorPartial_apply]

/-- If the second operator iterate vanishes on `f`, its exponential is `f + 𝒪 f`. -/
theorem expOperator_of_sq_zero (O : σ → A →ₗ[ℚ] A) {f : MvPowerSeries σ A}
    (hf : coefficientOperator O (coefficientOperator O f) = 0) :
    expOperator O f = f + coefficientOperator O f := by
  classical
  have hz (n : ℕ) : (coefficientOperator O)^[n + 2] f = 0 := by
    rw [← Module.End.coe_pow]
    exact Module.End.pow_map_zero_of_le (k := 2) (by omega) hf
  ext d
  rw [coeff_expOperator O f (N := d.degree + 2) (by omega), expOperatorPartial_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_eq_zero (fun n _ => by rw [hz, smul_zero])]
  simp [add_comm]

/-- The exponential fixes an input annihilated by the coefficient operator. -/
theorem expOperator_of_zero (O : σ → A →ₗ[ℚ] A) {f : MvPowerSeries σ A}
    (hf : coefficientOperator O f = 0) : expOperator O f = f := by
  rw [expOperator_of_sq_zero O (by rw [hf, map_zero]), hf, add_zero]

/-- The exponential of the zero coefficient-map family is the identity linear map. -/
@[simp] theorem expOperator_zero_family :
    expOperator (fun _ : σ => (0 : A →ₗ[ℚ] A)) = LinearMap.id := by
  ext f d
  have hf : coefficientOperator (fun _ : σ => (0 : A →ₗ[ℚ] A)) f = 0 := by
    ext e
    simp
  rw [expOperator_of_zero _ hf]
  rfl

end MvPowerSeries
