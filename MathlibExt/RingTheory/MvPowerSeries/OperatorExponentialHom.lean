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
commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5, to canonical derivations and
the lawful zero-constant formal exponential.
-/
module

public import MathlibExt.RingTheory.Derivation.IteratedLeibniz
public import MathlibExt.RingTheory.MvPowerSeries.ExponentialHom
public import MathlibExt.RingTheory.MvPowerSeries.OperatorExponential

/-! # The coefficient-operator exponential as a ring homomorphism

When each coefficient map is a derivation, the coefficient operator is itself a
derivation. Its formal exponential is therefore multiplicative, without any
commutation assumption on the family and without requiring finitely many variables.
-/

@[expose] public section

namespace MvPowerSeries

open Finset

variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

/-- The coefficient operator packaged as the derivation supplied by its product law. -/
private noncomputable def coefficientOperatorDerivation
    (D : σ → Derivation ℚ A A) :
    Derivation ℚ (MvPowerSeries σ A) (MvPowerSeries σ A) :=
  Derivation.mk' (coefficientOperator fun i => (D i).toLinearMap) fun f g => by
    simpa only [smul_eq_mul, mul_comm] using coefficientOperator_mul D f g

private theorem sum_triangle {M : Type*} [AddCommMonoid M] (N : ℕ)
    (F : ℕ → ℕ → M) (h : ∀ i j, N ≤ i + j → F i j = 0) :
    ∑ n ∈ range N, ∑ p ∈ antidiagonal n, F p.1 p.2 =
      ∑ i ∈ range N, ∑ j ∈ range N, F i j := by
  rw [← sum_product' (range N) (range N) F]
  have hfilter : ∑ p ∈ range N ×ˢ range N, F p.1 p.2 =
      ∑ p ∈ (range N ×ˢ range N) with p.1 + p.2 < N, F p.1 p.2 := by
    rw [sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rfl
    · exact h p.1 p.2 (by omega)
  rw [hfilter, ← sum_fiberwise_of_maps_to (t := range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2)
    (fun p hp => mem_range.2 (mem_filter.1 hp).2)]
  refine sum_congr rfl fun n hn => sum_congr ?_ fun _ _ => rfl
  have hn' := mem_range.1 hn
  ext p
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_range]
  omega

omit [Algebra ℚ A] in
private theorem coeff_mul_congr_degree {f f' g g' : MvPowerSeries σ A}
    {d : σ →₀ ℕ}
    (hf : ∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e f = coeff e f')
    (hg : ∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e g = coeff e g') :
    coeff d (f * g) = coeff d (f' * g') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine sum_congr rfl fun p hp => ?_
  have hdegree := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at hdegree
  rw [hf p.1 (by omega), hg p.2 (by omega)]

private theorem coeff_iterate_mul_iterate_eq_zero (O : σ → A →ₗ[ℚ] A)
    (f g : MvPowerSeries σ A) {d : σ →₀ ℕ} {i j : ℕ}
    (hd : d.degree < i + j) :
    coeff d ((coefficientOperator O)^[i] f * (coefficientOperator O)^[j] g) = 0 := by
  classical
  rw [coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  have hdegree := congrArg Finsupp.degree (mem_antidiagonal.1 hp)
  rw [map_add] at hdegree
  by_cases hi : p.1.degree < i
  · rw [coeff_iterate_coefficientOperator_eq_zero O f hi, zero_mul]
  · rw [coeff_iterate_coefficientOperator_eq_zero O g (by omega), mul_zero]

/-- The formal exponential of a family of coefficient derivations preserves products.
No pairwise commutation or finiteness hypothesis on the family is needed. -/
theorem expOperator_mul (D : σ → Derivation ℚ A A) (f g : MvPowerSeries σ A) :
    expOperator (fun i => (D i).toLinearMap) (f * g) =
      expOperator (fun i => (D i).toLinearMap) f *
        expOperator (fun i => (D i).toLinearMap) g := by
  classical
  let O : σ → A →ₗ[ℚ] A := fun i => (D i).toLinearMap
  let Δ := coefficientOperatorDerivation D
  ext d
  change coeff d (expOperator O (f * g)) =
    coeff d (expOperator O f * expOperator O g)
  rw [coeff_mul_congr_degree
    (f' := expOperatorPartial O (d.degree + 1) f)
    (g' := expOperatorPartial O (d.degree + 1) g)
    (fun e he => coeff_expOperator O f (by omega))
    (fun e he => coeff_expOperator O g (by omega)),
    coeff_expOperator_def, expOperatorPartial_apply, expOperatorPartial_apply,
    expOperatorPartial_apply]
  rw [sum_mul_sum, map_sum, map_sum]
  have hiterate (n : ℕ) :
      (n.factorial : ℚ)⁻¹ • (coefficientOperator O)^[n] (f * g) =
        ∑ p ∈ antidiagonal n,
          ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) •
            ((coefficientOperator O)^[p.1] f *
              (coefficientOperator O)^[p.2] g) := by
    simpa only [O, Δ, coefficientOperatorDerivation, Derivation.coe_mk'] using
      Δ.iterate_mul_div n f g
  simp only [hiterate, map_sum, smul_mul_smul_comm]
  refine sum_triangle (d.degree + 1)
    (fun i j => coeff d (((i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹) •
      ((coefficientOperator O)^[i] f * (coefficientOperator O)^[j] g))) ?_
  intro i j hij
  rw [map_rat_smul, coeff_iterate_mul_iterate_eq_zero O f g (by omega), smul_zero]

/-- The formal exponential of a family of coefficient derivations preserves one. -/
@[simp] theorem expOperator_one (D : σ → Derivation ℚ A A) :
    expOperator (fun i => (D i).toLinearMap) (1 : MvPowerSeries σ A) = 1 := by
  apply expOperator_of_zero
  simpa only [coefficientOperatorDerivation, Derivation.coe_mk'] using
    (coefficientOperatorDerivation D).map_one_eq_zero

/-- The formal exponential of coefficient derivations as a ring endomorphism. -/
noncomputable def expOperatorHom (D : σ → Derivation ℚ A A) :
    MvPowerSeries σ A →+* MvPowerSeries σ A where
  toFun := expOperator fun i => (D i).toLinearMap
  map_one' := expOperator_one D
  map_mul' := expOperator_mul D
  map_zero' := map_zero _
  map_add' := map_add _

/-- Applying the operator-exponential ring homomorphism is the existing formal operator
exponential. -/
@[simp] theorem expOperatorHom_apply (D : σ → Derivation ℚ A A)
    (f : MvPowerSeries σ A) :
    expOperatorHom D f = expOperator (fun i => (D i).toLinearMap) f := rfl

/-- A coefficient of the operator exponential depends only on input coefficients of no
greater total degree. -/
theorem coeff_expOperator_congr (O : σ → A →ₗ[ℚ] A) (d : σ →₀ ℕ)
    (f g : MvPowerSeries σ A)
    (h : ∀ e : σ →₀ ℕ, e.degree ≤ d.degree → coeff e f = coeff e g) :
    coeff d (expOperator O f) = coeff d (expOperator O g) := by
  have horder : (((d.degree + 1 : ℕ) : ℕ∞) ≤ (f - g).order) := by
    apply nat_le_order
    intro e he
    rw [map_sub, h e (by omega), sub_self]
  have hzero : coeff d (expOperator O (f - g)) = 0 := by
    rw [coeff_expOperator_def, expOperatorPartial_apply, map_sum]
    apply sum_eq_zero
    intro n hn
    rw [map_rat_smul]
    have hiter := add_le_order_iterate_coefficientOperator O horder n
    rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast
      (show d.degree < d.degree + 1 + n by omega)) hiter), smul_zero]
  have hfg : f = (f - g) + g := (sub_add_cancel f g).symm
  rw [hfg, map_add, map_add, hzero, zero_add]

/-- The operator exponential commutes with the lawful ordinary formal exponential. -/
theorem expOperator_expOfConstantCoeffZero (D : σ → Derivation ℚ A A)
    {w : MvPowerSeries σ A} (hw : constantCoeff w = 0) :
    expOperator (fun i => (D i).toLinearMap) (expOfConstantCoeffZero w hw) =
      expOfConstantCoeffZero (expOperator (fun i => (D i).toLinearMap) w)
        (by rw [constantCoeff_expOperator, hw]) := by
  exact hom_expOfConstantCoeffZero (expOperatorHom D)
    (coeff_expOperator_congr fun i => (D i).toLinearMap) hw

end MvPowerSeries
