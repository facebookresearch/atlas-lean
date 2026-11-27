/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.CompactlySupported

import Mathlib.Tactic.FunProp

/-!
# Continuous Hilbert vectors are separated by their original compact scalar Haar tests

An open-positive measure finite on compact sets separates a continuous
Hilbert-valued function through its integrals against actual compact-support
complex scalar functions. A compact nonnegative bump and the positive part
of its original inner coefficient give a nonnegative scalar integral which
cannot vanish when the tested vector is nonzero.

No countability, sigma-finiteness, norm model or chosen integral inverse is
assumed. The statement applies to the original Haar vector integral and is
the kernel prerequisite of the full coefficient multiplier embedding.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set
open scoped CompactlySupported InnerProductSpace

noncomputable section

universe uX uH

variable {X : Type uX} [TopologicalSpace X] [RegularSpace X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- Let `X` be a regular locally compact space with its Borel σ-algebra, let `μ` be finite on
compact sets and positive on nonempty open sets, and let `H` be a complete complex inner-product
space. Assume `F : X → H` is continuous and every integral of `ψ(x) • F(x)` vanishes for a
compactly supported continuous complex test function `ψ`.

The compact scalar integrals recover every continuous Hilbert vector. -/
theorem Continuous.eq_zero_of_compactScalar_integrals_eq_zero
    {F : X → H} (hF : Continuous F) (x₀ : X)
    (hTest : ∀ ψ : C_c(X, ℂ), (∫ x : X, ψ x • F x ∂μ) = 0) : F x₀ = 0 := by
  by_contra hNonzero
  let w := F x₀
  let L : H →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ w).restrictScalars ℝ)
  have hL (v : H) : L v = Complex.re ⟪w, v⟫_ℂ := by
    change Complex.re (innerSL ℂ w v) = Complex.re ⟪w, v⟫_ℂ
    rw [innerSL_apply_apply]
  let p : X → ℝ := fun x => L (F x)
  have hpContinuous : Continuous p := L.continuous.comp hF
  have hpAt : p x₀ = ‖w‖ ^ 2 := by
    change L (F x₀) = ‖w‖ ^ 2
    rw [hL]
    change Complex.re ⟪w, w⟫_ℂ = ‖w‖ ^ 2
    rw [← RCLike.re_eq_complex_re]
    exact inner_self_eq_norm_sq w
  have hpPositive : 0 < p x₀ := by
    rw [hpAt]
    exact pow_pos (norm_pos_iff.mpr hNonzero) 2
  obtain ⟨φ, hφCompact, hφNonneg, hφAt⟩ := exists_continuous_nonneg_pos x₀
  let q : X → ℝ := fun x => φ x * max 0 (p x)
  have hqContinuous : Continuous q := by fun_prop
  have hqCompact : HasCompactSupport q := hφCompact.mul_right
  let ψ : C_c(X, ℂ) :=
    { toFun x := (q x : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp hqContinuous
      hasCompactSupport' := hqCompact.comp_left (g := Complex.ofReal) Complex.ofReal_zero }
  let r : X → ℝ := fun x => q x * p x
  have hrContinuous : Continuous r := by fun_prop
  have hrCompact : HasCompactSupport r := hqCompact.mul_right
  have hrNonneg : 0 ≤ r := by
    intro x
    by_cases hp : 0 ≤ p x
    · change 0 ≤ (φ x * max 0 (p x)) * p x
      rw [max_eq_right hp]
      exact mul_nonneg (mul_nonneg (hφNonneg x) hp) hp
    · change 0 ≤ (φ x * max 0 (p x)) * p x
      rw [max_eq_left (le_of_not_ge hp), mul_zero, zero_mul]
  have hrAt : r x₀ ≠ 0 := by
    change (φ x₀ * max 0 (p x₀)) * p x₀ ≠ 0
    rw [max_eq_right hpPositive.le]
    exact mul_ne_zero (mul_ne_zero hφAt hpPositive.ne') hpPositive.ne'
  have hPositive : 0 < ∫ x : X, r x ∂μ :=
    hrContinuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hrCompact hrNonneg hrAt
  have hWeightedContinuous : Continuous (fun x : X => ψ x • F x) := by fun_prop
  have hWeightedCompact : HasCompactSupport (fun x : X => ψ x • F x) := by
    apply HasCompactSupport.intro' ψ.hasCompactSupport (isClosed_tsupport ψ)
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hWeightedIntegrable : Integrable (fun x : X => ψ x • F x) μ :=
    hWeightedContinuous.integrable_of_hasCompactSupport hWeightedCompact
  have hValue (x : X) : L (ψ x • F x) = r x := by
    rw [hL]
    change Complex.re ⟪w, (q x : ℂ) • F x⟫_ℂ = q x * p x
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hL]
  have hZero : (∫ x : X, L (ψ x • F x) ∂μ) = 0 := by
    rw [L.integral_comp_comm hWeightedIntegrable, hTest ψ, map_zero]
  have hrZero : (∫ x : X, r x ∂μ) = 0 :=
    (integral_congr_ae (Eventually.of_forall hValue)).symm.trans hZero
  exact hPositive.ne' hrZero

end
