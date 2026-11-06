/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0

Adapted from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/
S_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero.lean,
lines 23-30 and 96-198 (integrability, approximation and distributional proof).
The source NOTICE attributes the repository to Anthropic; no individual
file author is named for this solution in ATTRIBUTION.md.
The polynomial-basis argument is independently authored using Mathlib's
Polynomial.Sequence.basis, rather than copying the source recurrence proof.
-/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Complex L¹ uniqueness from Chebyshev-U moments

The moments here are unweighted angle integrals on `[0, π]`, not L²
coefficients for a Chebyshev measure. Continuity and the zero conclusion
are restricted to `(0, π)`. No endpoint regularity is required.
-/

open MeasureTheory Set Polynomial
open scoped ContDiff

namespace Polynomial.Chebyshev

private lemma integrable_mul_eval {g : ℝ → ℂ}
    (hgi : IntervalIntegrable g volume 0 Real.pi) (p : ℝ[X]) :
    IntervalIntegrable
      (fun θ => g θ * ((p.eval (Real.cos θ) : ℝ) : ℂ)) volume 0 Real.pi :=
  hgi.mul_continuousOn
    (Complex.continuous_ofReal.comp
      (p.continuous.comp Real.continuous_cos)).continuousOn

private lemma integral_mul_eval_eq_zero {g : ℝ → ℂ}
    (hgi : IntervalIntegrable g volume 0 Real.pi)
    (hmodes : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
      g θ * ((U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0)
    (p : ℝ[X]) :
    ∫ θ in (0 : ℝ)..Real.pi,
      g θ * ((p.eval (Real.cos θ) : ℝ) : ℂ) = 0 := by
  let L : ℝ[X] →ₗ[ℝ] ℂ :=
    { toFun := fun p => ∫ θ in (0 : ℝ)..Real.pi,
        g θ * ((p.eval (Real.cos θ) : ℝ) : ℂ)
      map_add' := fun p q => by
        simp only [eval_add, Complex.ofReal_add, mul_add]
        exact intervalIntegral.integral_add
          (integrable_mul_eval hgi p) (integrable_mul_eval hgi q)
      map_smul' := fun c p => by
        simp only [eval_smul, smul_eq_mul, Complex.ofReal_mul,
          RingHom.id_apply, Complex.real_smul]
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext θ
        ring }
  let S : Polynomial.Sequence ℝ :=
    { elems' := fun n => U ℝ n
      degree_eq' := degree_U_natCast ℝ }
  have hcoeff : ∀ n, IsUnit (S n).leadingCoeff := by
    intro n
    change IsUnit (U ℝ n).leadingCoeff
    rw [leadingCoeff_U_natCast]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hL : L = 0 := (S.basis hcoeff).ext fun n => by
    simpa only [Polynomial.Sequence.basis_eq_self, LinearMap.zero_apply,
      L, S, LinearMap.coe_mk, AddHom.coe_mk] using hmodes n
  exact congrArg (fun l : ℝ[X] →ₗ[ℝ] ℂ => l p) hL

private lemma norm_integral_mul_le {g : ℝ → ℂ}
    (hgi : IntervalIntegrable g volume 0 Real.pi) {ψ : ℝ → ℝ}
    {ε : ℝ} (hbound : ∀ θ ∈ Icc (0 : ℝ) Real.pi, |ψ θ| ≤ ε) :
    ‖∫ θ in (0 : ℝ)..Real.pi, g θ * (ψ θ : ℂ)‖ ≤
      ε * ∫ θ in (0 : ℝ)..Real.pi, ‖g θ‖ := by
  calc
    _ ≤ ∫ θ in (0 : ℝ)..Real.pi, ε * ‖g θ‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le Real.pi_pos.le
        _ (hgi.norm.const_mul ε)
      exact ae_of_all _ fun θ hθ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (hbound θ ⟨hθ.1.le, hθ.2⟩) (norm_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

private lemma integral_mul_continuous_eq_zero {g : ℝ → ℂ}
    (hgi : IntervalIntegrable g volume 0 Real.pi)
    (hmodes : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
      g θ * ((U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) = 0)
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Icc 0 Real.pi)) :
    ∫ θ in (0 : ℝ)..Real.pi, g θ * (ψ θ : ℂ) = 0 := by
  have hφ : ContinuousOn (fun x => ψ (Real.arccos x)) (Icc (-1) 1) :=
    hψ.comp Real.continuous_arccos.continuousOn
      (fun x _ => ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩)
  have hψi : IntervalIntegrable
      (fun θ => g θ * (ψ θ : ℂ)) volume 0 Real.pi :=
    hgi.mul_continuousOn (Complex.continuous_ofReal.comp_continuousOn
      (by simpa only [uIcc_of_le Real.pi_pos.le] using hψ))
  let Cg := ∫ θ in (0 : ℝ)..Real.pi, ‖g θ‖
  have hCg : 0 ≤ Cg :=
    intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => norm_nonneg _)
  apply norm_le_zero_iff.mp
  apply le_of_forall_pos_lt_add
  intro ε hε
  let δ := ε / (Cg + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    (-1) 1 (fun x => ψ (Real.arccos x)) hφ δ hδ
  have hdiff : (∫ θ in (0 : ℝ)..Real.pi, g θ * (ψ θ : ℂ)) =
      ∫ θ in (0 : ℝ)..Real.pi,
        g θ * ((ψ θ - p.eval (Real.cos θ) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub]
    rw [intervalIntegral.integral_sub hψi (integrable_mul_eval hgi p),
      integral_mul_eval_eq_zero hgi hmodes p, sub_zero]
  rw [hdiff]
  calc
    _ ≤ δ * Cg := norm_integral_mul_le hgi fun θ hθ => by
      have h := (hp (Real.cos θ)
        ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).le
      simpa only [Real.arccos_cos hθ.1 hθ.2, abs_sub_comm] using h
    _ < 0 + ε := by
      dsimp [δ]
      rw [zero_add, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- An interior-continuous complex L¹ function with every unweighted
Chebyshev-U angle moment zero vanishes on `(0, π)`.

This is the exact contract of FLT entry238, wrapper
`Thm_Polynomial_Chebyshev_eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero`.
The L¹ premise is with respect to real volume; neither endpoint continuity
nor square integrability is assumed. -/
public theorem eq_zero_on_Ioo_of_forall_intervalIntegral_mul_U_eq_zero
    (g : ℝ → ℂ) (hg : ContinuousOn g (Ioo 0 Real.pi))
    (hgi : IntervalIntegrable g volume 0 Real.pi)
    (hmodes : ∀ j : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
      g θ * (((U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) = 0) :
    ∀ θ ∈ Ioo (0 : ℝ) Real.pi, g θ = 0 := by
  have hli : LocallyIntegrableOn g (Ioo 0 Real.pi) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le Real.pi_pos.le).mp
      hgi).locallyIntegrableOn
  have htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 Real.pi → ∫ x, φ x • g x ∂volume = 0 := by
    intro φ hφ _ hsupp
    have hzero : ∀ x, x ∉ Ioc (0 : ℝ) Real.pi → φ x • g x = 0 := by
      intro x hx
      have hz : φ x = 0 := by
        by_contra hne
        exact hx (Ioo_subset_Ioc_self (hsupp (subset_tsupport _ hne)))
      rw [hz, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      ← intervalIntegral.integral_of_le Real.pi_pos.le]
    simpa only [Complex.real_smul, mul_comm] using
      integral_mul_continuous_eq_zero hgi hmodes hφ.continuous.continuousOn
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hli htest
  have hae' : g =ᵐ[volume.restrict (Ioo 0 Real.pi)] (fun _ => (0 : ℂ)) := by
    rwa [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  exact fun _ hθ =>
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hg continuousOn_const hθ

end Polynomial.Chebyshev
