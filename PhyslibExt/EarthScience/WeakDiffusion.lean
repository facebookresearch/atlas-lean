/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Weak solutions of steady diffusion on (0,1)

For bounded measurable `κ ≥ kmin > 0` and `f ∈ L²(0,1)`, the steady diffusion
problem `-(κ u')' = f` on `(0,1)`, `u(0) = u(1) = 0`, has a unique weak
solution in `H¹₀(0,1)`.

## i. Overview

`κ` is the diffusivity and `f` the source. The weak form of the problem asks
for `u ∈ H¹₀(0,1)` with `∫₀¹ κ u' v' = ∫₀¹ f v` for every `v ∈ H¹₀(0,1)`.
For `κ` a.e. strongly measurable with `0 < kmin ≤ κ ≤ kmax` a.e. on `[0,1]`
and `f ∈ L²(0,1)`, such a `u` exists and its values on `[0,1]` are unique.
There is no drift or zeroth-order term.

`H¹₀(0,1)` is encoded by the structure `WeakH10` (see its docstring): the
absolutely continuous representative on `[0,1]`, written as the primitive of
an `L²` weak derivative with zero integral. The Sobolev spaces of pinned
Mathlib (`TemperedDistribution.MemSobolev`) and Physlib
(`QuantumMechanics.SpaceDHilbertSpace.SobolevSubmodule`) live on the whole
space and are defined through the Fourier transform; neither provides `H¹₀`
of an interval.

Existence uses the explicit one-dimensional formula, obtained by integrating
the equation once. With `F x = ∫ t in 0..x, f t` and
`C = (∫ t in 0..1, F t / κ t) / (∫ t in 0..1, 1 / κ t)`, the weak derivative
`w = (C - F) / κ` is in `L²`, its integral over `[0,1]` is zero (this is the
choice of `C`, and it gives `u(1) = 0`), and it satisfies the weak equation
by integration by parts (`∫ F * v' = -∫ f * v`, with no boundary terms since
`v 0 = v 1 = 0`). Uniqueness: testing the difference of two solutions against
itself gives `∫ κ * (Δw)² = 0`, and `κ ≥ kmin > 0` forces `Δw = 0` a.e.,
hence agreement on `[0,1]` through the integral representations.

## ii. Key results

- `EarthScience.WeakH10`: the `H¹₀(0,1)` structure used by the statement.
- `EarthScience.weak_diffusion_exists_unique`: existence and uniqueness of
  the weak solution in `H¹₀(0,1)`.
- `EarthScience.weak_diffusion_ibp`: integration by parts for the primitive
  of an `L²` function against a `WeakH10` test function.

## iii. Table of contents

- A. The `H¹₀(0,1)` encoding
- B. Existence (explicit formula)
- C. Uniqueness (energy argument)
- D. Existence and uniqueness of the weak solution

## iv. References

- H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
  Equations*, Universitext, Springer, 2011, Chapter 8. §8.2 (the space
  `W^{1,p}(I)`) and §8.3 (the space `W₀^{1,p}(I)`) give the one-dimensional
  description that `WeakH10` encodes: a continuous representative whose
  increments are integrals of the weak derivative, vanishing at both
  endpoints for `W₀^{1,p}`. §8.4 solves Dirichlet problems through their
  variational formulation.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in
  Mathematics 19, American Mathematical Society, 2010, Chapter 6: weak
  solutions of second-order elliptic equations in divergence form (§6.1.2)
  and their existence through the Lax–Milgram theorem and energy estimates
  (§6.2).
- G. Grammel, *Homogenization of elliptic differential equations in
  one-dimensional spaces*, Abstract and Applied Analysis 2007, Article ID
  98538, Eqs. (2.4)–(2.5): for a measurable coefficient with
  `0 < α ≤ a ≤ β`, the one-dimensional equation is integrated once, the flux
  `ξ = a u'` being an affine function of a primitive of the forcing and `u`
  the primitive of `ξ / a`. Here `κ u' = C - F`.
- `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` in
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
  (Mathlib): integration by parts for absolutely continuous functions.

## A. The `H¹₀(0,1)` encoding
-/

@[expose] public section

namespace EarthScience

open MeasureTheory

/-- An element of `H¹₀(0,1)`, stored as its absolutely continuous
representative `toFun` on `[0,1]` together with a weak derivative
`weakDeriv ∈ L²(0,1)`.

In one dimension a function is in `H¹(0,1)` exactly when it has a continuous
representative that is a constant plus the primitive of an `L²(0,1)`
function, its weak derivative; it is in `H¹₀(0,1)` exactly when that
representative vanishes at both endpoints (Brezis, Chapter 8). The fields
encode this description:

- `toFun_eq_integral` makes `toFun` the primitive of `weakDeriv` on `[0,1]`,
  normalized by `toFun 0 = 0` (an empty integral). So `toFun` is absolutely
  continuous on `[0,1]`, vanishes at `0`, and `weakDeriv` plays the role of
  `u'`: it is the derivative of `toFun` at almost every point of `(0,1)`.
- `integral_weakDeriv_eq_zero` is the condition at the other endpoint: by
  `toFun_eq_integral` at `x = 1`, `toFun 1 = ∫₀¹ weakDeriv`, so the field
  says exactly `toFun 1 = 0`.

Values of `toFun` and `weakDeriv` outside `[0,1]` are unconstrained and do
not enter `weak_diffusion_exists_unique`, which reads `toFun` only on `[0,1]`
and `weakDeriv` only through integrals over `[0,1]`. -/
structure WeakH10 where
  /-- The absolutely continuous representative, meaningful on `[0,1]`. -/
  toFun : ℝ → ℝ
  /-- The weak derivative, an `L²` function on `[0,1]`. -/
  weakDeriv : ℝ → ℝ
  /-- The weak derivative is square integrable on `[0,1]`. -/
  weakDeriv_memLp :
    MemLp weakDeriv 2 (volume.restrict (Set.Icc 0 1))
  /-- On `[0,1]`, `toFun` is the primitive of `weakDeriv` starting from `0`. -/
  toFun_eq_integral :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, toFun x = ∫ t in (0 : ℝ)..x, weakDeriv t
  /-- The weak derivative has integral zero over `[0,1]`, which is the
  boundary condition `toFun 1 = 0`. -/
  integral_weakDeriv_eq_zero :
    ∫ t in (0 : ℝ)..1, weakDeriv t = 0

/-! ## B. Existence (explicit formula) -/

private lemma weak_diffusion_candidate
    {κ f : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1))) :
    ∃ w : ℝ → ℝ,
      MemLp w 2 (volume.restrict (Set.Icc 0 1))
      ∧ (∫ x in (0 : ℝ)..1, w x) = 0
      ∧ ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)),
          κ x * w x = (∫ t in (0 : ℝ)..1, (∫ s in (0 : ℝ)..t, f s) / κ t)
            / (∫ t in (0 : ℝ)..1, 1 / κ t)
            - ∫ s in (0 : ℝ)..x, f s := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hf_int : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.integrable (by norm_num)
  have hInteg_uIcc : IntegrableOn f (Set.uIcc (0 : ℝ) 1) volume := by
    rw [Set.uIcc_of_le h01]
    exact hf_int
  have hF_cont : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, f s) (Set.Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := (1 : ℝ))
      (μ := volume) (f := f) hInteg_uIcc
    rw [Set.uIcc_of_le h01] at h
    exact h
  have hF_meas : AEStronglyMeasurable (fun x => ∫ s in (0 : ℝ)..x, f s)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hF_cont.aestronglyMeasurable measurableSet_Icc
  have hM_nonneg : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume := by
    apply integral_nonneg_of_ae
    filter_upwards with s
    exact norm_nonneg _
  have hF_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖∫ s in (0 : ℝ)..x, f s‖ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume := by
    intro x hx
    calc ‖∫ s in (0 : ℝ)..x, f s‖
        ≤ ∫ s in Set.uIoc (0 : ℝ) x, ‖f s‖ ∂volume :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ s in Set.Ioc (0 : ℝ) x, ‖f s‖ ∂volume := by rw [Set.uIoc_of_le hx.1]
      _ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume := by
          refine setIntegral_mono_set hf_int.norm ?_ ?_
          · filter_upwards with s
            exact norm_nonneg _
          · exact Filter.Eventually.of_forall (fun _ hs => ⟨hs.1.le, le_trans hs.2 hx.2⟩)
  have hkmax : 0 < kmax := by
    have hmem : {x | kmin ≤ κ x ∧ κ x ≤ kmax} ∈
        ae (volume.restrict (Set.Icc (0 : ℝ) 1)) := hκ
    have hne : {x | kmin ≤ κ x ∧ κ x ≤ kmax} ≠ ∅ := by
      intro hempty
      have h0 := mem_ae_iff.mp hmem
      rw [hempty, Set.compl_empty, Measure.restrict_apply_univ, Real.volume_Icc] at h0
      rw [ENNReal.ofReal_eq_zero] at h0
      norm_num at h0
    obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hx0' : kmin ≤ κ x0 ∧ κ x0 ≤ kmax := hx0
    exact lt_of_lt_of_le hkmin (le_trans hx0'.1 hx0'.2)
  have hκinv_meas : AEStronglyMeasurable (fun x => 1 / κ x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    aestronglyMeasurable_const.div₀ hκ_meas
  have hκinv_bound : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖(1 : ℝ) / κ x‖ ≤ 1 / kmin := by
    filter_upwards [hκ] with x hx
    have hκpos : (0 : ℝ) < κ x := lt_of_lt_of_le hkmin hx.1
    rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hκpos]
    exact one_div_le_one_div_of_le hkmin hx.1
  have hκinv_int : Integrable (fun x => 1 / κ x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    Integrable.of_bound hκinv_meas (1 / kmin) hκinv_bound
  have hFκ_meas : AEStronglyMeasurable (fun x => (∫ s in (0 : ℝ)..x, f s) / κ x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hF_meas.div₀ hκ_meas
  have hFκ_bound : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖(∫ s in (0 : ℝ)..x, f s) / κ x‖
        ≤ (∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) / kmin := by
    filter_upwards [hκ, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    have hκpos : (0 : ℝ) < κ x := lt_of_lt_of_le hkmin hx.1
    have hFx : ‖∫ s in (0 : ℝ)..x, f s‖ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume :=
      hF_bound x hxmem
    rw [norm_div, Real.norm_eq_abs (κ x), abs_of_pos hκpos]
    calc ‖∫ s in (0 : ℝ)..x, f s‖ / κ x
        = ‖∫ s in (0 : ℝ)..x, f s‖ * (1 / κ x) := div_eq_mul_one_div _ _
      _ ≤ (∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) * (1 / κ x) :=
          mul_le_mul_of_nonneg_right hFx (le_of_lt (one_div_pos.mpr hκpos))
      _ ≤ (∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) * (1 / kmin) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hkmin hx.1) hM_nonneg
      _ = (∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) / kmin :=
          (div_eq_mul_one_div _ _).symm
  have hFκ_int : Integrable (fun x => (∫ s in (0 : ℝ)..x, f s) / κ x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    Integrable.of_bound hFκ_meas _ hFκ_bound
  have hD_pos : (0 : ℝ) < ∫ t in (0 : ℝ)..1, 1 / κ t := by
    have hD_eq : (∫ t in (0 : ℝ)..1, 1 / κ t)
        = ∫ t in Set.Ioc (0 : ℝ) 1, 1 / κ t ∂volume :=
      intervalIntegral.integral_of_le h01
    rw [hD_eq]
    have hle : (∫ t in Set.Ioc (0 : ℝ) 1, (1 / kmax : ℝ) ∂volume)
        ≤ ∫ t in Set.Ioc (0 : ℝ) 1, 1 / κ t ∂volume := by
      refine setIntegral_mono_ae_restrict ?_ ?_ ?_
      · apply integrableOn_const
        · rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top
        · simp
      · exact (show IntegrableOn (fun t => 1 / κ t) (Set.Icc (0 : ℝ) 1) volume
          from hκinv_int).mono_set Set.Ioc_subset_Icc_self
      · apply ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
        filter_upwards [hκ] with x hx
        exact one_div_le_one_div_of_le (lt_of_lt_of_le hkmin hx.1) hx.2
    have hconst : (∫ t in Set.Ioc (0 : ℝ) 1, (1 / kmax : ℝ) ∂volume) = 1 / kmax := by
      rw [setIntegral_const, Real.volume_real_Ioc, show max ((1 : ℝ) - 0) 0 = 1 by norm_num,
        one_smul]
    have hpos : (0 : ℝ) < ∫ t in Set.Ioc (0 : ℝ) 1, (1 / kmax : ℝ) ∂volume := by
      rw [hconst]
      exact one_div_pos.mpr hkmax
    exact lt_of_lt_of_le hpos hle
  have hD_ne : (∫ t in (0 : ℝ)..1, 1 / κ t) ≠ 0 := ne_of_gt hD_pos
  have hκinv_Ioc : Integrable (fun t => 1 / κ t)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (show IntegrableOn (fun t => 1 / κ t) (Set.Icc (0 : ℝ) 1) volume
      from hκinv_int).mono_set Set.Ioc_subset_Icc_self
  have hFκ_Ioc : Integrable (fun x => (∫ s in (0 : ℝ)..x, f s) / κ x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (show IntegrableOn (fun x => (∫ s in (0 : ℝ)..x, f s) / κ x) (Set.Icc (0 : ℝ) 1) volume
      from hFκ_int).mono_set Set.Ioc_subset_Icc_self
  set C : ℝ := (∫ t in (0 : ℝ)..1, (∫ s in (0 : ℝ)..t, f s) / κ t)
    / (∫ t in (0 : ℝ)..1, 1 / κ t) with hC_def
  refine ⟨fun x => (C - ∫ s in (0 : ℝ)..x, f s) / κ x, ?_, ?_, ?_⟩
  · have hw_meas : AEStronglyMeasurable (fun x => (C - ∫ s in (0 : ℝ)..x, f s) / κ x)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (aestronglyMeasurable_const.sub hF_meas).div₀ hκ_meas
    have hw_bound : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ‖(C - ∫ s in (0 : ℝ)..x, f s) / κ x‖
          ≤ (‖C‖ + ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) / kmin := by
      filter_upwards [hκ, ae_restrict_mem measurableSet_Icc] with x hx hxmem
      have hκpos : (0 : ℝ) < κ x := lt_of_lt_of_le hkmin hx.1
      have hFx : ‖∫ s in (0 : ℝ)..x, f s‖ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume :=
        hF_bound x hxmem
      have hnum : ‖C - ∫ s in (0 : ℝ)..x, f s‖
          ≤ ‖C‖ + ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume :=
        le_trans (norm_sub_le _ _) (by linarith [hFx])
      have hB : (0 : ℝ) ≤ ‖C‖ + ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume :=
        add_nonneg (norm_nonneg _) hM_nonneg
      rw [norm_div, Real.norm_eq_abs (κ x), abs_of_pos hκpos]
      calc ‖C - ∫ s in (0 : ℝ)..x, f s‖ / κ x
          = ‖C - ∫ s in (0 : ℝ)..x, f s‖ * (1 / κ x) := div_eq_mul_one_div _ _
        _ ≤ (‖C‖ + ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) * (1 / κ x) :=
            mul_le_mul_of_nonneg_right hnum (le_of_lt (one_div_pos.mpr hκpos))
        _ ≤ (‖C‖ + ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) * (1 / kmin) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hkmin hx.1) hB
        _ = (‖C‖ + ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume) / kmin :=
            (div_eq_mul_one_div _ _).symm
    exact MemLp.of_bound hw_meas _ hw_bound
  · have hcongr : (fun x => (C - ∫ s in (0 : ℝ)..x, f s) / κ x)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun x => C * (1 / κ x) - (∫ s in (0 : ℝ)..x, f s) / κ x) :=
      Filter.Eventually.of_forall (fun x => by
        change (C - ∫ s in (0 : ℝ)..x, f s) / κ x
          = C * (1 / κ x) - (∫ s in (0 : ℝ)..x, f s) / κ x
        rw [sub_div, mul_one_div])
    have hsub1 : Integrable (fun x => C * (1 / κ x))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      hκinv_Ioc.const_mul C
    have e1 : (∫ x in Set.Ioc (0 : ℝ) 1, (C - ∫ s in (0 : ℝ)..x, f s) / κ x ∂volume)
        = ∫ x in Set.Ioc (0 : ℝ) 1,
          (C * (1 / κ x) - (∫ s in (0 : ℝ)..x, f s) / κ x) ∂volume :=
      integral_congr_ae hcongr
    have e2 : (∫ x in Set.Ioc (0 : ℝ) 1,
          (C * (1 / κ x) - (∫ s in (0 : ℝ)..x, f s) / κ x) ∂volume)
        = (∫ x in Set.Ioc (0 : ℝ) 1, C * (1 / κ x) ∂volume)
          - (∫ x in Set.Ioc (0 : ℝ) 1, (∫ s in (0 : ℝ)..x, f s) / κ x ∂volume) :=
      integral_sub hsub1 hFκ_Ioc
    have e3 : (∫ x in Set.Ioc (0 : ℝ) 1, C * (1 / κ x) ∂volume)
        = C * (∫ x in Set.Ioc (0 : ℝ) 1, 1 / κ x ∂volume) :=
      integral_const_mul C _
    have hW : (∫ x in (0 : ℝ)..1, (C - ∫ s in (0 : ℝ)..x, f s) / κ x) = 0 := by
      refine (intervalIntegral.integral_of_le h01).trans ?_
      refine e1.trans ?_
      refine e2.trans ?_
      rw [e3, ← intervalIntegral.integral_of_le h01, ← intervalIntegral.integral_of_le h01,
        hC_def, div_mul_cancel₀ _ hD_ne, sub_self]
    exact hW
  · filter_upwards [hκ] with x hx
    exact mul_div_cancel₀ _ (ne_of_gt (lt_of_lt_of_le hkmin hx.1))


private lemma intervalIntegrable_of_memLp_two {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    IntervalIntegrable g volume 0 1 := by
  have hU : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
  have hInt : Integrable g (volume.restrict (Set.uIcc (0 : ℝ) 1)) := by
    rw [hU]
    exact hg.integrable one_le_two
  exact MeasureTheory.IntegrableOn.intervalIntegrable hInt

private lemma WeakH10.toFun_zero (v : WeakH10) : v.toFun 0 = 0 := by
  rw [v.toFun_eq_integral 0 (by simp)]
  simp

private lemma WeakH10.toFun_one (v : WeakH10) : v.toFun 1 = 0 := by
  rw [v.toFun_eq_integral 1 (by simp)]
  exact v.integral_weakDeriv_eq_zero

private lemma ac_primitive_of_memLp {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, g t) 0 1 :=
  (intervalIntegrable_of_memLp_two hg).absolutelyContinuousOnInterval_intervalIntegral
    (by simp)

private lemma WeakH10.absolutelyContinuous_toFun (v : WeakH10) :
    AbsolutelyContinuousOnInterval v.toFun 0 1 := by
  have hG := ac_primitive_of_memLp v.weakDeriv_memLp
  apply hG.congr
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  exact (v.toFun_eq_integral x hx).symm

private lemma hasDerivAt_primitive_of_memLp {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    ∀ᵐ x, x ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, g t) (g x) x := by
  have hInt := intervalIntegrable_of_memLp_two hg
  filter_upwards [hInt.ae_hasDerivAt_integral] with x hx
  intro hxIcc
  exact hx hxIcc 0 (by simp)

private lemma deriv_primitive_eq_of_memLp {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      deriv (fun x => ∫ t in (0 : ℝ)..x, g t) x = g x := by
  filter_upwards [hasDerivAt_primitive_of_memLp hg] with x hx
  intro hxIoc
  have hxIcc : x ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hxIoc
  exact (hx hxIcc).deriv

private lemma WeakH10.deriv_toFun_eq_weakDeriv (v : WeakH10) :
    ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      deriv v.toFun x = v.weakDeriv x := by
  have h1 : ∀ᵐ x : ℝ, x ≠ (1 : ℝ) := by
    rw [ae_iff]
    have hset : {x : ℝ | ¬x ≠ 1} = {1} := by ext x; simp
    rw [hset]
    exact Real.volume_singleton
  filter_upwards [hasDerivAt_primitive_of_memLp v.weakDeriv_memLp, h1] with x hx hxNe
  intro hxIoc
  have hxIcc : x ∈ Set.uIcc (0 : ℝ) 1 := Set.uIoc_subset_uIcc hxIoc
  have hIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxIoc
    exact ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxNe⟩
  have hIccMem : Set.Icc (0 : ℝ) 1 ∈ nhds x :=
    Filter.mem_of_superset (Ioo_mem_nhds hIoo.1 hIoo.2) Set.Ioo_subset_Icc_self
  have hEq : v.toFun =ᶠ[nhds x] (fun y => ∫ t in (0 : ℝ)..y, v.weakDeriv t) := by
    filter_upwards [hIccMem] with y hy
    exact v.toFun_eq_integral y hy
  have hHas : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, v.weakDeriv t) (v.weakDeriv x) x :=
    hx hxIcc
  exact (hHas.congr_of_eventuallyEq hEq).deriv

/-- Integration by parts for the primitive of an `L²` function against a
`WeakH10` test function: `∫ F * v' = -∫ f * v`, where `F x = ∫ s in 0..x,
f s`. Both `F` and `v.toFun` are absolutely continuous on `[0,1]`, with
derivatives `f` and `v.weakDeriv` almost everywhere, so Mathlib's
integration by parts for absolutely continuous functions applies; the
boundary terms vanish because `v 0 = v 1 = 0`. -/
lemma weak_diffusion_ibp
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1)))
    (v : WeakH10) :
    ∫ x in (0 : ℝ)..1, (∫ s in (0 : ℝ)..x, f s) * v.weakDeriv x
      = -∫ x in (0 : ℝ)..1, f x * v.toFun x := by
  have hF := ac_primitive_of_memLp hf
  have hv := v.absolutelyContinuous_toFun
  have hIbp := hF.integral_mul_deriv_eq_deriv_mul hv
  rw [v.toFun_zero, v.toFun_one, mul_zero, mul_zero, sub_zero, zero_sub] at hIbp
  have hLHS : ∫ x in (0 : ℝ)..1, (∫ s in (0 : ℝ)..x, f s) * deriv v.toFun x
      = ∫ x in (0 : ℝ)..1, (∫ s in (0 : ℝ)..x, f s) * v.weakDeriv x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [v.deriv_toFun_eq_weakDeriv] with x hx
    intro hxIoc
    rw [hx hxIoc]
  have hRHS : ∫ x in (0 : ℝ)..1, deriv (fun x => ∫ s in (0 : ℝ)..x, f s) x * v.toFun x
      = ∫ x in (0 : ℝ)..1, f x * v.toFun x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [deriv_primitive_eq_of_memLp hf] with x hx
    intro hxIoc
    rw [hx hxIoc]
  rw [hLHS, hRHS] at hIbp
  exact hIbp

/-! ## C. Uniqueness (energy argument) -/

private lemma intervalIntegrable_of_memLp_Icc (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1)))
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable f volume 0 x := by
  have hInt : IntegrableOn f (Set.Icc 0 1) volume :=
    MemLp.integrable (by norm_num) hf
  have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc 0 1 :=
    Set.Icc_subset_Icc_right hx.2
  have hOn : IntegrableOn f (Set.Icc (0 : ℝ) x) volume := hInt.mono hsub le_rfl
  have hU : IntegrableOn f (Set.uIcc 0 x) volume := by
    rw [Set.uIcc_of_le hx.1]
    exact hOn
  exact hU.intervalIntegrable

/-- The difference of two `WeakH10` functions is a `WeakH10` function, with
the difference function and the difference weak derivative: the `L²` field
by `MemLp.sub`, the other two by linearity of the interval integral. -/
private lemma weakH10_sub (u u' : WeakH10) :
    ∃ w : WeakH10, w.toFun = (fun x => u'.toFun x - u.toFun x)
      ∧ w.weakDeriv = (fun x => u'.weakDeriv x - u.weakDeriv x) := by
  refine ⟨⟨fun x => u'.toFun x - u.toFun x, fun x => u'.weakDeriv x - u.weakDeriv x,
    u'.weakDeriv_memLp.sub u.weakDeriv_memLp, ?_, ?_⟩, rfl, rfl⟩
  · intro x hx
    show u'.toFun x - u.toFun x = ∫ t in (0 : ℝ)..x, (u'.weakDeriv t - u.weakDeriv t)
    rw [u'.toFun_eq_integral x hx, u.toFun_eq_integral x hx,
      intervalIntegral.integral_sub
        (intervalIntegrable_of_memLp_Icc _ u'.weakDeriv_memLp x hx)
        (intervalIntegrable_of_memLp_Icc _ u.weakDeriv_memLp x hx)]
  · show (∫ t in (0 : ℝ)..1, (u'.weakDeriv t - u.weakDeriv t)) = 0
    rw [intervalIntegral.integral_sub
        (intervalIntegrable_of_memLp_Icc _ u'.weakDeriv_memLp 1 ⟨zero_le_one, le_rfl⟩)
        (intervalIntegrable_of_memLp_Icc _ u.weakDeriv_memLp 1 ⟨zero_le_one, le_rfl⟩),
      u'.integral_weakDeriv_eq_zero, u.integral_weakDeriv_eq_zero, sub_self]

private lemma weak_diffusion_eqOn_of_energy_zero_of_measurable
    {κ : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hκmeas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (u u' : WeakH10)
    (hE : ∫ x in (0 : ℝ)..1, κ x * (u'.weakDeriv x - u.weakDeriv x) ^ 2 = 0) :
    Set.EqOn u'.toFun u.toFun (Set.Icc 0 1) := by
  have hsub : MemLp (u'.weakDeriv - u.weakDeriv) 2 (volume.restrict (Set.Icc 0 1)) :=
    u'.weakDeriv_memLp.sub u.weakDeriv_memLp
  have hmul : Integrable ((u'.weakDeriv - u.weakDeriv) * (u'.weakDeriv - u.weakDeriv))
      (volume.restrict (Set.Icc 0 1)) :=
    MemLp.integrable_mul hsub hsub
  have hfun : (fun x => (u'.weakDeriv x - u.weakDeriv x) ^ 2) =
      ((u'.weakDeriv - u.weakDeriv) * (u'.weakDeriv - u.weakDeriv)) := by
    funext x
    simp [Pi.mul_apply, Pi.sub_apply, sq]
  have hsq : Integrable (fun x => (u'.weakDeriv x - u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) := by
    rw [hfun]
    exact hmul
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), ‖κ x‖ ≤ |kmin| ⊔ |kmax| := by
    filter_upwards [hκ] with x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [Real.norm_eq_abs]
    by_cases hsign : 0 ≤ κ x
    · rw [abs_of_nonneg hsign]
      calc κ x ≤ kmax := h2
        _ ≤ |kmax| := le_abs_self kmax
        _ ≤ |kmin| ⊔ |kmax| := le_max_right _ _
    · have hneg : κ x < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hneg]
      calc -κ x ≤ -kmin := by linarith
        _ ≤ |kmin| := neg_le_abs kmin
        _ ≤ |kmin| ⊔ |kmax| := le_max_left _ _
  have hf_int : Integrable (fun x => κ x * (u'.weakDeriv x - u.weakDeriv x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) :=
    Integrable.bdd_mul hsq hκmeas hbdd
  have hf_interval : IntervalIntegrable
      (fun x => κ x * (u'.weakDeriv x - u.weakDeriv x) ^ 2) volume 0 1 := by
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le h01
    apply IntegrableOn.intervalIntegrable
    rw [huIcc]
    exact hf_int
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hIoc10 : Set.Ioc (1 : ℝ) 0 = ∅ := Set.Ioc_eq_empty_of_le h01
  have hsub_union : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc 1 0 ⊆ Set.Icc 0 1 := by
    rw [hIoc10, Set.union_empty]
    exact Set.Ioc_subset_Icc_self
  have hκ_union : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc 1 0)),
      kmin ≤ κ x ∧ κ x ≤ kmax :=
    ae_restrict_of_ae_restrict_of_subset hsub_union hκ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc 1 0)]
      fun x => κ x * (u'.weakDeriv x - u.weakDeriv x) ^ 2 := by
    filter_upwards [hκ_union] with x hx
    obtain ⟨h1, h2⟩ := hx
    have hκnn : 0 ≤ κ x := le_trans (le_of_lt hkmin) h1
    have hsqnn : 0 ≤ (u'.weakDeriv x - u.weakDeriv x) ^ 2 := sq_nonneg _
    exact mul_nonneg hκnn hsqnn
  have hf_zero_union :
      (fun x => κ x * (u'.weakDeriv x - u.weakDeriv x) ^ 2)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc 1 0)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae hnonneg hf_interval).mp hE
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc 1 0 = Set.Ioc 0 1 := by
    rw [hIoc10, Set.union_empty]
  rw [hunion] at hf_zero_union
  have hκ_ioc : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      kmin ≤ κ x ∧ κ x ≤ kmax :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hκ
  have hΔw_zero :
      (fun x => u'.weakDeriv x - u.weakDeriv x)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] 0 := by
    filter_upwards [hf_zero_union, hκ_ioc] with x hx_f hx_κ
    obtain ⟨h1, h2⟩ := hx_κ
    have hκne : κ x ≠ 0 := ne_of_gt (lt_of_lt_of_le hkmin h1)
    simp only [Pi.zero_apply] at hx_f ⊢
    have hsq0 : (u'.weakDeriv x - u.weakDeriv x) ^ 2 = 0 := by
      have h := (mul_eq_zero.mp hx_f).resolve_left hκne
      exact h
    have hΔ0 : u'.weakDeriv x - u.weakDeriv x = 0 := by
      rw [pow_two] at hsq0
      exact (mul_eq_zero.mp hsq0).elim id id
    exact hΔ0
  intro x hx
  have hx_mem : x ∈ Set.Icc (0 : ℝ) 1 := hx
  obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx_mem
  have hu'_eq := u'.toFun_eq_integral x hx_mem
  have hu_eq := u.toFun_eq_integral x hx_mem
  have hInt_u : Integrable u.weakDeriv (volume.restrict (Set.Icc 0 1)) :=
    MemLp.integrable (by norm_num) u.weakDeriv_memLp
  have hInt_u' : Integrable u'.weakDeriv (volume.restrict (Set.Icc 0 1)) :=
    MemLp.integrable (by norm_num) u'.weakDeriv_memLp
  have huIcc0x : Set.uIcc (0 : ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx0
  have hIcc_sub : Set.Icc (0 : ℝ) x ⊆ Set.Icc 0 1 := by
    intro y hy
    obtain ⟨hy0, hyx⟩ := Set.mem_Icc.mp hy
    exact Set.mem_Icc.mpr ⟨hy0, le_trans hyx hx1⟩
  have hII_u : IntervalIntegrable u.weakDeriv volume 0 x := by
    apply IntegrableOn.intervalIntegrable
    rw [huIcc0x]
    exact IntegrableOn.mono_set hInt_u hIcc_sub
  have hII_u' : IntervalIntegrable u'.weakDeriv volume 0 x := by
    apply IntegrableOn.intervalIntegrable
    rw [huIcc0x]
    exact IntegrableOn.mono_set hInt_u' hIcc_sub
  have hIoc_sub : Set.Ioc (0 : ℝ) x ⊆ Set.Ioc 0 1 :=
    Set.Ioc_subset_Ioc_right hx1
  have hΔw_zero_x :
      (fun t => u'.weakDeriv t - u.weakDeriv t)
        =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) x)] 0 :=
    ae_restrict_of_ae_restrict_of_subset hIoc_sub hΔw_zero
  have hInt_diff_zero : ∫ t in (0 : ℝ)..x, (u'.weakDeriv t - u.weakDeriv t) = 0 := by
    rw [intervalIntegral.integral_of_le hx0]
    exact integral_eq_zero_of_ae hΔw_zero_x
  have hsub_eq := intervalIntegral.integral_sub hII_u' hII_u
  rw [hInt_diff_zero] at hsub_eq
  have hEq : (∫ t in (0 : ℝ)..x, u'.weakDeriv t) = ∫ t in (0 : ℝ)..x, u.weakDeriv t := by
    linarith [hsub_eq]
  rw [hu'_eq, hu_eq]
  exact hEq

/-! ## D. Existence and uniqueness of the weak solution -/

private lemma integrable_primitive_mul_of_memLp {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) :
    Integrable (fun x => (∫ s in (0:ℝ)..x, f s) * g x)
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hf_int : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hf.integrable (by norm_num)
  have hInteg_uIcc : IntegrableOn f (Set.uIcc (0 : ℝ) 1) volume := by
    rw [Set.uIcc_of_le h01]
    exact hf_int
  have hF_cont : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, f s) (Set.Icc (0 : ℝ) 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := (1 : ℝ))
      (μ := volume) (f := f) hInteg_uIcc
    rw [Set.uIcc_of_le h01] at h
    exact h
  have hF_meas : AEStronglyMeasurable (fun x => ∫ s in (0 : ℝ)..x, f s)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hF_cont.aestronglyMeasurable measurableSet_Icc
  have hF_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖∫ s in (0 : ℝ)..x, f s‖ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume := by
    intro x hx
    calc ‖∫ s in (0 : ℝ)..x, f s‖
        ≤ ∫ s in Set.uIoc (0 : ℝ) x, ‖f s‖ ∂volume :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ s in Set.Ioc (0 : ℝ) x, ‖f s‖ ∂volume := by rw [Set.uIoc_of_le hx.1]
      _ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume := by
          refine setIntegral_mono_set hf_int.norm ?_ ?_
          · filter_upwards with s
            exact norm_nonneg _
          · exact Filter.Eventually.of_forall (fun _ hs => ⟨hs.1.le, le_trans hs.2 hx.2⟩)
  have hg_int : Integrable g (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    hg.integrable (by norm_num)
  have hF_bdd : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖∫ s in (0 : ℝ)..x, f s‖ ≤ ∫ s in Set.Icc (0 : ℝ) 1, ‖f s‖ ∂volume := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hxmem
    exact hF_bound x hxmem
  exact Integrable.bdd_mul hg_int hF_meas hF_bdd

private lemma integrable_kappa_mul {κ R : ℝ → ℝ} {kmin kmax : ℝ}
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hR : Integrable R (volume.restrict (Set.Icc 0 1))) :
    Integrable (fun x => κ x * R x) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  have hbdd : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), ‖κ x‖ ≤ |kmin| ⊔ |kmax| := by
    filter_upwards [hκ] with x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [Real.norm_eq_abs]
    by_cases hsign : 0 ≤ κ x
    · rw [abs_of_nonneg hsign]
      calc κ x ≤ kmax := h2
        _ ≤ |kmax| := le_abs_self kmax
        _ ≤ |kmin| ⊔ |kmax| := le_max_right _ _
    · have hneg : κ x < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hneg]
      calc -κ x ≤ -kmin := by linarith
        _ ≤ |kmin| := neg_le_abs kmin
        _ ≤ |kmin| ⊔ |kmax| := le_max_left _ _
  exact Integrable.bdd_mul hR hκ_meas hbdd

/-- Existence and uniqueness of the weak solution of the steady diffusion
problem `-(κ u')' = f` on `(0,1)`, `u(0) = u(1) = 0`. For `κ` a.e. strongly
measurable with `0 < kmin ≤ κ ≤ kmax` a.e. on `[0,1]` and `f ∈ L²(0,1)`,
some `u : WeakH10` satisfies `∫₀¹ κ u' v' = ∫₀¹ f v` for every
`v : WeakH10`, and every `u' : WeakH10` satisfying the same equations agrees
with `u` on `[0,1]`. There is no drift or zeroth-order term. -/
theorem weak_diffusion_exists_unique
    {κ f : ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable κ (volume.restrict (Set.Icc 0 1)))
    (hκ : ∀ᵐ x ∂(volume.restrict (Set.Icc 0 1)), kmin ≤ κ x ∧ κ x ≤ kmax)
    (hf : MemLp f 2 (volume.restrict (Set.Icc 0 1))) :
    ∃ u : WeakH10,
      (∀ v : WeakH10,
        ∫ x in (0 : ℝ)..1, κ x * u.weakDeriv x * v.weakDeriv x
          = ∫ x in (0 : ℝ)..1, f x * v.toFun x)
      ∧ ∀ u' : WeakH10,
        (∀ v : WeakH10,
          ∫ x in (0 : ℝ)..1, κ x * u'.weakDeriv x * v.weakDeriv x
            = ∫ x in (0 : ℝ)..1, f x * v.toFun x) →
        Set.EqOn u'.toFun u.toFun (Set.Icc 0 1) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨w, hw_mem, hw_zero, hw_ae⟩ := weak_diffusion_candidate hkmin hκ_meas hκ hf
  set C : ℝ := (∫ t in (0:ℝ)..1, (∫ s in (0:ℝ)..t, f s) / κ t)
    / (∫ t in (0:ℝ)..1, 1 / κ t)
  set u : WeakH10 := ⟨fun x => ∫ t in (0:ℝ)..x, w t, w, hw_mem, fun x _ => rfl, hw_zero⟩
  have heq : ∀ v : WeakH10,
      ∫ x in (0:ℝ)..1, κ x * u.weakDeriv x * v.weakDeriv x
        = ∫ x in (0:ℝ)..1, f x * v.toFun x := by
    intro v
    change ∫ x in (0:ℝ)..1, κ x * w x * v.weakDeriv x
      = ∫ x in (0:ℝ)..1, f x * v.toFun x
    have hA : ∫ x in (0:ℝ)..1, κ x * w x * v.weakDeriv x
        = ∫ x in (0:ℝ)..1, (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01]
      have hcongr : (fun x => κ x * w x * v.weakDeriv x)
          =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)]
          (fun x => (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x) := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
          Set.Ioc_subset_Icc_self hw_ae] with x hx
        show κ x * w x * v.weakDeriv x = (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x
        rw [hx]
      exact integral_congr_ae hcongr
    have h2Icc : Integrable (fun x => (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x)
        (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      integrable_primitive_mul_of_memLp hf v.weakDeriv_memLp
    have h2 : Integrable (fun x => (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (show IntegrableOn _ (Set.Icc (0:ℝ) 1) volume from h2Icc).mono_set
        Set.Ioc_subset_Icc_self
    have hvIcc : Integrable v.weakDeriv (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      v.weakDeriv_memLp.integrable (by norm_num)
    have hvIoc : Integrable v.weakDeriv (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (show IntegrableOn _ (Set.Icc (0:ℝ) 1) volume from hvIcc).mono_set
        Set.Ioc_subset_Icc_self
    have h1 : Integrable (fun x => C * v.weakDeriv x)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      hvIoc.const_mul C
    have e1 : (∫ x in Set.Ioc (0:ℝ) 1, (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x ∂volume)
        = ∫ x in Set.Ioc (0:ℝ) 1,
          (C * v.weakDeriv x - (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        change (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x
          = C * v.weakDeriv x - (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x
        ring))
    have e2 : (∫ x in Set.Ioc (0:ℝ) 1,
          (C * v.weakDeriv x - (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x) ∂volume)
        = (∫ x in Set.Ioc (0:ℝ) 1, C * v.weakDeriv x ∂volume)
          - ∫ x in Set.Ioc (0:ℝ) 1, (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x ∂volume :=
      integral_sub h1 h2
    have e3 : (∫ x in Set.Ioc (0:ℝ) 1, C * v.weakDeriv x ∂volume)
        = C * ∫ x in Set.Ioc (0:ℝ) 1, v.weakDeriv x ∂volume :=
      integral_const_mul C _
    have hB : ∫ x in (0:ℝ)..1, (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x
        = C * (∫ x in (0:ℝ)..1, v.weakDeriv x)
          - ∫ x in (0:ℝ)..1, (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01,
        intervalIntegral.integral_of_le h01, e1, e2, e3]
    have hibp := weak_diffusion_ibp hf v
    calc ∫ x in (0:ℝ)..1, κ x * w x * v.weakDeriv x
        = ∫ x in (0:ℝ)..1, (C - ∫ s in (0:ℝ)..x, f s) * v.weakDeriv x := hA
      _ = C * (∫ x in (0:ℝ)..1, v.weakDeriv x)
          - ∫ x in (0:ℝ)..1, (∫ s in (0:ℝ)..x, f s) * v.weakDeriv x := hB
      _ = C * 0 - -∫ x in (0:ℝ)..1, f x * v.toFun x := by
          rw [v.integral_weakDeriv_eq_zero, hibp]
      _ = ∫ x in (0:ℝ)..1, f x * v.toFun x := by
          rw [mul_zero, sub_neg_eq_add, zero_add]
  refine ⟨u, heq, ?_⟩
  intro u' hu'
  obtain ⟨wΔ, hwΔ_fun, hwΔ_deriv⟩ := weakH10_sub u u'
  have hwΔ_eq : ∀ x, wΔ.weakDeriv x = u'.weakDeriv x - u.weakDeriv x :=
    fun x => congrFun hwΔ_deriv x
  have e1 := hu' wΔ
  have e2 := heq wΔ
  simp only [hwΔ_eq, mul_assoc] at e1 e2
  have hEq : (∫ x in (0:ℝ)..1, κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      = (∫ x in (0:ℝ)..1, κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))) :=
    e1.trans e2.symm
  have hΔmem : MemLp (fun x => u'.weakDeriv x - u.weakDeriv x) 2
      (volume.restrict (Set.Icc 0 1)) :=
    u'.weakDeriv_memLp.sub u.weakDeriv_memLp
  have hP1 : Integrable (fun x => u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))
      (volume.restrict (Set.Icc 0 1)) :=
    MemLp.integrable_mul u'.weakDeriv_memLp hΔmem
  have hP2 : Integrable (fun x => u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))
      (volume.restrict (Set.Icc 0 1)) :=
    MemLp.integrable_mul u.weakDeriv_memLp hΔmem
  have hK1 : Integrable
      (fun x => κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      (volume.restrict (Set.Icc 0 1)) :=
    integrable_kappa_mul hκ_meas hκ hP1
  have hK2 : Integrable
      (fun x => κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      (volume.restrict (Set.Icc 0 1)) :=
    integrable_kappa_mul hκ_meas hκ hP2
  have hI1 : Integrable
      (fun x => κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (show IntegrableOn _ (Set.Icc (0:ℝ) 1) volume from hK1).mono_set
      Set.Ioc_subset_Icc_self
  have hI2 : Integrable
      (fun x => κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (show IntegrableOn _ (Set.Icc (0:ℝ) 1) volume from hK2).mono_set
      Set.Ioc_subset_Icc_self
  have es : (∫ x in Set.Ioc (0:ℝ) 1,
        (κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))
          - κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))) ∂volume)
      = (∫ x in Set.Ioc (0:ℝ) 1,
          κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)) ∂volume)
        - ∫ x in Set.Ioc (0:ℝ) 1,
          κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)) ∂volume :=
    integral_sub hI1 hI2
  have ec : (∫ x in Set.Ioc (0:ℝ) 1,
        (κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))
          - κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))) ∂volume)
      = ∫ x in Set.Ioc (0:ℝ) 1, κ x * (u'.weakDeriv x - u.weakDeriv x)^2 ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by
      change (κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x))
          - κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
          = κ x * (u'.weakDeriv x - u.weakDeriv x)^2
      ring))
  have hcomb : (∫ x in (0:ℝ)..1, κ x * (u'.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      - (∫ x in (0:ℝ)..1, κ x * (u.weakDeriv x * (u'.weakDeriv x - u.weakDeriv x)))
      = ∫ x in (0:ℝ)..1, κ x * (u'.weakDeriv x - u.weakDeriv x)^2 := by
    rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01,
      intervalIntegral.integral_of_le h01]
    exact es.symm.trans ec
  have hE : ∫ x in (0:ℝ)..1, κ x * (u'.weakDeriv x - u.weakDeriv x)^2 = 0 := by
    rw [← hcomb, hEq, sub_self]
  exact weak_diffusion_eqOn_of_energy_zero_of_measurable hkmin hκ hκ_meas u u' hE

end EarthScience
