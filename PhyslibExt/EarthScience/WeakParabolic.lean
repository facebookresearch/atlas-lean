/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Prod
public import PhyslibExt.EarthScience.WeakDiffusion

/-!
# Uniqueness of weak solutions of one-dimensional parabolic diffusion

Weak solutions of `∂ₜu = ∂ₓ(κ ∂ₓu) + F` on `(t0, t1) × (0, 1)` with zero boundary values,
continuous in time with values in `L²(0,1)`, are determined by their initial value, given
the energy identity of the homogeneous equation.

## i. Overview

The equation describes one-dimensional diffusion with a diffusivity `κ (t, x)` that may
vary in time and in space, for example heat conduction across a layer whose boundary
temperatures are held fixed (after the boundary values are subtracted). The diffusivity is
a.e. strongly measurable with `0 < kmin ≤ κ ≤ kmax` a.e. Test functions (`ParabolicTest`)
are C^∞ with support inside the open rectangle, and weak forms are iterated integrals with
time outside. Spatial profiles use `EarthScience.WeakH10`, the `H¹₀(0,1)` structure of
`PhyslibExt.EarthScience.WeakDiffusion`.

`IsWeakParabolicSolution` is the solution class
`L²(t0, t1; H¹₀(0,1)) ∩ C([t0, t1]; L²(0,1))`, with the given function as its representative
in time: time slices in `L²(0,1)` that vary continuously, `H¹₀(0,1)` profiles at almost every
time, a forcing integrable against every test function, and the weak equation. In space it
fixes no representative: the profile condition asks for agreement almost everywhere on
`[0, 1]`, the other conditions on a time slice depend on it only up to such agreement, and
those on the rectangle only up to equality almost everywhere there. The initial value is an
`L²(0,1)` trace, `u t0 = u0` in `L²(0,1)`, so it may be any function of `L²(0,1)`.

`weak_parabolic_unique` proves that two solutions with the same forcing and the same
initial value agree in `L²(0,1)` at every time. It takes the energy identity of the
homogeneous equation, `‖w τ‖² + 2 ∫_{t0}^{τ} ∫₀¹ κ (∂ₓw)² = ‖w t0‖²`, as an explicit
hypothesis on the same class. The identity holds for every admissible `κ` (Evans, §5.9.2,
Theorem 3), but its proof needs time-regularity results this module does not contain. Time
continuity matters here: a solution changed at a single time still satisfies the weak
equation, and without continuity the identity fails
(`PhyslibExtTest.EarthScience.WeakParabolic` records the counterexample). Existence of
solutions is not treated.

## ii. Key results

- `EarthScience.IsWeakParabolicSolution`: the class of weak solutions.
- `EarthScience.weak_parabolic_sub`: two solutions with the same forcing differ by a
  solution of the homogeneous equation.
- `EarthScience.weak_parabolic_unique_of_energy`: the energy identity with zero initial
  value forces a solution with `L²(0,1)` time slices to vanish almost everywhere.
- `EarthScience.weak_parabolic_unique`: uniqueness of weak solutions, given the energy
  identity.

## iii. Table of contents

- A. The weak formulation
- B. Differences of solutions
- C. Uniqueness

## iv. References

- L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics
  19, American Mathematical Society, 2010: §7.1 (weak solutions of second-order parabolic
  equations and their uniqueness) and §5.9.2, Theorem 3 (continuity in time and the energy
  identity for `u ∈ L²(0, T; H¹₀)` with `u' ∈ L²(0, T; H⁻¹)`).
- `PhyslibExt.EarthScience.WeakDiffusion`: the `H¹₀(0,1)` structure `WeakH10`.
-/

open MeasureTheory
open scoped ENNReal
open Filter
open scoped BigOperators
open Set

@[expose] public section

namespace EarthScience

/-! ## A. The weak formulation -/

/-- **Test functions.** The test functions of the parabolic weak formulation are the smooth
functions on time × space whose support, the closure of the set where they do not vanish, lies
inside the open rectangle `(t0, t1) × (0, 1)`. Such a support is closed and bounded, hence
compact.
Note: `ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞)` is C^∞. Under current Mathlib `ContDiff` is indexed
by `ℕ∞ω`, where `⊤ = ω` means analytic, while `∞` means C^∞. -/
def ParabolicTest (t0 t1 : ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun p : ℝ × ℝ => φ p.1 p.2)
    ∧ tsupport (fun p : ℝ × ℝ => φ p.1 p.2) ⊆ Set.Ioo t0 t1 ×ˢ Set.Ioo 0 1

lemma parabolicTest_deriv_memLp
    {t0 t1 : ℝ}
    (φ : ℝ → ℝ → ℝ) (hφ : ParabolicTest t0 t1 φ) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
      ∧ Continuous (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2)
      ∧ MemLp (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ MemLp (Function.uncurry (fun t x => deriv (fun y => φ t y) x)) 2
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  obtain ⟨h_smooth, -⟩ := hφ
  have hn0 : (((⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ (fun p : ℝ × ℝ => φ p.1 p.2) :=
    h_smooth.differentiable hn0
  have hderiv1 : ∀ t x : ℝ, deriv (fun s => φ s x) t
      = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (1, 0) := by
    intro t x
    have hF_at : HasFDerivAt (fun p : ℝ × ℝ => φ p.1 p.2)
        (fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x)) (t, x) :=
      (hdiff (t, x)).hasFDerivAt
    have hid : HasFDerivAt (fun s : ℝ => s) (ContinuousLinearMap.id ℝ ℝ) t :=
      hasFDerivAt_id t
    have hconst : HasFDerivAt (fun _ : ℝ => x) (0 : ℝ →L[ℝ] ℝ) t :=
      hasFDerivAt_const x t
    have hprod := hid.prodMk hconst
    have hcomp := hF_at.comp t hprod
    have hder := hcomp.hasDerivAt.deriv
    have hM1 : (((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) (1 : ℝ))
        = (1, 0) := by
      simp [ContinuousLinearMap.prod_apply]
    calc deriv (fun s => φ s x) t
        = deriv ((fun p : ℝ × ℝ => φ p.1 p.2) ∘ (fun s : ℝ => (s, x))) t := rfl
      _ = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (1, 0) := by
          have h2 := hder
          rw [ContinuousLinearMap.comp_apply, hM1] at h2
          exact h2
  have hfun_eq1 : (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
      = (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) p (1, 0)) := by
    funext p
    obtain ⟨t, x⟩ := p
    exact hderiv1 t x
  have hcont1 : Continuous (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) := by
    rw [hfun_eq1]
    have hcf : Continuous (fun p : ℝ × ℝ => (p, ((1, 0) : ℝ × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact (h_smooth.continuous_fderiv_apply hn0).comp hcf
  have hderiv2 : ∀ t x : ℝ, deriv (fun y => φ t y) x
      = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (0, 1) := by
    intro t x
    have hF_at : HasFDerivAt (fun p : ℝ × ℝ => φ p.1 p.2)
        (fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x)) (t, x) :=
      (hdiff (t, x)).hasFDerivAt
    have hid : HasFDerivAt (fun y : ℝ => y) (ContinuousLinearMap.id ℝ ℝ) x :=
      hasFDerivAt_id x
    have hconst : HasFDerivAt (fun _ : ℝ => t) (0 : ℝ →L[ℝ] ℝ) x :=
      hasFDerivAt_const t x
    have hprod := hconst.prodMk hid
    have hcomp := hF_at.comp x hprod
    have hder := hcomp.hasDerivAt.deriv
    have hM1 : (((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) (1 : ℝ))
        = (0, 1) := by
      simp [ContinuousLinearMap.prod_apply]
    calc deriv (fun y => φ t y) x
        = deriv ((fun p : ℝ × ℝ => φ p.1 p.2) ∘ (fun y : ℝ => (t, y))) x := rfl
      _ = fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (t, x) (0, 1) := by
          have h2 := hder
          rw [ContinuousLinearMap.comp_apply, hM1] at h2
          exact h2
  have hfun_eq2 : (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2)
      = (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => φ p.1 p.2) p (0, 1)) := by
    funext p
    obtain ⟨t, x⟩ := p
    exact hderiv2 t x
  have hcont2 : Continuous (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2) := by
    rw [hfun_eq2]
    have hcf : Continuous (fun p : ℝ × ℝ => (p, ((0, 1) : ℝ × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact (h_smooth.continuous_fderiv_apply hn0).comp hcf
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := ⟨by
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  have hmeasR : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    MeasurableSet.prod measurableSet_Icc measurableSet_Icc
  have hcompR : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hmem1 : MemLp (fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    have himg : IsCompact ((fun p : ℝ × ℝ => deriv (fun s => φ s p.2) p.1)
        '' (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := hcompR.image hcont1
    obtain ⟨C₁, hC₁⟩ := himg.bddAbove
    obtain ⟨C₂, hC₂⟩ := himg.bddBelow
    have hbdd : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
        deriv (fun s => φ s p.2) p.1 ∈ Set.Icc C₂ C₁ := by
      refine (ae_restrict_mem hmeasR).mono (fun p hp => ?_)
      rw [Set.mem_Icc]
      exact ⟨(mem_lowerBounds.mp hC₂) _ (Set.mem_image_of_mem _ hp),
        (mem_upperBounds.mp hC₁) _ (Set.mem_image_of_mem _ hp)⟩
    exact memLp_of_bounded hbdd hcont1.aestronglyMeasurable 2
  have hmem2 : MemLp (fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    have himg : IsCompact ((fun p : ℝ × ℝ => deriv (fun y => φ p.1 y) p.2)
        '' (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := hcompR.image hcont2
    obtain ⟨C₁, hC₁⟩ := himg.bddAbove
    obtain ⟨C₂, hC₂⟩ := himg.bddBelow
    have hbdd : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)),
        deriv (fun y => φ p.1 y) p.2 ∈ Set.Icc C₂ C₁ := by
      refine (ae_restrict_mem hmeasR).mono (fun p hp => ?_)
      rw [Set.mem_Icc]
      exact ⟨(mem_lowerBounds.mp hC₂) _ (Set.mem_image_of_mem _ hp),
        (mem_upperBounds.mp hC₁) _ (Set.mem_image_of_mem _ hp)⟩
    exact memLp_of_bounded hbdd hcont2.aestronglyMeasurable 2
  have hunc1 : MemLp (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := hmem1
  have hunc2 : MemLp (Function.uncurry (fun t x => deriv (fun y => φ t y) x)) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := hmem2
  exact ⟨hcont1, hcont2, hunc1, hunc2⟩

/-- **Weak parabolic solutions.** These are the weak solutions of `∂ₜu = ∂ₓ(κ ∂ₓu) + F` on
`(t0, t1) × (0, 1)` with zero boundary values that are continuous in time with values in
`L²(0,1)`.

`u` is the solution and `ux` its spatial derivative, both as functions of `(t, x)`. This is
the class `L²(t0, t1; H¹₀(0,1)) ∩ C([t0, t1]; L²(0,1))` of the standard theory (Evans,
§5.9.2 and §7.1.1). In space no representative is prescribed: at almost every time `u t` need
only agree almost everywhere on `[0, 1]` with an `H¹₀(0,1)` function (`WeakH10`) whose weak
derivative agrees almost everywhere on `[0, 1]` with `ux t`; the other conditions on a time
slice depend on it only up to such agreement, and those on the rectangle only up to equality
almost everywhere there. In time the given `u` is the representative: every time slice is in
`L²(0,1)` and the slices vary continuously in `L²(0,1)`, while the `H¹₀(0,1)` condition, which
imposes the boundary values, is required at almost every time only. In particular no profile
is required at the initial time, so the initial value may be any function of `L²(0,1)`.

Both sides of the weak equation are Lebesgue integrals, not Lean's default value `0` for a
non-integrable function: the class requires the forcing to be integrable against every test
function, and the left side is integrable for every test function once `κ` is a.e. bounded
and a.e. strongly measurable (`weak_parabolic_integrand_integrable`), as in
`weak_parabolic_unique`. -/
structure IsWeakParabolicSolution (t0 t1 : ℝ) (κ F u ux : ℝ → ℝ → ℝ) : Prop where
  /-- Every time slice `u t`, `t ∈ [t0, t1]`, is in `L²(0,1)`. -/
  memLp_slice : ∀ t ∈ Set.Icc t0 t1, MemLp (fun x => u t x) 2 (volume.restrict (Set.Icc 0 1))
  /-- `t ↦ u t` is continuous on `[t0, t1]` for the `L²(0,1)` distance. -/
  continuous_slice : ∀ s ∈ Set.Icc t0 t1, Filter.Tendsto
    (fun t => (eLpNorm (fun x => u t x - u s x) 2 (volume.restrict (Set.Icc 0 1))).toReal)
    (nhdsWithin s (Set.Icc t0 t1)) (nhds 0)
  /-- At almost every time, `u t` agrees almost everywhere on `[0, 1]` with an `H¹₀(0,1)`
  function whose weak derivative agrees almost everywhere on `[0, 1]` with `ux t`. -/
  profile : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
    ∃ h : WeakH10, h.toFun =ᵐ[volume.restrict (Set.Icc 0 1)] u t
      ∧ h.weakDeriv =ᵐ[volume.restrict (Set.Icc 0 1)] ux t
  /-- `u` is in `L²` on the rectangle. -/
  memLp : MemLp (Function.uncurry u) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
  /-- The spatial derivative `ux` is in `L²` on the rectangle. -/
  memLp_deriv : MemLp (Function.uncurry ux) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
  /-- The forcing is integrable against every test function on the rectangle. -/
  forcing_integrable : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
    Integrable (fun p : ℝ × ℝ => F p.1 p.2 * φ p.1 p.2)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
  /-- The weak equation against every test function. -/
  weak_eq : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
    ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-u t x * deriv (fun s => φ s x) t + κ t x * ux t x * deriv (fun y => φ t y) x)
      = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x

/-! ## B. Differences of solutions -/

/-- An `L²` function on `[0,1]` is interval integrable on every `[0,x]`, `x ∈ [0,1]`. -/
private lemma weakH10_memLp_intervalIntegrable (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Set.Icc 0 1))) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable g volume 0 x := by
  have hIntOn : IntegrableOn g (Set.Icc 0 1) volume := hg.integrable one_le_two
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1]
  exact hIntOn.mono_set (fun t ht => ⟨ht.1.le, ht.2.trans hx.2⟩)

/-- The difference of two `H¹₀(0,1)` functions is an `H¹₀(0,1)` function whose weak
derivative is the difference of the weak derivatives. -/
private lemma exists_weakH10_sub (a b : WeakH10) :
    ∃ c : WeakH10, c.toFun = a.toFun - b.toFun ∧ c.weakDeriv = a.weakDeriv - b.weakDeriv := by
  refine ⟨{ toFun := a.toFun - b.toFun
            weakDeriv := a.weakDeriv - b.weakDeriv
            weakDeriv_memLp := a.weakDeriv_memLp.sub b.weakDeriv_memLp
            toFun_eq_integral := fun x hx => ?_
            integral_weakDeriv_eq_zero := ?_ }, rfl, rfl⟩
  · have h1 := weakH10_memLp_intervalIntegrable _ a.weakDeriv_memLp x hx
    have h2 := weakH10_memLp_intervalIntegrable _ b.weakDeriv_memLp x hx
    calc (a.toFun - b.toFun) x = a.toFun x - b.toFun x := rfl
      _ = (∫ t in (0 : ℝ)..x, a.weakDeriv t) - ∫ t in (0 : ℝ)..x, b.weakDeriv t := by
          rw [a.toFun_eq_integral x hx, b.toFun_eq_integral x hx]
      _ = ∫ t in (0 : ℝ)..x, a.weakDeriv t - b.weakDeriv t :=
          (intervalIntegral.integral_sub h1 h2).symm
      _ = ∫ t in (0 : ℝ)..x, (a.weakDeriv - b.weakDeriv) t := rfl
  · have h1 := weakH10_memLp_intervalIntegrable _ a.weakDeriv_memLp 1 ⟨zero_le_one, le_rfl⟩
    have h2 := weakH10_memLp_intervalIntegrable _ b.weakDeriv_memLp 1 ⟨zero_le_one, le_rfl⟩
    calc ∫ t in (0 : ℝ)..1, (a.weakDeriv - b.weakDeriv) t
        = ∫ t in (0 : ℝ)..1, a.weakDeriv t - b.weakDeriv t := rfl
      _ = (∫ t in (0 : ℝ)..1, a.weakDeriv t) - ∫ t in (0 : ℝ)..1, b.weakDeriv t :=
          intervalIntegral.integral_sub h1 h2
      _ = 0 := by rw [a.integral_weakDeriv_eq_zero, b.integral_weakDeriv_eq_zero, sub_zero]

lemma iterated_eq_product
    {t0 t1 : ℝ} (ht : t0 < t1)
    (g : ℝ → ℝ → ℝ)
    (hInt : Integrable (Function.uncurry g)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1))) :
    (∫ t in t0..t1, ∫ x in (0 : ℝ)..1, g t x)
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1,
          g p.1 p.2 ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have hS : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hInt' : IntegrableOn (Function.uncurry g)
      (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) (volume.prod volume) := hInt
  have hProd : (∫ t in Set.Icc t0 t1, ∫ x in Set.Icc (0 : ℝ) 1, g t x ∂volume ∂volume)
      = ∫ p in Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1, g p.1 p.2 ∂volume :=
    (setIntegral_prod (Function.uncurry g) hInt').symm
  rw [intervalIntegral.integral_of_le ht.le]
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp only [← integral_Icc_eq_integral_Ioc]
  rw [hProd, Measure.restrict_restrict hS, Set.inter_self]

/-- **Integrability of the weak integrand.** For `u` and `ux` in `L²` on the rectangle and `κ`
a.e. bounded and a.e. strongly measurable, the integrand of the weak equation is integrable on
the rectangle for every test function. -/
lemma weak_parabolic_integrand_integrable
    {t0 t1 : ℝ} {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ}
    (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    {u ux : ℝ → ℝ → ℝ}
    (hu : MemLp (Function.uncurry u) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hux : MemLp (Function.uncurry ux) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    {φ : ℝ → ℝ → ℝ} (hφ : ParabolicTest t0 t1 φ) :
    Integrable (fun p : ℝ × ℝ => -u p.1 p.2 * deriv (fun s => φ s p.2) p.1
        + κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  obtain ⟨hc1, hc2, -, -⟩ := parabolicTest_deriv_memLp φ hφ
  have hRm : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hRc : IsCompact (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have : IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hRc.measure_lt_top⟩
  have hbd : ∀ {f : ℝ × ℝ → ℝ}, Continuous f →
      MemLp f ∞ (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    intro f hf
    obtain ⟨C, hC⟩ := hRc.exists_bound_of_continuousOn hf.continuousOn
    exact memLp_top_of_bound hf.aestronglyMeasurable C
      ((ae_restrict_iff' hRm).mpr (Eventually.of_forall hC))
  have hκ_top : MemLp (Function.uncurry κ) ∞
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    memLp_top_of_bound hκ_meas (max |kmin| |kmax|) (hκ.mono fun p hp => by
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs hp.1 hp.2)
  have h1 : MemLp (fun p : ℝ × ℝ => -u p.1 p.2 * deriv (fun s => φ s p.2) p.1) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    hu.neg.fun_mul (hbd hc1)
  have h2' : MemLp (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    hκ_top.fun_mul hux
  have h2 : MemLp (fun p : ℝ × ℝ => κ p.1 p.2 * ux p.1 p.2 * deriv (fun y => φ p.1 y) p.2) 2
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    h2'.fun_mul (hbd hc2)
  exact (h1.add h2).integrable one_le_two

/-- **Differences of weak solutions.** Two solutions of the weak equation with the same forcing
differ by a solution of the homogeneous equation, provided both weak integrands are integrable
on the rectangle (`weak_parabolic_integrand_integrable` gives this when `u` and `ux` are in
`L²` there). -/
lemma weak_parabolic_sub
    {t0 t1 : ℝ} (ht : t0 < t1) {κ F : ℝ → ℝ → ℝ}
    (u₁ ux₁ u₂ ux₂ : ℝ → ℝ → ℝ)
    (hInt₁ : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Integrable (fun p : ℝ × ℝ => -u₁ p.1 p.2 * deriv (fun s => φ s p.2) p.1
        + κ p.1 p.2 * ux₁ p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hInt₂ : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      Integrable (fun p : ℝ × ℝ => -u₂ p.1 p.2 * deriv (fun s => φ s p.2) p.1
        + κ p.1 p.2 * ux₂ p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hWeak1 : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x)
    (hWeak2 : ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x)
        = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, F t x * φ t x) :
    ∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
      ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
          (-(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
            + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x) = 0 := by
  intro φ hφ
  have hI₁ := hInt₁ φ hφ
  have hI₂ := hInt₂ φ hφ
  have e1 := iterated_eq_product ht (fun t x =>
    -u₁ t x * deriv (fun s => φ s x) t + κ t x * ux₁ t x * deriv (fun y => φ t y) x) hI₁
  have e2 := iterated_eq_product ht (fun t x =>
    -u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x) hI₂
  have hfun : (fun t x => -(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
        + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x)
      = fun t x => (-u₁ t x * deriv (fun s => φ s x) t
          + κ t x * ux₁ t x * deriv (fun y => φ t y) x)
        - (-u₂ t x * deriv (fun s => φ s x) t + κ t x * ux₂ t x * deriv (fun y => φ t y) x) := by
    funext t x
    ring
  have e3 := iterated_eq_product ht (fun t x => -(u₁ t x - u₂ t x) * deriv (fun s => φ s x) t
        + κ t x * (ux₁ t x - ux₂ t x) * deriv (fun y => φ t y) x)
    (by rw [hfun]; exact hI₁.sub hI₂)
  have hfun' : (fun p : ℝ × ℝ => -(u₁ p.1 p.2 - u₂ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + κ p.1 p.2 * (ux₁ p.1 p.2 - ux₂ p.1 p.2) * deriv (fun y => φ p.1 y) p.2)
      = fun p : ℝ × ℝ => (-u₁ p.1 p.2 * deriv (fun s => φ s p.2) p.1
          + κ p.1 p.2 * ux₁ p.1 p.2 * deriv (fun y => φ p.1 y) p.2)
        - (-u₂ p.1 p.2 * deriv (fun s => φ s p.2) p.1
          + κ p.1 p.2 * ux₂ p.1 p.2 * deriv (fun y => φ p.1 y) p.2) := by
    funext p
    ring
  rw [e3, hfun', integral_sub hI₁.restrict hI₂.restrict, ← e1, ← e2, hWeak1 φ hφ, hWeak2 φ hφ,
    sub_self]

/-! ## C. Uniqueness -/

/-- **Vanishing from the energy identity.** Let the time slices `w τ`, `τ ∈ [t0, t1]`, be in
`L²(0,1)`. If `w` satisfies the energy identity on `[t0, t1]` and `w t0 = 0` almost everywhere
on `[0, 1]`, then `w τ = 0` almost everywhere on `[0, 1]` at every time `τ` of `[t0, t1]`: the
dissipation `∫∫ κ (∂ₓw)²` is nonnegative because `κ ≥ kmin > 0`, so the energy identity forces
`‖w τ‖ = 0`, and the norm is finite. -/
lemma weak_parabolic_unique_of_energy
    {t0 t1 : ℝ} {κ : ℝ → ℝ → ℝ} {kmin : ℝ} (hkmin : 0 < kmin)
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)), kmin ≤ κ p.1 p.2)
    (w wx : ℝ → ℝ → ℝ)
    (hmem : ∀ τ ∈ Set.Icc t0 t1, MemLp (fun x => w τ x) 2 (volume.restrict (Set.Icc 0 1)))
    (hEnergy : ∀ τ : ℝ, τ ∈ Set.Icc t0 t1 →
      (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2
        = (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)
    (hInit : (fun x => w t0 x) =ᵐ[volume.restrict (Set.Icc 0 1)] 0) :
    ∀ τ ∈ Set.Icc t0 t1, (fun x => w τ x) =ᵐ[volume.restrict (Set.Icc 0 1)] 0 := by
  have hEq : (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) : Measure (ℝ × ℝ))
      = (volume.restrict (Set.Icc t0 t1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [hEq] at hκ
  have hκ_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), kmin ≤ κ t x :=
    Measure.ae_ae_of_ae_prod hκ
  have hInit' : (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal = 0 := by
    rw [eLpNorm_congr_ae hInit, eLpNorm_zero, ENNReal.toReal_zero]
  intro τ hτ
  obtain ⟨hτlo, hτhi⟩ := Set.mem_Icc.mp hτ
  have hE := hEnergy τ hτ
  rw [hInit'] at hE
  have hinner_ae : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      0 ≤ ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2 := by
    filter_upwards [hκ_ae] with t ht
    apply intervalIntegral.integral_nonneg_of_ae_restrict zero_le_one
    filter_upwards [ht] with x hx
    exact mul_nonneg (le_trans hkmin.le hx) (sq_nonneg _)
  have hB : 0 ≤ ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2 := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hτlo
    exact ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hτhi) hinner_ae
  have hA : 0 ≤ (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal :=
    ENNReal.toReal_nonneg
  have hsq : (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
      = 0 := by
    nlinarith
  have hnorm : eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp ((pow_eq_zero_iff two_ne_zero).mp hsq)).resolve_right
      (hmem τ hτ).eLpNorm_ne_top
  exact (eLpNorm_eq_zero_iff two_ne_zero).mp hnorm

/-- **Uniqueness of weak solutions of `∂ₜu = ∂ₓ(κ ∂ₓu) + F` on `(0, 1)`.**

Let `κ` be a.e. strongly measurable on the rectangle `[t0, t1] × [0, 1]` with
`0 < kmin ≤ κ ≤ kmax` a.e. Two solutions `(u, ux)` and `(u', ux')` of the class
`IsWeakParabolicSolution` with the same forcing `F` and the same initial value `u0`,
`u t0 = u0 = u' t0` in `L²(0,1)`, agree in `L²(0,1)` at every time of `[t0, t1]`.

The energy identity `‖w τ‖² + 2 ∫_{t0}^{τ} ∫₀¹ κ (∂ₓw)² = ‖w t0‖²` for the solutions `w` of
the homogeneous equation (`F = 0`) in the same class is an explicit hypothesis, `hEnergyId`.
It is the energy identity of weak solutions (Evans, §5.9.2, Theorem 3, applied as in the
uniqueness proof of §7.1.2), which holds for every such `κ`; this module does not prove it.
The proof subtracts the two solutions, which gives a solution of the homogeneous equation
with zero initial value, and the identity with `κ ≥ kmin > 0` forces its `L²(0,1)` norm to
vanish at every time. -/
theorem weak_parabolic_unique
    {t0 t1 : ℝ} (ht : t0 < t1)
    {κ : ℝ → ℝ → ℝ} {kmin kmax : ℝ} (hkmin : 0 < kmin)
    (hκ_meas : AEStronglyMeasurable (Function.uncurry κ)
      (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    (hκ : ∀ᵐ p ∂(volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)),
      kmin ≤ κ p.1 p.2 ∧ κ p.1 p.2 ≤ kmax)
    (hEnergyId : ∀ w wx : ℝ → ℝ → ℝ, IsWeakParabolicSolution t0 t1 κ 0 w wx →
      ∀ τ ∈ Set.Icc t0 t1,
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ∫ t in t0..τ, ∫ x in (0 : ℝ)..1, κ t x * (wx t x) ^ 2
          = (eLpNorm (fun x => w t0 x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
    {F : ℝ → ℝ → ℝ} {u0 : ℝ → ℝ} {u ux u' ux' : ℝ → ℝ → ℝ}
    (hu : IsWeakParabolicSolution t0 t1 κ F u ux)
    (hu' : IsWeakParabolicSolution t0 t1 κ F u' ux')
    (hinit : eLpNorm (fun x => u t0 x - u0 x) 2 (volume.restrict (Set.Icc 0 1)) = 0)
    (hinit' : eLpNorm (fun x => u' t0 x - u0 x) 2 (volume.restrict (Set.Icc 0 1)) = 0) :
    ∀ t ∈ Set.Icc t0 t1, (fun x => u' t x) =ᵐ[volume.restrict (Set.Icc 0 1)] fun x => u t x := by
  intro τ hτ
  have hsol : IsWeakParabolicSolution t0 t1 κ 0
      (fun t x => u' t x - u t x) (fun t x => ux' t x - ux t x) := by
    refine ⟨fun t ht => (hu'.memLp_slice t ht).sub (hu.memLp_slice t ht), ?_, ?_,
      hu'.memLp.sub hu.memLp, hu'.memLp_deriv.sub hu.memLp_deriv, fun φ _ => by simp, ?_⟩
    · intro s hs
      have hsum := (hu'.continuous_slice s hs).add (hu.continuous_slice s hs)
      rw [add_zero] at hsum
      refine squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) ?_ hsum
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h1 : MemLp (fun x => u' t x - u' s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (hu'.memLp_slice t ht).sub (hu'.memLp_slice s hs)
      have h2 : MemLp (fun x => u t x - u s x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (hu.memLp_slice t ht).sub (hu.memLp_slice s hs)
      have hsplit : (fun x => (u' t x - u t x) - (u' s x - u s x))
          = (fun x => u' t x - u' s x) - (fun x => u t x - u s x) := by
        funext x
        simp only [Pi.sub_apply]
        ring
      change (eLpNorm (fun x => (u' t x - u t x) - (u' s x - u s x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ _
      rw [hsplit, ← ENNReal.toReal_add h1.eLpNorm_ne_top h2.eLpNorm_ne_top]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1.eLpNorm_ne_top, h2.eLpNorm_ne_top⟩)
        (eLpNorm_sub_le one_le_two)
    · filter_upwards [hu.profile, hu'.profile] with t ht ht'
      obtain ⟨h, hh1, hh2⟩ := ht
      obtain ⟨h', hh1', hh2'⟩ := ht'
      obtain ⟨c, hc1, hc2⟩ := exists_weakH10_sub h' h
      exact ⟨c, hc1 ▸ hh1'.sub hh1, hc2 ▸ hh2'.sub hh2⟩
    · intro φ hφ
      exact (weak_parabolic_sub ht u' ux' u ux
        (fun _ hφ => weak_parabolic_integrand_integrable hκ_meas hκ hu'.memLp hu'.memLp_deriv hφ)
        (fun _ hφ => weak_parabolic_integrand_integrable hκ_meas hκ hu.memLp hu.memLp_deriv hφ)
        hu'.weak_eq hu.weak_eq φ hφ).trans (by simp)
  have hW0 : (fun x => u' t0 x - u t0 x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0 := by
    filter_upwards [(eLpNorm_eq_zero_iff two_ne_zero).mp hinit,
      (eLpNorm_eq_zero_iff two_ne_zero).mp hinit'] with x hx hx'
    simp only [Pi.zero_apply] at hx hx' ⊢
    linarith
  have hzero := weak_parabolic_unique_of_energy hkmin (hκ.mono fun _ hp => hp.1)
    (fun t x => u' t x - u t x) (fun t x => ux' t x - ux t x) hsol.memLp_slice
    (hEnergyId _ _ hsol) hW0 τ hτ
  filter_upwards [hzero] with x hx
  simp only [Pi.zero_apply] at hx
  linarith

end EarthScience
