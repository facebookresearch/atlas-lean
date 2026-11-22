/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.ClassicalColeHopf
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cole–Hopf on open time-space domains

The classical residual identity only needs joint `C³` regularity on an open
product `I × J`. No regularity, nonvanishing or PDE hypothesis is imposed outside
that product. In particular `I = Set.Ioi 0` permits singular behavior at time zero.
Spatial and temporal derivatives below are ordinary derivatives at interior points.
Connectedness is unnecessary for these differential identities.

This localizes the quotient calculation of Gesztesy and Holden,
*The Cole–Hopf and Miura transformations revisited*, Lemmas 3.1–3.2 and
Theorem 3.3(ii), https://arxiv.org/abs/solv-int/9812025, using joint `C³`
regularity as a sufficient (rather than minimal anisotropic) assumption.
-/

@[expose] public section

open Set
open scoped ContDiff Topology

namespace ColeHopf.OnInterval

variable {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)

include hI hJ

private theorem hasDerivAt_space {φ : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (Function.uncurry φ) (I ×ˢ J)) (hn : n ≠ 0)
    (t x : ℝ) (ht : t ∈ I) (hx : x ∈ J) :
    HasDerivAt (φ t) (fderiv ℝ (Function.uncurry φ) (t, x) (0, 1)) x := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
    ((h.contDiffAt ((hI.prod hJ).mem_nhds ⟨ht, hx⟩)).differentiableAt hn).hasFDerivAt
      |>.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))

private theorem hasDerivAt_time {φ : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (Function.uncurry φ) (I ×ˢ J)) (hn : n ≠ 0)
    (t x : ℝ) (ht : t ∈ I) (hx : x ∈ J) :
    HasDerivAt (fun s => φ s x) (fderiv ℝ (Function.uncurry φ) (t, x) (1, 0)) t := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
    ((h.contDiffAt ((hI.prod hJ).mem_nhds ⟨ht, hx⟩)).differentiableAt hn).hasFDerivAt
      |>.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

/-- Spatial differentiation loses one order of regularity inside the open product. -/
theorem contDiffOn_spaceDeriv {φ : ℝ → ℝ → ℝ} {m n : ℕ∞ω}
    (h : ContDiffOn ℝ n (Function.uncurry φ) (I ×ˢ J))
    (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContDiffOn ℝ m (Function.uncurry (fun t x => deriv (φ t) x)) (I ×ˢ J) := by
  refine ((h.fderiv_of_isOpen (hI.prod hJ) hm).clm_apply
    (contDiffOn_const (c := (0, 1)))).congr ?_
  intro p hp
  exact (hasDerivAt_space hI hJ h hn p.1 p.2 hp.1 hp.2).deriv

/-- Temporal differentiation loses one order of regularity inside the open product. -/
theorem contDiffOn_timeDeriv {φ : ℝ → ℝ → ℝ} {m n : ℕ∞ω}
    (h : ContDiffOn ℝ n (Function.uncurry φ) (I ×ˢ J))
    (hn : n ≠ 0) (hm : m + 1 ≤ n) :
    ContDiffOn ℝ m (Function.uncurry (fun t x => deriv (fun s => φ s x) t)) (I ×ˢ J) := by
  refine ((h.fderiv_of_isOpen (hI.prod hJ) hm).clm_apply
    (contDiffOn_const (c := (1, 0)))).congr ?_
  intro p hp
  exact (hasDerivAt_time hI hJ h hn p.1 p.2 hp.1 hp.2).deriv

/-- Ordinary spatial derivative at an interior point. -/
theorem space_derivative {φ : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (Function.uncurry φ) (I ×ˢ J)) (hn : n ≠ 0)
    (t x : ℝ) (ht : t ∈ I) (hx : x ∈ J) :
    HasDerivAt (φ t) (deriv (φ t) x) x :=
  (hasDerivAt_space hI hJ h hn t x ht hx).differentiableAt.hasDerivAt

/-- Ordinary temporal derivative at an interior point. -/
theorem time_derivative {φ : ℝ → ℝ → ℝ} {n : ℕ∞ω}
    (h : ContDiffOn ℝ n (Function.uncurry φ) (I ×ˢ J)) (hn : n ≠ 0)
    (t x : ℝ) (ht : t ∈ I) (hx : x ∈ J) :
    HasDerivAt (fun s => φ s x) (deriv (fun s => φ s x) t) t :=
  (hasDerivAt_time hI hJ h hn t x ht hx).differentiableAt.hasDerivAt

private theorem mixed_deriv_eq {φ : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (ht : t ∈ I) (hx : x ∈ J) :
    deriv (fun s => deriv (φ s) x) t =
      deriv (fun y => deriv (fun s => φ s y) t) x := by
  let f := Function.uncurry φ
  have ha : ContDiffAt ℝ 3 (Function.uncurry φ) (t, x) :=
    h.contDiffAt ((hI.prod hJ).mem_nhds ⟨ht, hx⟩)
  have hfd := (ha.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have he (v w : ℝ × ℝ) :
      fderiv ℝ (fun p => fderiv ℝ f p v) (t, x) w =
        fderiv ℝ (fderiv ℝ f) (t, x) w v := by
    have hh := hfd.hasFDerivAt.clm_apply (hasFDerivAt_const v (t, x))
    simpa using congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) hh.fderiv
  have es : (fun s => deriv (φ s) x) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (s, x) (0, 1)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (hasDerivAt_space hI hJ h (by norm_num) s x hs hx).deriv
  have et : (fun y => deriv (fun s => φ s y) t) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f (t, y) (1, 0)) := by
    filter_upwards [hJ.mem_nhds hx] with y hy
    exact (hasDerivAt_time hI hJ h (by norm_num) t y ht hy).deriv
  rw [es.deriv_eq, et.deriv_eq]
  have hc (v : ℝ × ℝ) : ContDiffOn ℝ 2 (fun p => fderiv ℝ f p v) (I ×ˢ J) :=
    (h.fderiv_of_isOpen (hI.prod hJ) (by norm_num)).clm_apply contDiffOn_const
  rw [(hasDerivAt_time hI hJ (φ := fun t x => fderiv ℝ f (t, x) (0, 1))
      (hc (0, 1)) (by norm_num) t x ht hx).deriv,
    (hasDerivAt_space hI hJ (φ := fun t x => fderiv ℝ f (t, x) (1, 0))
      (hc (1, 0)) (by norm_num) t x ht hx).deriv]
  exact (he (0, 1) (1, 0)).trans
    (((ha.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)).trans
      (he (1, 0) (0, 1)).symm)

/-- The transform is jointly `C²` on the nonzero part of the open domain. -/
theorem classicalTransform_contDiffOn (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (hp : ∀ p ∈ I ×ˢ J, φ p.1 p.2 ≠ 0) :
    ContDiffOn ℝ 2 (Function.uncurry (classicalTransform ν φ)) (I ×ˢ J) :=
  contDiffOn_const.mul ((contDiffOn_spaceDeriv hI hJ hφ (by norm_num) (by norm_num)).div
    (hφ.of_le (by norm_num)) hp)

/-- Spatial quotient rule for the classical transform. -/
theorem classicalTransform_hasDerivAt_x (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (htI : t ∈ I) (hxJ : x ∈ J) (h : φ t x ≠ 0) :
    HasDerivAt (classicalTransform ν φ t)
      (-2 * ν * ((deriv (deriv (φ t)) x * φ t x -
        deriv (φ t) x * deriv (φ t) x) / φ t x ^ 2)) x := by
  have hx := contDiffOn_spaceDeriv hI hJ hφ (by norm_num) (m := 2) (by norm_num)
  exact ((space_derivative hI hJ hx (by norm_num) t x htI hxJ).div
    (space_derivative hI hJ hφ (by norm_num) t x htI hxJ) h).const_mul (-2 * ν)

/-- Time quotient rule; the mixed derivative is the derivative of the time slice. -/
theorem classicalTransform_hasDerivAt_t (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (htI : t ∈ I) (hxJ : x ∈ J) (h : φ t x ≠ 0) :
    HasDerivAt (fun s => classicalTransform ν φ s x)
      (-2 * ν * ((deriv (fun y => deriv (fun s => φ s y) t) x * φ t x -
        deriv (φ t) x * deriv (fun s => φ s x) t) / φ t x ^ 2)) t := by
  have hx := contDiffOn_spaceDeriv hI hJ hφ (by norm_num) (m := 2) (by norm_num)
  have hd := ((time_derivative hI hJ hx (by norm_num) t x htI hxJ).div
    (time_derivative hI hJ hφ (by norm_num) t x htI hxJ) h).const_mul (-2 * ν)
  simpa only [mixed_deriv_eq hI hJ hφ t x htI hxJ] using! hd

/-- Second spatial quotient derivative, justified on the local nonzero locus. -/
theorem classicalTransform_iteratedDeriv_two (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (htI : t ∈ I) (hxJ : x ∈ J) (h : φ t x ≠ 0) :
    iteratedDeriv 2 (classicalTransform ν φ t) x =
      -2 * ν * (deriv (deriv (deriv (φ t))) x / φ t x -
        3 * deriv (φ t) x * deriv (deriv (φ t)) x / φ t x ^ 2 +
        2 * deriv (φ t) x ^ 3 / φ t x ^ 3) := by
  have hx := contDiffOn_spaceDeriv hI hJ hφ (by norm_num) (m := 2) (by norm_num)
  have hxx := contDiffOn_spaceDeriv hI hJ hx (by norm_num) (m := 1) (by norm_num)
  have h0 := space_derivative hI hJ hφ (by norm_num) t x htI hxJ
  have h1 := space_derivative hI hJ hx (by norm_num) t x htI hxJ
  have h2 := space_derivative hI hJ hxx (by norm_num) t x htI hxJ
  have hd := (((h2.mul h0).sub (h1.mul h1)).div
    (h0.pow 2) (pow_ne_zero 2 h)).const_mul (-2 * ν)
  have heq : deriv (classicalTransform ν φ t) =ᶠ[𝓝 x]
      (fun y => -2 * ν * ((deriv (deriv (φ t)) y * φ t y -
        deriv (φ t) y * deriv (φ t) y) / φ t y ^ 2)) := by
    filter_upwards [h0.continuousAt.eventually_ne h, hJ.mem_nhds hxJ] with y hy hyJ
    exact (classicalTransform_hasDerivAt_x hI hJ ν φ hφ t y htI hyJ hy).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (hd.congr_of_eventuallyEq heq).deriv]
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

/-- Cole–Hopf intertwines the classical Burgers and normalized heat residuals. -/
theorem classicalTransform_residual (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (htI : t ∈ I) (hxJ : x ∈ J) (h : φ t x ≠ 0) :
    deriv (fun s => classicalTransform ν φ s x) t +
        classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x -
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x =
      -2 * ν * deriv (fun y =>
        (deriv (fun s => φ s y) t - ν * iteratedDeriv 2 (φ t) y) / φ t y) x := by
  have hx := contDiffOn_spaceDeriv hI hJ hφ (by norm_num) (m := 2) (by norm_num)
  have hxx := contDiffOn_spaceDeriv hI hJ hx (by norm_num) (m := 1) (by norm_num)
  have ht := contDiffOn_timeDeriv hI hJ hφ (by norm_num) (m := 2) (by norm_num)
  have hd := ((space_derivative hI hJ ht (by norm_num) t x htI hxJ).sub
    ((space_derivative hI hJ hxx (by norm_num) t x htI hxJ).const_mul ν)).div
      (space_derivative hI hJ hφ (by norm_num) t x htI hxJ) h
  rw [(classicalTransform_hasDerivAt_t hI hJ ν φ hφ t x htI hxJ h).deriv,
    (classicalTransform_hasDerivAt_x hI hJ ν φ hφ t x htI hxJ h).deriv,
    classicalTransform_iteratedDeriv_two hI hJ ν φ hφ t x htI hxJ h]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hd' : deriv (fun y =>
      (deriv (fun s => φ s y) t - ν * deriv (deriv (φ t)) y) / φ t y) x =
      ((deriv (fun y => deriv (fun s => φ s y) t) x -
        ν * deriv (deriv (deriv (φ t))) x) * φ t x -
        (deriv (fun s => φ s x) t - ν * deriv (deriv (φ t)) x) * deriv (φ t) x) /
        φ t x ^ 2 := hd.deriv
  rw [hd']
  unfold classicalTransform
  field_simp
  ring

/-- A heat equation on a spatial neighborhood gives Burgers at the point. -/
theorem classicalTransform_burgers (ν : ℝ) (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (htI : t ∈ I) (hxJ : x ∈ J) (h : φ t x ≠ 0)
    (hheat : ∀ᶠ y in 𝓝 x,
      deriv (fun s => φ s y) t = ν * iteratedDeriv 2 (φ t) y) :
    deriv (fun s => classicalTransform ν φ s x) t +
      classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x =
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x := by
  have heq : (fun y =>
      (deriv (fun s => φ s y) t - ν * iteratedDeriv 2 (φ t) y) / φ t y) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hheat] with y hy
    simp [hy]
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  have hr := classicalTransform_residual hI hJ ν φ hφ t x htI hxJ h
  rw [hz.deriv, mul_zero] at hr
  exact sub_eq_zero.mp hr

/-- A heat equation with potential `F` gives Burgers with forcing `-2ν Fₓ`.
Only spatial differentiability of `F` at the evaluation point is required. -/
theorem classicalTransform_forced_burgers (ν : ℝ) (φ F : ℝ → ℝ → ℝ)
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (I ×ˢ J))
    (t x : ℝ) (htI : t ∈ I) (hxJ : x ∈ J) (h : φ t x ≠ 0)
    (hF : DifferentiableAt ℝ (F t) x)
    (hheat : ∀ᶠ y in 𝓝 x,
      deriv (fun s => φ s y) t = ν * iteratedDeriv 2 (φ t) y + F t y * φ t y) :
    deriv (fun s => classicalTransform ν φ s x) t +
        classicalTransform ν φ t x * deriv (classicalTransform ν φ t) x -
        ν * iteratedDeriv 2 (classicalTransform ν φ t) x =
      -2 * ν * deriv (F t) x := by
  have hn := (space_derivative hI hJ hφ (by norm_num) t x htI hxJ).continuousAt.eventually_ne h
  have heq : (fun y =>
      (deriv (fun s => φ s y) t - ν * iteratedDeriv 2 (φ t) y) / φ t y) =ᶠ[𝓝 x]
        F t := by
    filter_upwards [hheat, hn] with y hy hny
    rw [hy]
    field_simp
    ring
  rw [classicalTransform_residual hI hJ ν φ hφ t x htI hxJ h,
    (hF.hasDerivAt.congr_of_eventuallyEq heq).deriv]

end ColeHopf.OnInterval
