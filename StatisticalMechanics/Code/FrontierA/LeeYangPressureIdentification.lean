/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Code.FrontierA.LeeYangPressurePrimitive

open Complex Filter Set Topology

namespace StatMech.FrontierA

open StatMech.FK

private theorem leeYang_pressureDerivative_tendstoLocallyUniformlyOn
    (d : ℕ) (beta : ℝ) (g : ℂ → ℂ) (U : Set ℂ) (I : Set ℝ)
    (hmap : MapsTo (fun h : ℝ => (h : ℂ)) I U)
    (hlimit : TendstoLocallyUniformlyOn
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      g atTop U) :
    TendstoLocallyUniformlyOn
      (fun n h => isingBoxPressureFieldDerivative d n beta h)
      (fun h => (g (h : ℂ)).re) atTop I := by
  have hpre := hlimit.comp (fun h : ℝ => (h : ℂ)) hmap
    Complex.continuous_ofReal.continuousOn
  have hre := Complex.reCLM.uniformContinuous.comp_tendstoLocallyUniformlyOn hpre
  have hF : (fun n => (Complex.reCLM : ℂ → ℝ) ∘
      leeYangNormalizedFieldLogDerivative (boxGraph d n) beta ∘
        fun h : ℝ => (h : ℂ)) =
      (fun n h => isingBoxPressureFieldDerivative d n beta h) := by
    funext n h
    rw [Function.comp_apply, Function.comp_apply,
      leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative]
    simp
  rw [hF] at hre
  simpa only [Function.comp_apply] using hre

private theorem leeYang_halfPlaneLimit_im_ofReal_eq_zero
    (d : ℕ) (beta : ℝ) (g : ℂ → ℂ) (U : Set ℂ)
    (hlimit : TendstoLocallyUniformlyOn
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      g atTop U)
    (h : ℝ) (hh : (h : ℂ) ∈ U) :
    (g (h : ℂ)).im = 0 := by
  have ht := hlimit.tendsto_at hh
  have him := Complex.continuous_im.continuousAt.tendsto.comp ht
  have hzero : Tendsto
      (fun n => (leeYangNormalizedFieldLogDerivative
        (boxGraph d n) beta (h : ℂ)).im) atTop (nhds 0) := by
    have heq : (fun n => (leeYangNormalizedFieldLogDerivative
        (boxGraph d n) beta (h : ℂ)).im) = fun _ => 0 := by
      funext n
      rw [leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative]
      simp
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique him hzero

private theorem isingBoxPressureLimit_hasDerivAt_of_halfPlaneLimit
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) (g : ℂ → ℂ)
    (U : Set ℂ) (I : Set ℝ) (hIopen : IsOpen I)
    (hmap : MapsTo (fun h : ℝ => (h : ℂ)) I U)
    (hlimit : TendstoLocallyUniformlyOn
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      g atTop U)
    (h : ℝ) (hh : h ∈ I) :
    HasDerivAt (isingBoxPressureLimit d hd beta)
      (g (h : ℂ)).re h := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hIopen
    (leeYang_pressureDerivative_tendstoLocallyUniformlyOn
      d beta g U I hmap hlimit)
  · exact Filter.Eventually.of_forall (fun n x _ =>
      isingBoxPressureSeq_hasDerivAt_field d n beta x)
  · intro x _
    exact isingBoxPressure_tendsto_limit d hd beta x
  · exact hh

private theorem leeYangPressurePrimitive_eq_real_of_halfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    (U : Set ℂ) (I : Set ℝ)
    (hUopen : IsOpen U) (hIopen : IsOpen I) (hIconn : IsPreconnected I)
    (hmap : MapsTo (fun h : ℝ => (h : ℂ)) I U)
    (P g : ℂ → ℂ) (h₀ : ℝ) (hh₀ : h₀ ∈ I)
    (hanchor : P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ))
    (hlimit : TendstoLocallyUniformlyOn
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      g atTop U)
    (hPdiff : DifferentiableOn ℂ P U)
    (hPderiv : Set.EqOn (deriv P) g U) :
    ∀ h ∈ I, P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ) := by
  let f : ℝ → ℂ := fun h => P (h : ℂ)
  let q : ℝ → ℂ := fun h => (isingBoxPressureLimit d hd beta h : ℂ)
  have hfderiv : ∀ h ∈ I, HasDerivAt f (g (h : ℂ)) h := by
    intro h hh
    have hhU := hmap hh
    have hP := (hPdiff (h : ℂ) hhU).differentiableAt
      (hUopen.mem_nhds hhU) |>.hasDerivAt
    rw [hPderiv hhU] at hP
    exact hP.comp_ofReal
  have hqderiv : ∀ h ∈ I, HasDerivAt q (g (h : ℂ)) h := by
    intro h hh
    have hp := isingBoxPressureLimit_hasDerivAt_of_halfPlaneLimit
      d hd beta g U I hIopen hmap hlimit h hh
    have hpComplex := hp.ofReal_comp
    have him := leeYang_halfPlaneLimit_im_ofReal_eq_zero
      d beta g U hlimit h (hmap hh)
    have hgeq : ((g (h : ℂ)).re : ℂ) = g (h : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him.symm
    rw [← hgeq]
    simpa only [q] using hpComplex
  have hfdiff : DifferentiableOn ℝ f I :=
    fun h hh => (hfderiv h hh).differentiableAt.differentiableWithinAt
  have hqdiff : DifferentiableOn ℝ q I :=
    fun h hh => (hqderiv h hh).differentiableAt.differentiableWithinAt
  have hdeq : Set.EqOn (deriv f) (deriv q) I := by
    intro h hh
    rw [(hfderiv h hh).deriv, (hqderiv h hh).deriv]
  have heq := hIopen.eqOn_of_deriv_eq hIconn hfdiff hqdiff hdeq hh₀
    (by simpa only [f, q] using hanchor)
  intro h hh
  exact heq hh



theorem leeYangPressurePrimitive_eq_real_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    (P g : ℂ → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hanchor : P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ))
    (hlimit : TendstoLocallyUniformlyOn
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      g atTop {z : ℂ | 0 < z.re})
    (hPdiff : DifferentiableOn ℂ P {z : ℂ | 0 < z.re})
    (hPderiv : Set.EqOn (deriv P) g {z : ℂ | 0 < z.re}) :
    ∀ h : ℝ, 0 < h →
      P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ) := by
  exact leeYangPressurePrimitive_eq_real_of_halfPlane
    d hd beta {z : ℂ | 0 < z.re} (Ioi 0)
    (isOpen_lt continuous_const Complex.continuous_re) isOpen_Ioi
    (convex_Ioi (0 : ℝ)).isPreconnected
    (by intro h hh; simpa using hh) P g h₀ hh₀
    hanchor hlimit hPdiff hPderiv


theorem leeYangPressurePrimitive_eq_real_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    (P g : ℂ → ℂ) (h₀ : ℝ) (hh₀ : h₀ < 0)
    (hanchor : P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ))
    (hlimit : TendstoLocallyUniformlyOn
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      g atTop {z : ℂ | z.re < 0})
    (hPdiff : DifferentiableOn ℂ P {z : ℂ | z.re < 0})
    (hPderiv : Set.EqOn (deriv P) g {z : ℂ | z.re < 0}) :
    ∀ h : ℝ, h < 0 →
      P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ) := by
  exact leeYangPressurePrimitive_eq_real_of_halfPlane
    d hd beta {z : ℂ | z.re < 0} (Iio 0)
    (isOpen_lt Complex.continuous_re continuous_const) isOpen_Iio
    (convex_Iio (0 : ℝ)).isPreconnected
    (by intro h hh; simpa using hh) P g h₀ hh₀
    hanchor hlimit hPdiff hPderiv




theorem leeYangBox_holomorphicPressure_rightHalfPlane_identified
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (h₀ : ℝ) (hh₀ : 0 < h₀) :
    ∃ (P g : ℂ → ℂ),
      P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ) ∧
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ P {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      Set.EqOn (deriv P) g {z : ℂ | 0 < z.re} ∧
      (∀ h : ℝ, 0 < h →
        P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ)) := by
  obtain ⟨P, g, hanchor, hlimit, hPdiff, hg, hPderiv, _⟩ :=
    leeYangBox_holomorphicPressure_rightHalfPlane d hd hbeta h₀ hh₀
  exact ⟨P, g, hanchor, hlimit, hPdiff, hg, hPderiv,
    leeYangPressurePrimitive_eq_real_rightHalfPlane
      d hd beta P g h₀ hh₀ hanchor hlimit hPdiff hPderiv⟩


theorem leeYangBox_holomorphicPressure_leftHalfPlane_identified
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (h₀ : ℝ) (hh₀ : h₀ < 0) :
    ∃ (P g : ℂ → ℂ),
      P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ) ∧
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ P {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      Set.EqOn (deriv P) g {z : ℂ | z.re < 0} ∧
      (∀ h : ℝ, h < 0 →
        P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ)) := by
  obtain ⟨P, g, hanchor, hlimit, hPdiff, hg, hPderiv, _⟩ :=
    leeYangBox_holomorphicPressure_leftHalfPlane d hd hbeta h₀ hh₀
  exact ⟨P, g, hanchor, hlimit, hPdiff, hg, hPderiv,
    leeYangPressurePrimitive_eq_real_leftHalfPlane
      d hd beta P g h₀ hh₀ hanchor hlimit hPdiff hPderiv⟩

end StatMech.FrontierA
