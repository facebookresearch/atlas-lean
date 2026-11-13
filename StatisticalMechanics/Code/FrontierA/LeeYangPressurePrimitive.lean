/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Mathlib.Analysis.Complex.HasPrimitives
import Code.FrontierA.LeeYangHalfPlaneDiagonal

open Complex Filter Metric Set Topology

namespace StatMech.FrontierA

open StatMech.FK


noncomputable def leeYangRightCayley (z : ℂ) : ℂ := (z - 1) / (z + 1)


noncomputable def leeYangRightCayleyInv (w : ℂ) : ℂ := (1 + w) / (1 - w)

theorem leeYangRightCayley_mem_ball {z : ℂ} (hz : 0 < z.re) :
    leeYangRightCayley z ∈ ball 0 1 := by
  rw [mem_ball, dist_zero_right, leeYangRightCayley, norm_div, div_lt_one]
  · rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, sub_re, one_re, sub_im, one_im,
      add_re, add_im]
    nlinarith
  · exact norm_pos_iff.mpr (by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith)

theorem leeYangRightCayleyInv_mem {w : ℂ} (hw : w ∈ ball 0 1) :
    0 < (leeYangRightCayleyInv w).re := by
  rw [mem_ball, dist_zero_right] at hw
  rw [leeYangRightCayleyInv, Complex.div_re]
  have hden : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr (by
    intro h
    have hw1 : w = 1 := (sub_eq_zero.mp h).symm
    rw [hw1] at hw
    norm_num at hw)
  have heq :
      (1 + w).re * (1 - w).re / Complex.normSq (1 - w) +
          (1 + w).im * (1 - w).im / Complex.normSq (1 - w) =
        (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    simp only [add_re, one_re, sub_re, add_im, one_im, sub_im,
      Complex.normSq_apply]
    field_simp
    ring
  rw [heq]
  exact div_pos (by
    rw [sub_pos, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]) hden

theorem leeYangRightCayleyInv_cayley (z : ℂ) (hz : z ≠ -1) :
    leeYangRightCayleyInv (leeYangRightCayley z) = z := by
  simp only [leeYangRightCayleyInv, leeYangRightCayley]
  have hz1 : z + 1 ≠ 0 := by
    intro h
    apply hz
    calc
      z = (z + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  field_simp [hz1]
  ring

theorem hasDerivAt_leeYangRightCayley (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt leeYangRightCayley (2 / (z + 1) ^ 2) z := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have h := ((hasDerivAt_id z).sub (hasDerivAt_const z 1)).div
    ((hasDerivAt_id z).add (hasDerivAt_const z 1)) hz1
  convert h using 1
  simp only [id_eq, Pi.sub_apply, Pi.add_apply, sub_zero, add_zero,
    one_mul, mul_one]
  ring

theorem hasDerivAt_leeYangRightCayleyInv (w : ℂ) (hw : w ∈ ball 0 1) :
    HasDerivAt leeYangRightCayleyInv (2 / (1 - w) ^ 2) w := by
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have hwone : w = 1 := (sub_eq_zero.mp h).symm
    rw [hwone, mem_ball, dist_zero_right] at hw
    norm_num at hw
  have h := ((hasDerivAt_const w 1).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w 1).sub (hasDerivAt_id w)) hw1
  convert h using 1
  simp only [id_eq, Pi.sub_apply, Pi.add_apply, zero_add,
    one_mul]
  ring

noncomputable def leeYangCayleyPulledDerivative
    (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  g (leeYangRightCayleyInv w) * (2 / (1 - w) ^ 2)

theorem leeYangCayleyPulledDerivative_differentiableOn
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re}) :
    DifferentiableOn ℂ (leeYangCayleyPulledDerivative g) (ball 0 1) := by
  intro w hw
  have hinv := hasDerivAt_leeYangRightCayleyInv w hw
  have hmem := leeYangRightCayleyInv_mem hw
  have hgAt : DifferentiableAt ℂ g (leeYangRightCayleyInv w) :=
    (hg _ hmem).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have hwone : w = 1 := (sub_eq_zero.mp h).symm
    rw [hwone, mem_ball, dist_zero_right] at hw
    norm_num at hw
  have hfactor : DifferentiableAt ℂ (fun u : ℂ => 2 / (1 - u) ^ 2) w :=
    ((hasDerivAt_const w 2).div
      (((hasDerivAt_const w 1).sub (hasDerivAt_id w)).pow 2)
      (pow_ne_zero 2 hw1)).differentiableAt
  simpa only [leeYangCayleyPulledDerivative] using
    ((hgAt.comp w hinv.differentiableAt).mul hfactor).differentiableWithinAt



theorem rightHalfPlane_normalizedPrimitive
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (h₀ : ℝ) (hh₀ : 0 < h₀) (p₀ : ℂ) :
    ∃ P : ℂ → ℂ,
      P (h₀ : ℂ) = p₀ ∧
      HasDerivAt P (g (h₀ : ℂ)) (h₀ : ℂ) ∧
      ∀ z, z ∈ {z : ℂ | 0 < z.re} → HasDerivAt P (g z) z := by
  have hpull := leeYangCayleyPulledDerivative_differentiableOn g hg
  obtain ⟨Q, hQanchor, hQ⟩ := hpull.isExactOn_ball.with_val_at
    (leeYangRightCayley (h₀ : ℂ)) p₀
  let P : ℂ → ℂ := Q ∘ leeYangRightCayley
  have hP : ∀ z, z ∈ {z : ℂ | 0 < z.re} → HasDerivAt P (g z) z := by
    intro z hz
    have hzc := leeYangRightCayley_mem_ball hz
    have hcayley := hasDerivAt_leeYangRightCayley z hz
    have hcomp := (hQ (leeYangRightCayley z) hzc).comp z hcayley
    have hzneg : z ≠ -1 := by
      intro heq
      rw [heq] at hz
      norm_num at hz
    have hinv := leeYangRightCayleyInv_cayley z hzneg
    rw [show P = Q ∘ leeYangRightCayley by rfl]
    convert hcomp using 1
    rw [leeYangCayleyPulledDerivative, hinv, leeYangRightCayley]
    have hz1 : z + 1 ≠ 0 := by
      intro h
      apply hzneg
      calc
        z = (z + 1) - 1 := by ring
        _ = -1 := by rw [h]; ring
    field_simp [hz1]
    ring
  refine ⟨P, hQanchor, hP (h₀ : ℂ) ?_, hP⟩
  simpa using hh₀



theorem leftHalfPlane_normalizedPrimitive
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | z.re < 0})
    (h₀ : ℝ) (hh₀ : h₀ < 0) (p₀ : ℂ) :
    ∃ P : ℂ → ℂ,
      P (h₀ : ℂ) = p₀ ∧
      HasDerivAt P (g (h₀ : ℂ)) (h₀ : ℂ) ∧
      ∀ z, z ∈ {z : ℂ | z.re < 0} → HasDerivAt P (g z) z := by
  let f : ℂ → ℂ := fun w => -g (-w)
  have hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.re} := by
    intro w hw
    change 0 < w.re at hw
    have hneg : (-w) ∈ {z : ℂ | z.re < 0} := by
      change -w.re < 0
      exact neg_neg_of_pos hw
    have hgAt : DifferentiableAt ℂ g (-w) :=
      (hg (-w) hneg).differentiableAt
        ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hneg)
    have hcomp := hgAt.comp w (hasDerivAt_neg w).differentiableAt
    simpa only [f, Function.comp_apply] using hcomp.neg.differentiableWithinAt
  obtain ⟨Q, hQanchor, _hQanchorDeriv, hQ⟩ :=
    rightHalfPlane_normalizedPrimitive f hf (-h₀) (neg_pos.mpr hh₀) p₀
  let P : ℂ → ℂ := Q ∘ fun z => -z
  have hP : ∀ z, z ∈ {z : ℂ | z.re < 0} → HasDerivAt P (g z) z := by
    intro z hz
    change z.re < 0 at hz
    have hneg : 0 < (-z).re := by
      change 0 < -z.re
      exact neg_pos.mpr hz
    have hcomp := (hQ (-z) hneg).comp z (hasDerivAt_neg z)
    simpa only [P, f, Function.comp_apply, neg_neg, mul_neg, mul_one] using hcomp
  refine ⟨P, ?_, hP (h₀ : ℂ) (by simpa using hh₀), hP⟩
  simpa only [P, Function.comp_apply, Complex.ofReal_neg] using hQanchor




theorem leeYangBox_holomorphicPressure_rightHalfPlane
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
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | 0 < z.re} := by
  obtain ⟨g, hlimit, hg, hderiv⟩ :=
    leeYangBox_normalizedFieldLogDerivative_rightHalfPlane d hd hbeta
  obtain ⟨P, hPanchor, _hPanchorDeriv, hP⟩ :=
    rightHalfPlane_normalizedPrimitive g hg h₀ hh₀
      (isingBoxPressureLimit d hd beta h₀ : ℂ)
  refine ⟨P, g, hPanchor, hlimit, ?_, hg, ?_, hderiv⟩
  · intro z hz
    exact (hP z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hP z hz).deriv



theorem leeYangBox_holomorphicPressure_leftHalfPlane
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
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | z.re < 0} := by
  obtain ⟨g, hlimit, hg, hderiv⟩ :=
    leeYangBox_normalizedFieldLogDerivative_leftHalfPlane d hd hbeta
  obtain ⟨P, hPanchor, _hPanchorDeriv, hP⟩ :=
    leftHalfPlane_normalizedPrimitive g hg h₀ hh₀
      (isingBoxPressureLimit d hd beta h₀ : ℂ)
  refine ⟨P, g, hPanchor, hlimit, ?_, hg, ?_, hderiv⟩
  · intro z hz
    exact (hP z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hP z hz).deriv

end StatMech.FrontierA
