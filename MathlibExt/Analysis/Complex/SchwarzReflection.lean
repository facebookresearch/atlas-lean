/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

/-- The Schwarz reflected extension of `f`: equal to `f` on the closed upper
half-plane, and the conjugate reflection below the real axis. -/
private noncomputable def schwarzExt (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if 0 ≤ z.im then f z else star (f (star z))

private theorem star_im (z : ℂ) : (star z).im = -z.im := by
  rw [Complex.star_def]
  exact Complex.conj_im z

private theorem star_re (z : ℂ) : (star z).re = z.re := by
  rw [Complex.star_def]
  exact Complex.conj_re z

private theorem hre (x t : ℝ) : (↑x + ↑t * Complex.I).im = t := by
  simp

private theorem schwarzExt_of_nonneg (f : ℂ → ℂ) (z : ℂ) (h : 0 ≤ z.im) :
    schwarzExt f z = f z := by
  simp [schwarzExt, h]

private theorem schwarzExt_of_neg (f : ℂ → ℂ) (z : ℂ) (h : ¬ 0 ≤ z.im) :
    schwarzExt f z = star (f (star z)) := by
  simp [schwarzExt, h]

private theorem schwarzExt_conj_of_im_eq_zero (f : ℂ → ℂ)
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0) (z : ℂ) (hz : z.im = 0) :
    star (f z) = f z := by
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.mpr (h3 z hz)

private theorem star_eq_self_of_im_eq_zero (z : ℂ) (hz : z.im = 0) : star z = z := by
  apply Complex.ext
  · simp only [Complex.star_def]
    exact Complex.conj_re z
  · simp only [Complex.star_def, Complex.conj_im, hz, neg_zero]

private theorem schwarzExt_of_not_pos (f : ℂ → ℂ)
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0) (z : ℂ) (h : ¬ 0 < z.im) :
    schwarzExt f z = star (f (star z)) := by
  by_cases h' : 0 ≤ z.im
  · have hz : z.im = 0 := le_antisymm (le_of_not_gt h) h'
    rw [schwarzExt_of_nonneg f z h', star_eq_self_of_im_eq_zero z hz]
    exact (schwarzExt_conj_of_im_eq_zero f h3 z hz).symm
  · exact schwarzExt_of_neg f z h'

private theorem schwarzExt_symm (f : ℂ → ℂ)
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0) (z : ℂ) :
    schwarzExt f (star z) = star (schwarzExt f z) := by
  have him : (star z).im = -z.im := star_im z
  by_cases h : 0 ≤ z.im
  · by_cases h0 : z.im = 0
    · have hzz : star z = z := star_eq_self_of_im_eq_zero z h0
      rw [hzz, schwarzExt_of_nonneg f z h]
      exact (schwarzExt_conj_of_im_eq_zero f h3 z h0).symm
    · have hpos : 0 < z.im := lt_of_le_of_ne h (Ne.symm h0)
      have hneg : ¬ 0 ≤ (star z).im := by
        rw [him]
        exact not_le.mpr (neg_lt_zero.mpr hpos)
      rw [schwarzExt_of_neg f (star z) hneg, star_star, schwarzExt_of_nonneg f z h]
  · have hpos : 0 < (star z).im := by
      rw [him]
      exact neg_pos.mpr (lt_of_not_ge h)
    rw [schwarzExt_of_nonneg f (star z) (le_of_lt hpos), schwarzExt_of_neg f z h,
      star_star]

private theorem schwarzExt_continuousOn_upper (f : ℂ → ℂ)
    (hf2 : ContinuousOn f {z | 0 ≤ z.im}) :
    ContinuousOn (schwarzExt f) {z | 0 ≤ z.im} := by
  apply hf2.congr
  intro z hz
  exact schwarzExt_of_nonneg f z hz

private theorem continuous_schwarzExt (f : ℂ → ℂ)
    (hf2 : ContinuousOn f {z | 0 ≤ z.im})
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0) :
    Continuous (schwarzExt f) := by
  have hs : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_Ici.preimage Complex.continuous_im
  have ht : IsClosed {z : ℂ | z.im ≤ 0} := isClosed_Iic.preimage Complex.continuous_im
  have hsup : {z : ℂ | 0 ≤ z.im} ∪ {z : ℂ | z.im ≤ 0} = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact le_total 0 z.im
  have hupper : ContinuousOn (schwarzExt f) {z : ℂ | 0 ≤ z.im} :=
    schwarzExt_continuousOn_upper f hf2
  have hlower : ContinuousOn (schwarzExt f) {z : ℂ | z.im ≤ 0} := by
    have hmap : ∀ z ∈ {z : ℂ | z.im ≤ 0}, star z ∈ {z : ℂ | 0 ≤ z.im} := by
      intro z hz
      change 0 ≤ (star z).im
      rw [star_im]
      exact neg_nonneg.mpr hz
    have h1 : ContinuousOn (fun z => f (star z)) {z : ℂ | z.im ≤ 0} :=
      hf2.comp continuous_star.continuousOn (fun z hz => hmap z hz)
    have hcomp : ContinuousOn (fun z => star (f (star z))) {z : ℂ | z.im ≤ 0} :=
      continuous_star.comp_continuousOn h1
    apply hcomp.congr
    intro z hz
    exact schwarzExt_of_not_pos f h3 z (not_lt.mpr hz)
  have hcont : ContinuousOn (schwarzExt f) ({z : ℂ | 0 ≤ z.im} ∪ {z : ℂ | z.im ≤ 0}) :=
    ContinuousOn.union_of_isClosed hupper hlower hs ht
  rw [hsup] at hcont
  exact continuousOn_univ.mp hcont

private theorem rect_subset_upper (a b : ℂ) (ha : 0 ≤ a.im) (hb : 0 ≤ b.im) :
    Set.uIcc a.re b.re ×ℂ Set.uIcc a.im b.im ⊆ {z | 0 ≤ z.im} := by
  intro p hp
  rw [Complex.mem_reProdIm] at hp
  rcases Set.mem_uIcc.mp hp.2 with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact le_trans ha h1
  · exact le_trans hb h1

private theorem interior_subset_upper_open (a b : ℂ) (ha : 0 ≤ a.im) (hb : 0 ≤ b.im) :
    Set.Ioo (min a.re b.re) (max a.re b.re) ×ℂ Set.Ioo (min a.im b.im) (max a.im b.im) ⊆
      {z | 0 < z.im} := by
  intro p hp
  rw [Complex.mem_reProdIm] at hp
  have h1 : min a.im b.im < p.im := (Set.mem_Ioo.mp hp.2).1
  change 0 < p.im
  exact lt_of_le_of_lt (le_min ha hb) h1

private theorem boundary_upper (f : ℂ → ℂ)
    (hf1 : DifferentiableOn ℂ f {z | 0 < z.im})
    (hf2 : ContinuousOn f {z | 0 ≤ z.im})
    (a b : ℂ) (ha : 0 ≤ a.im) (hb : 0 ≤ b.im) :
    (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑a.im * Complex.I)) -
      (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑b.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in a.im..b.im, schwarzExt f (↑b.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in a.im..b.im, schwarzExt f (↑a.re + ↑y * Complex.I)) = 0 := by
  have hhor : ∀ t c d : ℝ, 0 ≤ t →
      (∫ x : ℝ in c..d, schwarzExt f (↑x + ↑t * Complex.I)) =
      (∫ x : ℝ in c..d, f (↑x + ↑t * Complex.I)) := by
    intro t c d ht
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y _
    apply schwarzExt_of_nonneg
    rw [hre]
    exact ht
  have hvert : ∀ s c d : ℝ, 0 ≤ c → 0 ≤ d →
      (∫ y : ℝ in c..d, schwarzExt f (↑s + ↑y * Complex.I)) =
      (∫ y : ℝ in c..d, f (↑s + ↑y * Complex.I)) := by
    intro s c d hc hd
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y hy
    have hy0 : 0 ≤ y := by
      rcases Set.mem_uIoc.mp hy with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact le_trans hc (le_of_lt h1)
      · exact le_trans hd (le_of_lt h1)
    apply schwarzExt_of_nonneg
    rw [hre]
    exact hy0
  rw [hhor a.im a.re b.re ha, hhor b.im a.re b.re hb,
    hvert b.re a.im b.im ha hb, hvert a.re a.im b.im ha hb]
  exact Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f a b
    (hf2.mono (rect_subset_upper a b ha hb))
    (hf1.mono (interior_subset_upper_open a b ha hb))

private theorem star_add_im_point (x t : ℝ) :
    star (↑x + ↑t * Complex.I) = ↑x + ↑(-t) * Complex.I := by
  rw [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg]
  ring

private theorem boundary_lower (f : ℂ → ℂ)
    (hf1 : DifferentiableOn ℂ f {z | 0 < z.im})
    (hf2 : ContinuousOn f {z | 0 ≤ z.im})
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0)
    (a b : ℂ) (ha : a.im ≤ 0) (hb : b.im ≤ 0) :
    (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑a.im * Complex.I)) -
      (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑b.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in a.im..b.im, schwarzExt f (↑b.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in a.im..b.im, schwarzExt f (↑a.re + ↑y * Complex.I)) = 0 := by
  have hpt : ∀ x t : ℝ, t ≤ 0 →
      schwarzExt f (↑x + ↑t * Complex.I) = star (f (↑x + ↑(-t) * Complex.I)) := by
    intro x t ht
    have hneg : ¬ 0 < (↑x + ↑t * Complex.I).im := by
      rw [hre x t]
      exact not_lt.mpr ht
    rw [schwarzExt_of_not_pos f h3 _ hneg, star_add_im_point]
  have hhor : ∀ t : ℝ, t ≤ 0 →
      (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑t * Complex.I)) =
      ((starRingEnd ℂ) (∫ x : ℝ in a.re..b.re, f (↑x + ↑(-t) * Complex.I))) := by
    intro t ht
    have e : (fun x : ℝ => schwarzExt f (↑x + ↑t * Complex.I)) =
        (fun (x : ℝ) => (starRingEnd ℂ) (f (↑x + ↑(-t) * Complex.I))) := by
      apply funext
      intro x
      rw [hpt x t ht, Complex.star_def]
    rw [e, intervalIntegral.intervalIntegral_conj]
  have hvert : ∀ s c d : ℝ, c ≤ 0 → d ≤ 0 →
      (∫ y : ℝ in c..d, schwarzExt f (↑s + ↑y * Complex.I)) =
      ((starRingEnd ℂ) (∫ y : ℝ in -d..-c, f (↑s + ↑y * Complex.I))) := by
    intro s c d hc hd
    have e1 : (∫ y : ℝ in c..d, schwarzExt f (↑s + ↑y * Complex.I)) =
        (∫ y : ℝ in c..d, (starRingEnd ℂ) (f (↑s + ↑(-y) * Complex.I))) := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y hy
      have hy0 : y ≤ 0 := by
        rcases Set.mem_uIoc.mp hy with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact le_trans h2 hd
        · exact le_trans h2 hc
      rw [hpt s y hy0, Complex.star_def]
    rw [e1, intervalIntegral.intervalIntegral_conj]
    congr 1
    exact intervalIntegral.integral_comp_neg (fun u => f (↑s + ↑u * Complex.I))
  have T1eq : (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑a.im * Complex.I)) =
      ((starRingEnd ℂ) (∫ x : ℝ in (star a).re..(star b).re,
        f (↑x + ↑(star a).im * Complex.I))) := by
    rw [star_re a, star_re b, star_im a]
    exact hhor a.im ha
  have T2eq : (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑b.im * Complex.I)) =
      ((starRingEnd ℂ) (∫ x : ℝ in (star a).re..(star b).re,
        f (↑x + ↑(star b).im * Complex.I))) := by
    rw [star_re a, star_re b, star_im b]
    exact hhor b.im hb
  have T3eq : (∫ y : ℝ in a.im..b.im, schwarzExt f (↑b.re + ↑y * Complex.I)) =
      -((starRingEnd ℂ) (∫ y : ℝ in (star a).im..(star b).im,
        f (↑(star b).re + ↑y * Complex.I))) := by
    rw [star_im a, star_im b, star_re b]
    have e2 := hvert b.re a.im b.im ha hb
    have esym : (∫ y : ℝ in -a.im..-b.im, f (↑b.re + ↑y * Complex.I)) =
        -(∫ y : ℝ in -b.im..-a.im, f (↑b.re + ↑y * Complex.I)) :=
      intervalIntegral.integral_symm _ _
    rw [e2, esym, map_neg, neg_neg]
  have T4eq : (∫ y : ℝ in a.im..b.im, schwarzExt f (↑a.re + ↑y * Complex.I)) =
      -((starRingEnd ℂ) (∫ y : ℝ in (star a).im..(star b).im,
        f (↑(star a).re + ↑y * Complex.I))) := by
    rw [star_im a, star_im b, star_re a]
    have e2 := hvert a.re a.im b.im ha hb
    have esym : (∫ y : ℝ in -a.im..-b.im, f (↑a.re + ↑y * Complex.I)) =
        -(∫ y : ℝ in -b.im..-a.im, f (↑a.re + ↑y * Complex.I)) :=
      intervalIntegral.integral_symm _ _
    rw [e2, esym, map_neg, neg_neg]
  have star_smul_I : ∀ S : ℂ, (starRingEnd ℂ) (Complex.I • S) =
      Complex.I • (-(starRingEnd ℂ) S) := by
    intro S
    rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_I, neg_mul, mul_neg]
  have key : (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑a.im * Complex.I)) -
      (∫ x : ℝ in a.re..b.re, schwarzExt f (↑x + ↑b.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in a.im..b.im, schwarzExt f (↑b.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in a.im..b.im, schwarzExt f (↑a.re + ↑y * Complex.I)) =
      ((starRingEnd ℂ) ((∫ x : ℝ in (star a).re..(star b).re,
        f (↑x + ↑(star a).im * Complex.I)) -
      (∫ x : ℝ in (star a).re..(star b).re, f (↑x + ↑(star b).im * Complex.I)) +
      Complex.I • (∫ y : ℝ in (star a).im..(star b).im,
        f (↑(star b).re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (star a).im..(star b).im,
        f (↑(star a).re + ↑y * Complex.I)))) := by
    rw [T1eq, T2eq, T3eq, T4eq, map_sub, map_add, map_sub, star_smul_I, star_smul_I]
  have ha' : 0 ≤ (star a).im := by
    rw [star_im]
    exact neg_nonneg.mpr ha
  have hb' : 0 ≤ (star b).im := by
    rw [star_im]
    exact neg_nonneg.mpr hb
  have hf0 := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    f (star a) (star b) (hf2.mono (rect_subset_upper _ _ ha' hb'))
    (hf1.mono (interior_subset_upper_open _ _ ha' hb'))
  rw [key, hf0, map_zero]

private theorem boundary_swap (g : ℂ → ℂ) (z w : ℂ) :
    (∫ x : ℝ in w.re..z.re, g (↑x + ↑w.im * Complex.I)) -
      (∫ x : ℝ in w.re..z.re, g (↑x + ↑z.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in w.im..z.im, g (↑z.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in w.im..z.im, g (↑w.re + ↑y * Complex.I)) =
    (∫ x : ℝ in z.re..w.re, g (↑x + ↑z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, g (↑x + ↑w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, g (↑w.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, g (↑z.re + ↑y * Complex.I)) := by
  have e1 : (∫ x : ℝ in w.re..z.re, g (↑x + ↑w.im * Complex.I)) =
      -(∫ x : ℝ in z.re..w.re, g (↑x + ↑w.im * Complex.I)) :=
    intervalIntegral.integral_symm _ _
  have e2 : (∫ x : ℝ in w.re..z.re, g (↑x + ↑z.im * Complex.I)) =
      -(∫ x : ℝ in z.re..w.re, g (↑x + ↑z.im * Complex.I)) :=
    intervalIntegral.integral_symm _ _
  have e3 : (∫ y : ℝ in w.im..z.im, g (↑z.re + ↑y * Complex.I)) =
      -(∫ y : ℝ in z.im..w.im, g (↑z.re + ↑y * Complex.I)) :=
    intervalIntegral.integral_symm _ _
  have e4 : (∫ y : ℝ in w.im..z.im, g (↑w.re + ↑y * Complex.I)) =
      -(∫ y : ℝ in z.im..w.im, g (↑w.re + ↑y * Complex.I)) :=
    intervalIntegral.integral_symm _ _
  rw [e1, e2, e3, e4, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

private theorem boundary_straddle (f : ℂ → ℂ)
    (hf1 : DifferentiableOn ℂ f {z | 0 < z.im})
    (hf2 : ContinuousOn f {z | 0 ≤ z.im})
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0)
    (z w : ℂ) (hz : z.im ≤ 0) (hw : 0 ≤ w.im) :
    (∫ x : ℝ in z.re..w.re, schwarzExt f (↑x + ↑z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, schwarzExt f (↑x + ↑w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, schwarzExt f (↑w.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, schwarzExt f (↑z.re + ↑y * Complex.I)) = 0 := by
  have hg := continuous_schwarzExt f hf2 h3
  have hU := boundary_upper f hf1 hf2 ⟨z.re, 0⟩ ⟨w.re, w.im⟩ (le_refl 0) hw
  have hL := boundary_lower f hf1 hf2 h3 ⟨z.re, z.im⟩ ⟨w.re, 0⟩ hz (le_refl 0)
  have eU : (∫ x : ℝ in z.re..w.re, schwarzExt f (↑x + ↑(0:ℝ) * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, schwarzExt f (↑x + ↑w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in (0:ℝ)..w.im, schwarzExt f (↑w.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in (0:ℝ)..w.im, schwarzExt f (↑z.re + ↑y * Complex.I)) = 0 := hU
  have eL : (∫ x : ℝ in z.re..w.re, schwarzExt f (↑x + ↑z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, schwarzExt f (↑x + ↑(0:ℝ) * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..(0:ℝ), schwarzExt f (↑w.re + ↑y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..(0:ℝ), schwarzExt f (↑z.re + ↑y * Complex.I)) = 0 := hL
  have hcont1 : Continuous (fun y : ℝ => schwarzExt f (↑w.re + ↑y * Complex.I)) :=
    hg.comp (by fun_prop)
  have hcont2 : Continuous (fun y : ℝ => schwarzExt f (↑z.re + ↑y * Complex.I)) :=
    hg.comp (by fun_prop)
  have hsplit1 : (∫ y : ℝ in z.im..w.im, schwarzExt f (↑w.re + ↑y * Complex.I)) =
      (∫ y : ℝ in z.im..0, schwarzExt f (↑w.re + ↑y * Complex.I)) +
      (∫ y : ℝ in (0:ℝ)..w.im, schwarzExt f (↑w.re + ↑y * Complex.I)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont1.intervalIntegrable _ _)
      (hcont1.intervalIntegrable _ _)).symm
  have hsplit2 : (∫ y : ℝ in z.im..w.im, schwarzExt f (↑z.re + ↑y * Complex.I)) =
      (∫ y : ℝ in z.im..0, schwarzExt f (↑z.re + ↑y * Complex.I)) +
      (∫ y : ℝ in (0:ℝ)..w.im, schwarzExt f (↑z.re + ↑y * Complex.I)) :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont2.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)).symm
  rw [hsplit1, hsplit2]
  simp only [smul_eq_mul] at eU eL ⊢
  linear_combination eU + eL

private theorem boundary_all (f : ℂ → ℂ)
    (hf1 : DifferentiableOn ℂ f {z | 0 < z.im})
    (hf2 : ContinuousOn f {z | 0 ≤ z.im})
    (h3 : ∀ z : ℂ, z.im = 0 → (f z).im = 0) :
    Complex.IsConservativeOn (schwarzExt f) Set.univ := by
  intro z w _
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hz : 0 ≤ z.im <;> by_cases hw : 0 ≤ w.im
  · exact boundary_upper f hf1 hf2 z w hz hw
  · have hw' : w.im ≤ 0 := le_of_not_ge hw
    have h := boundary_straddle f hf1 hf2 h3 w z hw' hz
    have hsw := boundary_swap (schwarzExt f) z w
    rw [← hsw]
    exact h
  · have hz' : z.im ≤ 0 := le_of_not_ge hz
    exact boundary_straddle f hf1 hf2 h3 z w hz' hw
  · have hz' : z.im ≤ 0 := le_of_not_ge hz
    have hw' : w.im ≤ 0 := le_of_not_ge hw
    exact boundary_lower f hf1 hf2 h3 z w hz' hw'

/-- **Schwarz reflection principle.** Let $f : \mathbb{C} \to \mathbb{C}$ be holomorphic on the
open upper half-plane $\{z : \operatorname{Im} z > 0\}$, continuous on the closed upper half-plane
$\{z : \operatorname{Im} z \ge 0\}$, and real-valued on the real axis. Then there is an entire
function $g$ that agrees with $f$ on the closed upper half-plane and satisfies
$g(\bar z) = \overline{g(z)}$ for every $z \in \mathbb{C}$.

Source: https://en.wikipedia.org/wiki/Schwarz_reflection_principle, statement `schwarz-refl-s1`.

Proves `Wanted` entry `schwarz_reflection`.
-/
theorem schwarz_reflection :
  ∀ (f : ℂ → ℂ),
    DifferentiableOn ℂ f {z | 0 < z.im} →
      ContinuousOn f {z | 0 ≤ z.im} →
        (∀ z : ℂ, z.im = 0 → (f z).im = 0) →
          ∃ g : ℂ → ℂ,
            DifferentiableOn ℂ g Set.univ ∧
              (∀ z : ℂ, 0 ≤ z.im → g z = f z) ∧
                ∀ z : ℂ, g (star z) = star (g z) := by
  intro f hf1 hf2 h3
  refine ⟨schwarzExt f, ?_, ?_, ?_⟩
  · rw [← Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ]
    exact ⟨boundary_all f hf1 hf2 h3, (continuous_schwarzExt f hf2 h3).continuousOn⟩
  · intro z hz
    exact schwarzExt_of_nonneg f z hz
  · intro z
    exact schwarzExt_symm f h3 z

end

end MetaMathlibExt
