/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.LeeYangPressurePrimitive
import Code.FrontierB.FreeBoxSpinLimit
import Code.Sharpness.FieldGhostDict

open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict




noncomputable def leeYangBoxSpinProduct
    (d : ℕ) (beta : ℝ) (A : Finset (Site d)) (n : ℕ) (h : ℂ) : ℂ :=
  leeYangComplexFieldExpectation (boxGraph d n) beta
    (fun s => (spinProd (boxSpinSupport d n A) s : ℂ)) h

theorem leeYangBoxSpinProduct_ofReal
    (d n : ℕ) (beta h : ℝ) (A : Finset (Site d)) :
    leeYangBoxSpinProduct d beta A n (h : ℂ) =
      (isingExpectation (boxGraph d n) beta h
        (spinProd (boxSpinSupport d n A)) : ℂ) := by
  exact leeYangComplexFieldExpectation_ofReal _ beta h _

theorem leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane
    (d n : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    AnalyticOnNhd ℂ (leeYangBoxSpinProduct d beta A n)
      {h : ℂ | 0 < h.re} :=
  leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane
    (boxGraph d n) hbeta _

theorem leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane
    (d n : ℕ) {beta : ℝ} (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    AnalyticOnNhd ℂ (leeYangBoxSpinProduct d beta A n)
      {h : ℂ | h.re < 0} :=
  leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane
    (boxGraph d n) hbeta _



theorem leeYangBoxSpinProduct_tendsto_of_nonneg_real_field
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (A : Finset (Site d)) :
    Tendsto (fun n => leeYangBoxSpinProduct d beta A n (h : ℂ)) atTop
      (nhds (Complex.ofReal (∫ omega, spinProd A omega
        ∂(freeState d beta h : Measure (ConfigSpace (Site d)))))) := by
  have hr := integral_freeMeasure_spinProd_tendsto_freeState_of_nonneg_field
    d beta h hbeta hh A
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  refine hc.congr' ?_
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  filter_upwards [eventually_ge_atTop N] with n hn
  change Complex.ofReal (∫ omega, spinProd A omega
      ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d)))) = _
  rw [leeYangBoxSpinProduct_ofReal]
  exact congrArg Complex.ofReal (integral_freeMeasure_spinProd d n beta h A
    (hAN.trans (box_mono d hn)))


theorem isingExpectation_spinProd_neg_field
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta h : ℝ) (A : Finset V) :
    isingExpectation G beta (-h) (spinProd A) =
      (-1 : ℝ) ^ A.card * isingExpectation G beta h (spinProd A) := by
  unfold isingExpectation
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold isingProb
  rw [spinProd_flipV, isingWeight_flip, fgd_isingZ_neg]
  ring

theorem boxSpinSupport_card_eq
    (d n : ℕ) (A : Finset (Site d)) (hA : ↑A ⊆ box d n) :
    (boxSpinSupport d n A).card = A.card := by
  have hsupp : (boxSpinSupport d n A).image Subtype.val = A := by
    ext x
    constructor
    · rintro hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [boxSpinSupport] using hy
    · intro hx
      rw [Finset.mem_image]
      exact ⟨⟨x, hA hx⟩, by simp [boxSpinSupport, hx], rfl⟩
  calc
    (boxSpinSupport d n A).card =
        ((boxSpinSupport d n A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card hsupp



theorem leeYangBoxSpinProduct_tendsto_of_neg_real_field
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : h < 0)
    (A : Finset (Site d)) :
    Tendsto (fun n => leeYangBoxSpinProduct d beta A n (h : ℂ)) atTop
      (nhds ((((-1 : ℝ) : ℂ) ^ A.card) *
        Complex.ofReal (∫ omega, spinProd A omega
          ∂(freeState d beta (-h) : Measure (ConfigSpace (Site d)))))) := by
  have hp := leeYangBoxSpinProduct_tendsto_of_nonneg_real_field
    d beta (-h) hbeta (neg_nonneg.mpr hh.le) A
  have hmul := (tendsto_const_nhds (x := ((-1 : ℝ) ^ A.card : ℂ))).mul hp
  refine hmul.congr' ?_
  obtain ⟨N, hAN⟩ := finite_subset_box (↑A : Set (Site d)) A.finite_toSet
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [leeYangBoxSpinProduct_ofReal, leeYangBoxSpinProduct_ofReal]
  have hcard := boxSpinSupport_card_eq d n A
    (hAN.trans (box_mono d hn))
  have hs := isingExpectation_spinProd_neg_field (boxGraph d n) beta (-h)
    (boxSpinSupport d n A)
  rw [neg_neg, hcard] at hs
  exact_mod_cast hs.symm



noncomputable def leeYangSpinProductRightEnvelope
    (beta : ℝ) (A : Finset (Site d)) (h : ℂ) : ℝ :=
  let r := ‖Complex.exp (-2 * (beta : ℂ) * h)‖
  ((1 + r) / (1 - r)) ^ A.card


noncomputable def leeYangSpinProductLeftEnvelope
    (beta : ℝ) (A : Finset (Site d)) (h : ℂ) : ℝ :=
  let r := ‖Complex.exp (2 * (beta : ℂ) * h)‖
  ((1 + r) / (1 - r)) ^ A.card

theorem continuousOn_leeYangSpinProductRightEnvelope
    {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    ContinuousOn (leeYangSpinProductRightEnvelope beta A)
      {h : ℂ | 0 < h.re} := by
  have hr : Continuous
      (fun h : ℂ => ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
    fun_prop
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · exact continuousOn_const.add hr.continuousOn
  · exact continuousOn_const.sub hr.continuousOn
  · intro h hh
    change 0 < h.re at hh
    have hnorm : ‖Complex.exp (-2 * (beta : ℂ) * h)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      norm_num [Complex.mul_re]
      nlinarith
    simpa only [sub_ne_zero] using ne_of_gt hnorm

theorem continuousOn_leeYangSpinProductLeftEnvelope
    {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    ContinuousOn (leeYangSpinProductLeftEnvelope beta A)
      {h : ℂ | h.re < 0} := by
  have hr : Continuous
      (fun h : ℂ => ‖Complex.exp (2 * (beta : ℂ) * h)‖) := by
    fun_prop
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · exact continuousOn_const.add hr.continuousOn
  · exact continuousOn_const.sub hr.continuousOn
  · intro h hh
    change h.re < 0 at hh
    have hnorm : ‖Complex.exp (2 * (beta : ℂ) * h)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      norm_num [Complex.mul_re]
      nlinarith
    simpa only [sub_ne_zero] using ne_of_gt hnorm



def LeeYangSpinProductRightBound
    (d : ℕ) (beta : ℝ) (A : Finset (Site d)) : Prop :=
  ∀ n h, 0 < h.re →
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
      leeYangSpinProductRightEnvelope beta A h


def LeeYangSpinProductLeftBound
    (d : ℕ) (beta : ℝ) (A : Finset (Site d)) : Prop :=
  ∀ n h, h.re < 0 →
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
      leeYangSpinProductLeftEnvelope beta A h



theorem leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d))
    (hpoint : LeeYangSpinProductRightBound d beta A)
    {K : Set ℂ} (hK : IsCompact K) (hKright : K ⊆ {h : ℂ | 0 < h.re}) :
    ∃ C : ℝ, ∀ n h, h ∈ K → ‖leeYangBoxSpinProduct d beta A n h‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_leeYangSpinProductRightEnvelope hbeta A).mono hKright)
  refine ⟨C, fun n h hh => ?_⟩
  calc
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
        leeYangSpinProductRightEnvelope beta A h := hpoint n h (hKright hh)
    _ ≤ ‖leeYangSpinProductRightEnvelope beta A h‖ := Real.le_norm_self _
    _ ≤ C := hC h hh

theorem leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d))
    (hpoint : LeeYangSpinProductLeftBound d beta A)
    {K : Set ℂ} (hK : IsCompact K) (hKleft : K ⊆ {h : ℂ | h.re < 0}) :
    ∃ C : ℝ, ∀ n h, h ∈ K → ‖leeYangBoxSpinProduct d beta A n h‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_leeYangSpinProductLeftEnvelope hbeta A).mono hKleft)
  refine ⟨C, fun n h hh => ?_⟩
  calc
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
        leeYangSpinProductLeftEnvelope beta A h := hpoint n h (hKleft hh)
    _ ≤ ‖leeYangSpinProductLeftEnvelope beta A h‖ := Real.le_norm_self _
    _ ≤ C := hC h hh




theorem leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d))
    (hpoint : LeeYangSpinProductRightBound d beta A) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | 0 < z.re} := by
  let F := leeYangBoxSpinProduct d beta A
  let U : Set ℂ := {z | 0 < z.re}
  let anchor : Set ℂ := {z | z.im = 0 ∧ 0 < z.re}
  let anchorLimit : ℂ → ℂ := fun z => Complex.ofReal
    (∫ omega, spinProd A omega
      ∂(freeState d beta z.re : Measure (ConfigSpace (Site d))))
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U := fun n =>
    (leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane
      d n hbeta.le A).differentiableOn
  have hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C := by
    intro K hK hKU
    exact leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane
      d hbeta A hpoint hK hKU
  have hcompact : IsLocallyUniformlySequentiallyPrecompact F U :=
    holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F U hUopen hholomorphic hbounded rightHalfPlaneCompactExhaustion
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simpa using hz.1.symm
    simpa only [F, anchorLimit, hzreal] using
      leeYangBoxSpinProduct_tendsto_of_nonneg_real_field
        d beta z.re hbeta.le hz.2.le A
  have haccum : ∃ᶠ z in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), z ∈ anchor :=
    (leeYangRightRealAnchor_frequently_near d hd beta 1 zero_lt_one).mono
      fun z hz => ⟨hz.1, hz.2.1⟩
  simpa only [F, U] using
    montelVitali_of_locallyUniform_precompact F U anchor (1 : ℂ) anchorLimit
      hUopen (convex_halfSpace_re_gt 0).isPreconnected
      (by change 0 < (1 : ℂ).re; norm_num)
      (fun _ hz => hz.2) haccum hholomorphic hcompact hanchorLimit


theorem leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d))
    (hpoint : LeeYangSpinProductLeftBound d beta A) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | z.re < 0} := by
  let F := leeYangBoxSpinProduct d beta A
  let U : Set ℂ := {z | z.re < 0}
  let anchor : Set ℂ := {z | z.im = 0 ∧ z.re < 0}
  let anchorLimit : ℂ → ℂ := fun z => (((-1 : ℝ) : ℂ) ^ A.card) *
    Complex.ofReal (∫ omega, spinProd A omega
      ∂(freeState d beta (-z.re) : Measure (ConfigSpace (Site d))))
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U := fun n =>
    (leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane
      d n hbeta.le A).differentiableOn
  have hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C := by
    intro K hK hKU
    exact leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane
      d hbeta A hpoint hK hKU
  have hcompact : IsLocallyUniformlySequentiallyPrecompact F U :=
    holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F U hUopen hholomorphic hbounded leftHalfPlaneCompactExhaustion
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simpa using hz.1.symm
    simpa only [F, anchorLimit, hzreal] using
      leeYangBoxSpinProduct_tendsto_of_neg_real_field
        d beta z.re hbeta.le hz.2 A
  have hfreq := leeYangLeftRealAnchor_frequently_near
    d hd beta (-1 : ℝ) (by norm_num)
  have haccum : ∃ᶠ z in nhdsWithin ((-1 : ℝ) : ℂ) ({((-1 : ℝ) : ℂ)}ᶜ),
      z ∈ anchor := hfreq.mono fun z hz =>
    (show z.im = 0 ∧ z.re < 0 from ⟨hz.1, hz.2.1⟩)
  simpa only [F, U] using
    montelVitali_of_locallyUniform_precompact F U anchor ((-1 : ℝ) : ℂ) anchorLimit
      hUopen (convex_halfSpace_re_lt 0).isPreconnected
      (by change (((-1 : ℝ) : ℂ)).re < 0; norm_num)
      (fun _ hz => hz.2) haccum hholomorphic hcompact hanchorLimit





theorem multiAffine_sign_update_norm_le
    {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (hpAff : IsMultiAffine p)
    (hpStable : PolydiscStable p) (z : I → ℂ)
    (hz : ∀ j, ‖z j‖ < 1) (i : I) :
    ‖p (Function.update z i (-z i))‖ ≤
      ((1 + ‖z i‖) / (1 - ‖z i‖)) * ‖p z‖ := by
  let a := p (Function.update z i 0)
  let b := p (Function.update z i 1) - p (Function.update z i 0)
  have hp (t : ℂ) : p (Function.update z i t) = a + t * b := by
    simpa only [a, b] using hpAff i z t
  have hpz : p z = a + z i * b := by
    have hu : Function.update z i (z i) = z := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    calc
      p z = p (Function.update z i (z i)) := congrArg p hu.symm
      _ = a + z i * b := hp _
  have hpneg : p (Function.update z i (-z i)) = a + (-z i) * b := hp _
  have hba : ‖b‖ ≤ ‖a‖ := by
    by_contra hnot
    have hab : ‖a‖ < ‖b‖ := lt_of_not_ge hnot
    have hb0 : b ≠ 0 := by
      intro hb
      rw [hb, norm_zero] at hab
      exact (not_lt_of_ge (norm_nonneg a)) hab
    let t : ℂ := -a / b
    have ht : ‖t‖ < 1 := by
      simp only [t, norm_div, norm_neg]
      exact (div_lt_one (norm_pos_iff.mpr hb0)).2 hab
    have hzu : ∀ j, ‖Function.update z i t j‖ < 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using ht
      · simpa [hji] using hz j
    apply hpStable (Function.update z i t) hzu
    rw [hp]
    dsimp only [t]
    field_simp [hb0]
    ring
  have hnum : ‖p (Function.update z i (-z i))‖ ≤
      ‖a‖ + ‖z i‖ * ‖b‖ := by
    rw [hpneg]
    calc
      ‖a + -z i * b‖ ≤ ‖a‖ + ‖-z i * b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖z i‖ * ‖b‖ := by rw [norm_mul, norm_neg]
  have hden : ‖a‖ - ‖z i‖ * ‖b‖ ≤ ‖p z‖ := by
    rw [hpz]
    calc
      ‖a‖ - ‖z i‖ * ‖b‖ = ‖a‖ - ‖-(z i * b)‖ := by
        rw [norm_neg, norm_mul]
      _ ≤ ‖a - -(z i * b)‖ := norm_sub_norm_le a (-(z i * b))
      _ = ‖a + z i * b‖ := by ring_nf
  have hzi0 : 0 ≤ ‖z i‖ := norm_nonneg _
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hden0 : 0 ≤ ‖p z‖ := norm_nonneg _
  have hcross :
      ‖p (Function.update z i (-z i))‖ * (1 - ‖z i‖) ≤
        (1 + ‖z i‖) * ‖p z‖ := by
    nlinarith [hz i]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sub_pos.mpr (hz i))).2 hcross


def leeYangSignedDiagonal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (q : ℂ) : LeeYangVar G → ℂ
  | Sum.inl v => if v ∈ A then -q else q
  | Sum.inr _ => 0

theorem leeYangMonomial_anchorSupport_flip
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ConfigSpace V) (z : LeeYangVar G → ℂ) :
    leeYangMonomial (leeYangAnchorSupport G (leeYangFlip s)) z =
      ∏ v : V, if s v = false then z (leeYangAnchor G v) else 1 := by
  unfold leeYangMonomial leeYangAnchorSupport leeYangFlip leeYangAnchor
  rw [Finset.prod_filter]
  simp [Fintype.prod_sum_type]

theorem leeYangSignedProduct_eq_spinProd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ConfigSpace V) (A : Finset V) (q : ℂ) :
    (∏ v : V, if s v = false then
        leeYangSignedDiagonal G A q (leeYangAnchor G v) else 1) =
      (spinProd A s : ℂ) * q ^ minusSpinCount s := by
  rw [show (spinProd A s : ℂ) =
      ∏ v : V, if v ∈ A then (spin s v : ℂ) else 1 by
    calc
      (spinProd A s : ℂ) = ∏ v ∈ A, (spin s v : ℂ) := by
        unfold spinProd
        push_cast
        rfl
      _ = ∏ v : V, if v ∈ A then (spin s v : ℂ) else 1 := by simp]
  rw [show q ^ minusSpinCount s =
      ∏ v : V, if s v = false then q else 1 by
    simp [minusSpinCount, Finset.prod_ite, Finset.prod_const]]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  simp only [leeYangSignedDiagonal, leeYangAnchor]
  by_cases hA : v ∈ A <;> cases hs : s v <;> simp [hA, hs, spin]

theorem leeYangSignedDiagonal_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℂ) :
    leeYangSignedDiagonal G ∅ q = leeYangDiagonal G q := by
  funext k
  rcases k with v | he <;> simp [leeYangSignedDiagonal, leeYangDiagonal]

theorem leeYangSignedDiagonal_insert
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) (hv : v ∉ A) (q : ℂ) :
    leeYangSignedDiagonal G (insert v A) q =
      Function.update (leeYangSignedDiagonal G A q)
        (leeYangAnchor G v) (-q) := by
  funext k
  rcases k with w | he
  · by_cases hwv : w = v
    · subst w
      simp [leeYangSignedDiagonal, leeYangAnchor, hv]
    · simp [leeYangSignedDiagonal, leeYangAnchor, hwv]
  · simp [leeYangSignedDiagonal, leeYangAnchor]

theorem leeYangSignedDiagonal_norm_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {q : ℂ} (hq : ‖q‖ < 1) :
    ∀ k, ‖leeYangSignedDiagonal G A q k‖ < 1 := by
  intro k
  rcases k with v | he
  · by_cases hv : v ∈ A <;> simp [leeYangSignedDiagonal, hv, hq]
  · simp [leeYangSignedDiagonal]


theorem leeYangContracted_signed_norm_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {beta : ℝ} (hbeta : 0 ≤ beta) {q : ℂ} (hq : ‖q‖ < 1)
    (A : Finset V) :
    ‖leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)‖ ≤
      ((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card *
        ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖ := by
  induction A using Finset.induction with
  | empty =>
      rw [leeYangSignedDiagonal_empty]
      simp
  | @insert v A hv ih =>
      rw [leeYangSignedDiagonal_insert G A v hv q]
      let z := leeYangSignedDiagonal G A q
      have hz : ∀ k, ‖z k‖ < 1 := leeYangSignedDiagonal_norm_lt G A hq
      have hzi : z (leeYangAnchor G v) = q := by
        simp [z, leeYangSignedDiagonal, leeYangAnchor, hv]
      have hone := multiAffine_sign_update_norm_le
        (leeYangContractedProduct G beta)
        (leeYangContractedProduct_multiAffine G beta)
        (leeYangContractedProduct_stable G hbeta) z hz (leeYangAnchor G v)
      rw [hzi] at hone
      calc
        ‖leeYangContractedProduct G beta
            (Function.update z (leeYangAnchor G v) (-q))‖ ≤
            ((1 + ‖q‖) / (1 - ‖q‖)) *
              ‖leeYangContractedProduct G beta z‖ := hone
        _ ≤ ((1 + ‖q‖) / (1 - ‖q‖)) *
              (((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card *
                ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖) := by
              apply mul_le_mul_of_nonneg_left ih
              positivity
        _ = ((1 + ‖q‖) / (1 - ‖q‖)) ^ (insert v A).card *
              ‖leeYangContractedProduct G beta (leeYangDiagonal G q)‖ := by
              rw [Finset.card_insert_of_notMem hv, pow_succ]
              ring

theorem leeYangContracted_signed_eq_spin_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (A : Finset V) (q : ℂ) :
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
        leeYangContractedProduct G beta (leeYangSignedDiagonal G A q) =
      ∑ s : ConfigSpace V, (spinProd A s : ℂ) *
        (zeroFieldInteractionWeight G beta s : ℂ) * q ^ minusSpinCount s := by
  rw [leeYangContractedProduct_eq_sum_sigma, Finset.mul_sum]
  let F : ConfigSpace V → ℂ := fun sigma ↦
    (Real.exp (beta * G.edgeFinset.card) : ℂ) *
      (leeYangChoiceWeight G beta (sigma, leeYangTauOf G sigma) *
        leeYangMonomial (leeYangAnchorSupport G sigma)
          (leeYangSignedDiagonal G A q))
  change (∑ sigma : ConfigSpace V, F sigma) = _
  rw [show (∑ sigma : ConfigSpace V, F sigma) =
      ∑ s : ConfigSpace V, F (leeYangFlipEquiv s) by
        simpa using (Equiv.sum_comp leeYangFlipEquiv F).symm]
  apply Finset.sum_congr rfl
  intro s hs
  have hweight :
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
          leeYangChoiceWeight G beta
            (leeYangFlip s, leeYangTauOf G (leeYangFlip s)) =
        (zeroFieldInteractionWeight G beta s : ℂ) := by
    rw [leeYangChoiceWeight_eq_ofReal]
    rw [← Complex.ofReal_mul]
    rw [exp_card_mul_leeYangRealChoiceWeight]
    rw [zeroFieldInteractionWeight_flip]
  simp only [F, leeYangFlipEquiv_apply]
  rw [← mul_assoc, hweight, leeYangMonomial_anchorSupport_flip,
    leeYangSignedProduct_eq_spinProd]
  ring

theorem leeYangObservable_fugacity_eq_signed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (A : Finset V) (h : ℂ) :
    Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        leeYangComplexFieldObservableNumerator G beta
          (fun s ↦ (spinProd A s : ℂ)) h =
      (Real.exp (beta * G.edgeFinset.card) : ℂ) *
        leeYangContractedProduct G beta
          (leeYangSignedDiagonal G A
            (Complex.exp (-2 * (beta : ℂ) * h))) := by
  rw [leeYangContracted_signed_eq_spin_sum]
  unfold leeYangComplexFieldObservableNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Complex.exp_nat_mul]
  unfold zeroFieldInteractionWeight
  rw [Complex.ofReal_exp]
  rw [show Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        ((spinProd A s : ℂ) * Complex.exp
          ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
            (beta : ℂ) * h * (∑ v : V, spin s v))) =
      (spinProd A s : ℂ) *
        (Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
          Complex.exp
            ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
              (beta : ℂ) * h * (∑ v : V, spin s v))) by ring]
  rw [← Complex.exp_add]
  conv_rhs =>
    rw [mul_assoc, ← Complex.exp_add]
  rw [sum_spin_eq_card_sub_two_mul_minusSpinCount s]
  push_cast
  ring_nf

theorem leeYangComplexFieldExpectation_spinProd_eq_contractedRatio
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {beta : ℝ} (hbeta : 0 ≤ beta) (A : Finset V) {h : ℂ}
    (hh : h.re ≠ 0) :
    leeYangComplexFieldExpectation G beta (fun s ↦ (spinProd A s : ℂ)) h =
      leeYangContractedProduct G beta
          (leeYangSignedDiagonal G A
            (Complex.exp (-2 * (beta : ℂ) * h))) /
        leeYangContractedProduct G beta
          (leeYangDiagonal G (Complex.exp (-2 * (beta : ℂ) * h))) := by
  let q := Complex.exp (-2 * (beta : ℂ) * h)
  let c : ℂ := Real.exp (beta * G.edgeFinset.card)
  let e := Complex.exp (-(beta : ℂ) * h * Fintype.card V)
  let N := leeYangComplexFieldObservableNumerator G beta
    (fun s ↦ (spinProd A s : ℂ)) h
  let Z := leeYangComplexFieldPartition G beta h
  let P := leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)
  let Q := leeYangContractedProduct G beta (leeYangDiagonal G q)
  have hnum : e * N = c * P := by
    simpa only [e, N, c, P, q] using
      leeYangObservable_fugacity_eq_signed G beta A h
  have hden : e * Z = c * Q := by
    calc
      e * Z = (leeYangComplexPolynomial G beta).eval q := by
        symm
        simpa only [e, Z, q] using
          leeYangComplexFieldPartition_eq_fugacity G beta h
      _ = c * Q := by
        symm
        simpa only [c, Q, q] using leeYangContractedProduct_diagonal G beta q
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hZ : Z ≠ 0 :=
    leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh
  have hQ : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, mul_zero] at hden
    exact mul_ne_zero he hZ hden
  change N / Z = P / Q
  apply (div_eq_div_iff hZ hQ).2
  apply mul_left_cancel₀ he
  calc
    e * (N * Q) = (e * N) * Q := by ring
    _ = (c * P) * Q := by rw [hnum]
    _ = P * (c * Q) := by ring
    _ = P * (e * Z) := by rw [hden]
    _ = e * (P * Z) := by ring

theorem leeYangComplexFieldExpectation_spinProd_norm_le_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {beta : ℝ} (hbeta : 0 < beta) (A : Finset V) {h : ℂ}
    (hh : 0 < h.re) :
    ‖leeYangComplexFieldExpectation G beta
        (fun s ↦ (spinProd A s : ℂ)) h‖ ≤
      ((1 + ‖Complex.exp (-2 * (beta : ℂ) * h)‖) /
        (1 - ‖Complex.exp (-2 * (beta : ℂ) * h)‖)) ^ A.card := by
  let q := Complex.exp (-2 * (beta : ℂ) * h)
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    norm_num [q, Complex.mul_re]
    nlinarith
  have hratio := leeYangComplexFieldExpectation_spinProd_eq_contractedRatio
    G hbeta.le A (ne_of_gt hh)
  let P := leeYangContractedProduct G beta (leeYangSignedDiagonal G A q)
  let Q := leeYangContractedProduct G beta (leeYangDiagonal G q)
  have hbound : ‖P‖ ≤ ((1 + ‖q‖) / (1 - ‖q‖)) ^ A.card * ‖Q‖ :=
    leeYangContracted_signed_norm_le G hbeta.le hq A
  have hQ : Q ≠ 0 := by
    apply leeYangContractedProduct_stable G hbeta.le
    intro k
    rcases k with v | he
    · exact hq
    · simp [leeYangDiagonal]
  rw [hratio]
  change ‖P / Q‖ ≤ _
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hQ)).2
  simpa only [q] using hbound

theorem boxSpinSupport_card_le (d n : ℕ) (A : Finset (Site d)) :
    (boxSpinSupport d n A).card ≤ A.card := by
  have hsub : (boxSpinSupport d n A).image Subtype.val ⊆ A := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [boxSpinSupport] using hy
  calc
    (boxSpinSupport d n A).card =
        ((boxSpinSupport d n A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ A.card := Finset.card_le_card hsub


theorem leeYangSpinProductRightBound
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    LeeYangSpinProductRightBound d beta A := by
  intro n h hh
  let q := Complex.exp (-2 * (beta : ℂ) * h)
  let c : ℝ := (1 + ‖q‖) / (1 - ‖q‖)
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    norm_num [q, Complex.mul_re]
    nlinarith
  have hc : 1 ≤ c := by
    apply (le_div_iff₀ (sub_pos.mpr hq)).2
    dsimp only [c]
    nlinarith [norm_nonneg q]
  have hfinite := leeYangComplexFieldExpectation_spinProd_norm_le_right
    (boxGraph d n) hbeta (boxSpinSupport d n A) hh
  have hcard := boxSpinSupport_card_le d n A
  calc
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤ c ^ (boxSpinSupport d n A).card := by
      simpa only [leeYangBoxSpinProduct, q, c] using hfinite
    _ ≤ c ^ A.card := pow_le_pow_right₀ hc hcard
    _ = leeYangSpinProductRightEnvelope beta A h := by rfl

theorem leeYangComplexFieldPartition_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (h : ℂ) :
    leeYangComplexFieldPartition G beta (-h) =
      leeYangComplexFieldPartition G beta h := by
  unfold leeYangComplexFieldPartition
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  have hb : (∑ e ∈ G.edgeFinset, bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ ↦ bond_flipV s e)
  have hspin : (∑ x : V, spin (flipV s) x) = -∑ x : V, spin s x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ spin_flipV s x)
  rw [hb, hspin]
  push_cast
  ring

theorem leeYangComplexFieldObservable_spinProd_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (h : ℂ) (A : Finset V) :
    leeYangComplexFieldObservableNumerator G beta
        (fun s ↦ (spinProd A s : ℂ)) (-h) =
      (((-1 : ℝ) : ℂ) ^ A.card) *
        leeYangComplexFieldObservableNumerator G beta
          (fun s ↦ (spinProd A s : ℂ)) h := by
  unfold leeYangComplexFieldObservableNumerator
  rw [← Equiv.sum_comp (flipV_involutive (V := V)).toPerm]
  simp only [Function.Involutive.coe_toPerm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hb : (∑ e ∈ G.edgeFinset, bond (flipV s) e) =
      ∑ e ∈ G.edgeFinset, bond s e :=
    Finset.sum_congr rfl (fun e _ ↦ bond_flipV s e)
  have hspin : (∑ x : V, spin (flipV s) x) = -∑ x : V, spin s x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ ↦ spin_flipV s x)
  rw [hb, hspin, spinProd_flipV]
  push_cast
  ring

theorem leeYangComplexFieldExpectation_spinProd_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (h : ℂ) (A : Finset V) :
    leeYangComplexFieldExpectation G beta
        (fun s ↦ (spinProd A s : ℂ)) (-h) =
      (((-1 : ℝ) : ℂ) ^ A.card) *
        leeYangComplexFieldExpectation G beta
          (fun s ↦ (spinProd A s : ℂ)) h := by
  unfold leeYangComplexFieldExpectation
  rw [leeYangComplexFieldObservable_spinProd_neg,
    leeYangComplexFieldPartition_neg]
  ring


theorem leeYangSpinProductLeftBound
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    LeeYangSpinProductLeftBound d beta A := by
  intro n h hh
  have hright := leeYangSpinProductRightBound d hbeta A n (-h)
    (by simpa using neg_pos.mpr hh)
  have hflip := leeYangComplexFieldExpectation_spinProd_neg
    (boxGraph d n) beta h (boxSpinSupport d n A)
  have hnormpow :
      ‖(((-1 : ℝ) : ℂ) ^ (boxSpinSupport d n A).card)‖ = 1 := by
    rw [norm_pow]
    norm_num
  rw [leeYangBoxSpinProduct, hflip, norm_mul, hnormpow, one_mul] at hright
  simpa only [leeYangBoxSpinProduct, leeYangSpinProductRightEnvelope,
    leeYangSpinProductLeftEnvelope, neg_mul, mul_neg, neg_neg] using hright



theorem leeYangBoxSpinProduct_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d)) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | 0 < z.re} :=
  leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound
    d hd hbeta A (leeYangSpinProductRightBound d hbeta A)


theorem leeYangBoxSpinProduct_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d)) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | z.re < 0} :=
  leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound
    d hd hbeta A (leeYangSpinProductLeftBound d hbeta A)

end StatMech.FrontierA
