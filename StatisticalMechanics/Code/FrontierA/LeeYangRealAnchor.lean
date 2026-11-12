/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierA.LeeYangNormalFamilyReduction
import Code.Ising.PressureConvex
import Code.Sharpness.GHSFull
import Code.FK.FKPressureDeriv

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


noncomputable def isingBoxPressureLimit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) : ℝ :=
  Classical.choose (isingBoxPressure_tendsto d hd beta h)

theorem isingBoxPressure_tendsto_limit
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto (isingBoxPressureSeq d beta h) atTop
      (nhds (isingBoxPressureLimit d hd beta h)) :=
  Classical.choose_spec (isingBoxPressure_tendsto d hd beta h)



theorem isingBoxPressureSeq_convexOn_field
    (d n : ℕ) (beta : ℝ) :
    ConvexOn ℝ univ (fun h => isingBoxPressureSeq d beta h n) := by
  have hconv := isingLogZ_convexOn_field (boxGraph d n) beta
  have hscale : 0 ≤ (1 / (Fintype.card (boxVerts d n) : ℝ)) := by positivity
  have hscaled := hconv.smul hscale
  refine hscaled.congr ?_
  intro h _
  simp only [isingBoxPressureSeq, isingBoxLogZ, smul_eq_mul]
  ring


noncomputable def isingBoxPressureFieldDerivative
    (d n : ℕ) (beta h : ℝ) : ℝ :=
  beta * isingExpectation (boxGraph d n) beta h
      (fun s => ∑ v, spin s v) /
    (Fintype.card (boxVerts d n) : ℝ)

theorem isingBoxPressureSeq_hasDerivAt_field
    (d n : ℕ) (beta h : ℝ) :
    HasDerivAt (fun x => isingBoxPressureSeq d beta x n)
      (isingBoxPressureFieldDerivative d n beta h) h := by
  let G := boxGraph d n
  have hZ := hasDerivAt_isingZ G beta h
  have hlog := hZ.log (isingZ_ne_zero G beta h)
  have hdiv := hlog.div_const (Fintype.card (boxVerts d n) : ℝ)
  have hexpect := expectation_eq_div G beta h (fun s => ∑ v, spin s v)
  convert hdiv using 1
  unfold isingBoxPressureFieldDerivative
  rw [hexpect]
  have hsum :
      (∑ s : ConfigSpace (boxVerts d n),
        isingWeight G beta h s * (beta * ∑ x, spin s x)) =
        beta * ∑ s : ConfigSpace (boxVerts d n),
          (∑ x, spin s x) * isingWeight G beta h s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum]
  ring



theorem leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative
    (d n : ℕ) (beta h : ℝ) :
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta (h : ℂ) =
      (isingBoxPressureFieldDerivative d n beta h : ℂ) := by
  rw [leeYangNormalizedFieldLogDerivative_ofReal]
  unfold isingBoxPressureFieldDerivative
  push_cast
  rfl


theorem isingBoxPressureLimit_convexOn_field
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    ConvexOn ℝ univ (isingBoxPressureLimit d hd beta) :=
  cdl_limit_convexOn
    (fun n h => isingBoxPressureSeq d beta h n)
    (isingBoxPressureLimit d hd beta)
    (fun n => isingBoxPressureSeq_convexOn_field d n beta)
    (fun h => isingBoxPressure_tendsto_limit d hd beta h)



def leeYangPressureRegularRealSet
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) : Set ℝ :=
  {h | pressureLeftDeriv (isingBoxPressureLimit d hd beta) h =
    pressureRightDeriv (isingBoxPressureLimit d hd beta) h}


theorem leeYangPressureRegularRealSet_countable_compl
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    (leeYangPressureRegularRealSet d hd beta)ᶜ.Countable := by
  simpa only [leeYangPressureRegularRealSet, mem_setOf_eq, compl_setOf]
    using cdl_countable_leftDeriv_ne_rightDeriv
      (isingBoxPressureLimit_convexOn_field d hd beta)



theorem isingBoxPressureFieldDerivative_tendsto_of_regular
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ)
    (hh : h ∈ leeYangPressureRegularRealSet d hd beta) :
    Tendsto (fun n => isingBoxPressureFieldDerivative d n beta h) atTop
      (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
  exact fpd_deriv_interchange_of_differentiable
    (fun n x => isingBoxPressureSeq d beta x n)
    (isingBoxPressureLimit d hd beta)
    (fun n x => isingBoxPressureFieldDerivative d n beta x)
    (fun n => isingBoxPressureSeq_convexOn_field d n beta)
    (fun n x => isingBoxPressureSeq_hasDerivAt_field d n beta x)
    (fun x => isingBoxPressure_tendsto_limit d hd beta x)
    h (isingBoxPressureLimit_convexOn_field d hd beta) hh



theorem leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ)
    (hh : h ∈ leeYangPressureRegularRealSet d hd beta) :
    Tendsto
      (fun n => leeYangNormalizedFieldLogDerivative
        (boxGraph d n) beta (h : ℂ))
      atTop
      (nhds (pressureRightDeriv
        (isingBoxPressureLimit d hd beta) h : ℂ)) := by
  have hreal := isingBoxPressureFieldDerivative_tendsto_of_regular
    d hd beta h hh
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact hcomplex.congr' (Eventually.of_forall fun n =>
    (leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative
      d n beta h).symm)


def leeYangRightRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ 0 < z.re ∧
    z.re ∈ leeYangPressureRegularRealSet d hd beta}

theorem leeYangRightRealAnchor_subset_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    leeYangRightRealAnchor d hd beta ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  exact hz.2.1



theorem leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    {z : ℂ} (hz : z ∈ leeYangRightRealAnchor d hd beta) :
    Tendsto
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta z)
      atTop
      (nhds (pressureRightDeriv
        (isingBoxPressureLimit d hd beta) z.re : ℂ)) := by
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext
    · simp
    · simpa using hz.1.symm
  simpa only [hzreal] using
    leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular
      d hd beta z.re hz.2.2



theorem leeYangRightRealAnchor_frequently_near
    (d : ℕ) (hd : 1 ≤ d) (beta h₀ : ℝ) (hh₀ : 0 < h₀) :
    ∃ᶠ z in nhdsWithin (h₀ : ℂ) ({(h₀ : ℂ)}ᶜ),
      z ∈ leeYangRightRealAnchor d hd beta := by
  have hregularDense : Dense (leeYangPressureRegularRealSet d hd beta) := by
    have h := (leeYangPressureRegularRealSet_countable_compl d hd beta).dense_compl ℝ
    simpa only [compl_compl] using h
  have hclosure : (h₀ : ℂ) ∈
      closure (leeYangRightRealAnchor d hd beta \ {(h₀ : ℂ)}) := by
    refine mem_closure_iff.2 ?_
    intro U hUopen hhU
    let W : Set ℝ := ((Complex.ofReal ⁻¹' U) ∩ Ioi 0) \ {h₀}
    have hWopen : IsOpen W := by
      exact ((hUopen.preimage Complex.continuous_ofReal).inter isOpen_Ioi).sdiff
        isClosed_singleton
    have hbase : (Complex.ofReal ⁻¹' U) ∩ Ioi 0 ∈ nhds h₀ :=
      Filter.inter_mem
        ((hUopen.preimage Complex.continuous_ofReal).mem_nhds hhU)
        (isOpen_Ioi.mem_nhds hh₀)
    have hWnonempty : W.Nonempty := by
      obtain ⟨l, u, hlu, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp hbase
      obtain ⟨y, hh₀y, hyu⟩ := exists_between hlu.2
      have hybase : y ∈ (Complex.ofReal ⁻¹' U) ∩ Ioi 0 :=
        hsub ⟨hlu.1.trans hh₀y, hyu⟩
      exact ⟨y, hybase, by simpa using ne_of_gt hh₀y⟩
    obtain ⟨y, hyW, hyregular⟩ :=
      hregularDense.inter_open_nonempty W hWopen hWnonempty
    refine ⟨(y : ℂ), hyW.1.1, ?_⟩
    constructor
    · exact ⟨by simp, hyW.1.2, hyregular⟩
    · simpa using hyW.2
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp hclosure).mono fun z hz =>
    ⟨hz.1, hz.2⟩




theorem leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (hcompact : IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | 0 < z.re}) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | 0 < z.re} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  let U : Set ℂ := {z | 0 < z.re}
  let anchor := leeYangRightRealAnchor d hd beta
  let anchorLimit : ℂ → ℂ := fun z =>
    (pressureRightDeriv (isingBoxPressureLimit d hd beta) z.re : ℂ)
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconnected : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U :=
    (leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane
      d hbeta).1
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    exact leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor
      d hd beta hz
  simpa only [F, U, anchor, anchorLimit] using
    montelVitali_of_locallyUniform_precompact
      F U anchor (1 : ℂ) anchorLimit hUopen hUconnected
      (by change 0 < (1 : ℂ).re; norm_num)
      (leeYangRightRealAnchor_subset_rightHalfPlane d hd beta)
      (by simpa using leeYangRightRealAnchor_frequently_near d hd beta 1 zero_lt_one)
      hholomorphic hcompact hanchorLimit


def leeYangLeftRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ z.re < 0 ∧
    z.re ∈ leeYangPressureRegularRealSet d hd beta}

theorem leeYangLeftRealAnchor_subset_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    leeYangLeftRealAnchor d hd beta ⊆ {z : ℂ | z.re < 0} := by
  intro z hz
  exact hz.2.1

theorem leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    {z : ℂ} (hz : z ∈ leeYangLeftRealAnchor d hd beta) :
    Tendsto
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta z)
      atTop
      (nhds (pressureRightDeriv
        (isingBoxPressureLimit d hd beta) z.re : ℂ)) := by
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext
    · simp
    · simpa using hz.1.symm
  simpa only [hzreal] using
    leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular
      d hd beta z.re hz.2.2

theorem leeYangLeftRealAnchor_frequently_near
    (d : ℕ) (hd : 1 ≤ d) (beta h₀ : ℝ) (hh₀ : h₀ < 0) :
    ∃ᶠ z in nhdsWithin (h₀ : ℂ) ({(h₀ : ℂ)}ᶜ),
      z ∈ leeYangLeftRealAnchor d hd beta := by
  have hregularDense : Dense (leeYangPressureRegularRealSet d hd beta) := by
    have h := (leeYangPressureRegularRealSet_countable_compl d hd beta).dense_compl ℝ
    simpa only [compl_compl] using h
  have hclosure : (h₀ : ℂ) ∈
      closure (leeYangLeftRealAnchor d hd beta \ {(h₀ : ℂ)}) := by
    refine mem_closure_iff.2 ?_
    intro U hUopen hhU
    let W : Set ℝ := ((Complex.ofReal ⁻¹' U) ∩ Iio 0) \ {h₀}
    have hWopen : IsOpen W := by
      exact ((hUopen.preimage Complex.continuous_ofReal).inter isOpen_Iio).sdiff
        isClosed_singleton
    have hbase : (Complex.ofReal ⁻¹' U) ∩ Iio 0 ∈ nhds h₀ :=
      Filter.inter_mem
        ((hUopen.preimage Complex.continuous_ofReal).mem_nhds hhU)
        (isOpen_Iio.mem_nhds hh₀)
    have hWnonempty : W.Nonempty := by
      obtain ⟨l, u, hlu, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp hbase
      obtain ⟨y, hly, hyh₀⟩ := exists_between hlu.1
      have hybase : y ∈ (Complex.ofReal ⁻¹' U) ∩ Iio 0 :=
        hsub ⟨hly, hyh₀.trans hlu.2⟩
      exact ⟨y, hybase, by simpa using ne_of_lt hyh₀⟩
    obtain ⟨y, hyW, hyregular⟩ :=
      hregularDense.inter_open_nonempty W hWopen hWnonempty
    refine ⟨(y : ℂ), hyW.1.1, ?_⟩
    constructor
    · exact ⟨by simp, hyW.1.2, hyregular⟩
    · simpa using hyW.2
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp hclosure).mono fun z hz =>
    ⟨hz.1, hz.2⟩


theorem leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (hcompact : IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | z.re < 0}) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | z.re < 0} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  let U : Set ℂ := {z | z.re < 0}
  let anchor := leeYangLeftRealAnchor d hd beta
  let anchorLimit : ℂ → ℂ := fun z =>
    (pressureRightDeriv (isingBoxPressureLimit d hd beta) z.re : ℂ)
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hUconnected : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U :=
    (leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane
      d hbeta).1
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    exact leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor
      d hd beta hz
  simpa only [F, U, anchor, anchorLimit] using
    montelVitali_of_locallyUniform_precompact
      F U anchor (-1 : ℂ) anchorLimit hUopen hUconnected
      (by change (-1 : ℂ).re < 0; norm_num)
      (leeYangLeftRealAnchor_subset_leftHalfPlane d hd beta)
      (by simpa using leeYangLeftRealAnchor_frequently_near d hd beta (-1) (by norm_num))
      hholomorphic hcompact hanchorLimit

end StatMech.FrontierA
