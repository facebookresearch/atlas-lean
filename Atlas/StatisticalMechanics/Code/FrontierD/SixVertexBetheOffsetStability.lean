/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheContinuousOffset









namespace StatMech.FrontierD

open Filter Topology

noncomputable section


def sixVertexContinuousOffsetResidual
    (c : Real) (f : Real → Real) (x : Real) : Real :=
  2 * Real.pi * f x - sixVertexContinuousOffsetSource c x +
    ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c x y * f y

theorem sixVertexContinuousOffsetResidual_eq_zero
    {c : Real} {f : Real → Real}
    (hf : SixVertexSatisfiesContinuousOffsetEquation c f)
    {x : Real} (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexContinuousOffsetResidual c f x = 0 := by
  have h := hf x hx
  unfold sixVertexContinuousOffsetResidual
  linarith



theorem sixVertexContinuousOffset_error_le_residual
    {c : Real} (hc : 2 < c) {tau f : Real → Real} {ε : Real}
    (htau : Continuous tau) (hf : Continuous f)
    (htauOdd : Function.Odd tau) (hfOdd : Function.Odd f)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    (hres : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexContinuousOffsetResidual c f x| ≤ ε) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |f x - tau x| ≤
        ε / (2 * Real.pi *
          (1 - sixVertexRootDensityContractionRate c)) := by
  let e : Real → Real := fun y => f y - tau y
  have he : Continuous e := hf.sub htau
  have heOdd : Function.Odd e := by
    intro y
    dsimp [e]
    rw [hfOdd y, htauOdd y]
    ring
  have hweight : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have heQuotOdd : Function.Odd
      (fun y => e y / sixVertexRootDensityWeight c y) := by
    intro y
    dsimp only
    rw [heOdd y, sixVertexRootDensityWeight_neg]
    ring
  have heMass :
      (∫ y in -Real.pi..Real.pi,
        e y / sixVertexRootDensityWeight c y) = 0 :=
    intervalIntegral_neg_pi_pi_eq_zero_of_odd heQuotOdd
  have hnonempty : (Set.Icc (-Real.pi) Real.pi).Nonempty :=
    Set.nonempty_Icc.2 (by linarith [Real.pi_pos])
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn hnonempty
    he.abs.continuousOn
  let E := |e x0|
  have hE : 0 ≤ E := abs_nonneg _
  have hbound : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |e y| ≤ E :=
    fun y hy => hmax hy
  have hcontract := sixVertexRootDensityKernel_contraction hc he hE heMass
    hbound x0
  have hkernel (x : Real) : Continuous
      (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      hweight (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hresidualIdentity
      (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      sixVertexContinuousOffsetResidual c f x =
        2 * Real.pi * e x +
          ∫ y in -Real.pi..Real.pi,
            sixVertexContinuousOffsetKernel c x y * e y := by
    let IF := ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c x y * f y
    let IT := ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c x y * tau y
    have hFint : IntervalIntegrable
        (fun y => sixVertexContinuousOffsetKernel c x y * f y)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((hkernel x).mul hf).intervalIntegrable _ _
    have hTint : IntervalIntegrable
        (fun y => sixVertexContinuousOffsetKernel c x y * tau y)
        MeasureTheory.volume (-Real.pi) Real.pi :=
      ((hkernel x).mul htau).intervalIntegrable _ _
    have hJ :
        (∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c x y * e y) = IF - IT := by
      rw [show (fun y => sixVertexContinuousOffsetKernel c x y * e y) =
        fun y => sixVertexContinuousOffsetKernel c x y * f y -
          sixVertexContinuousOffsetKernel c x y * tau y by
          funext y
          dsimp [e]
          ring]
      exact intervalIntegral.integral_sub hFint hTint
    have hT := htauEq x hx
    change 2 * Real.pi * tau x =
      sixVertexContinuousOffsetSource c x - IT at hT
    unfold sixVertexContinuousOffsetResidual
    rw [hJ]
    dsimp [e, IF]
    linarith
  let q : Real := 1 / (2 * Real.pi)
  have hq : 0 < q := by dsimp [q]; positivity
  have hidentity
      (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      e x = -q *
          (∫ y in -Real.pi..Real.pi,
            sixVertexContinuousOffsetKernel c x y * e y) +
        q * sixVertexContinuousOffsetResidual c f x := by
    rw [hresidualIdentity x hx]
    dsimp [q]
    field_simp [Real.pi_ne_zero]
    ring
  have hcontract' :
      |q * (∫ y in -Real.pi..Real.pi,
        sixVertexContinuousOffsetKernel c x0 y * e y)| ≤
        sixVertexRootDensityContractionRate c * E := by
    simpa only [q, sixVertexContinuousOffsetKernel] using hcontract
  have hle :
      E ≤ sixVertexRootDensityContractionRate c * E + q * ε := by
    calc
      E = |e x0| := rfl
      _ = |-q * (∫ y in -Real.pi..Real.pi,
            sixVertexContinuousOffsetKernel c x0 y * e y) +
          q * sixVertexContinuousOffsetResidual c f x0| := by
        rw [hidentity x0 hx0]
      _ ≤ |q * (∫ y in -Real.pi..Real.pi,
            sixVertexContinuousOffsetKernel c x0 y * e y)| +
          q * |sixVertexContinuousOffsetResidual c f x0| := by
        calc
          _ ≤ |-q * (∫ y in -Real.pi..Real.pi,
                sixVertexContinuousOffsetKernel c x0 y * e y)| +
              |q * sixVertexContinuousOffsetResidual c f x0| := abs_add_le _ _
          _ = _ := by simp only [abs_mul, abs_neg, abs_of_pos hq]
      _ ≤ sixVertexRootDensityContractionRate c * E + q * ε :=
        add_le_add hcontract'
          (mul_le_mul_of_nonneg_left (hres x0 hx0) hq.le)
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hgap : 0 < 1 - sixVertexRootDensityContractionRate c := by
    linarith [hrate.2]
  have hstep :
      (1 - sixVertexRootDensityContractionRate c) * E ≤ q * ε := by
    linarith
  have hden : 0 < 2 * Real.pi *
      (1 - sixVertexRootDensityContractionRate c) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hgap
  have hEbound : E ≤ ε / (2 * Real.pi *
      (1 - sixVertexRootDensityContractionRate c)) := by
    rw [le_div_iff₀ hden]
    calc
      E * (2 * Real.pi *
          (1 - sixVertexRootDensityContractionRate c)) =
          (2 * Real.pi) *
            ((1 - sixVertexRootDensityContractionRate c) * E) := by ring
      _ ≤ (2 * Real.pi) * (q * ε) :=
        mul_le_mul_of_nonneg_left hstep
          (mul_nonneg (by norm_num) Real.pi_pos.le)
      _ = ε := by
        dsimp [q]
        field_simp [Real.pi_ne_zero]
  intro x hx
  exact (hbound x hx).trans hEbound



theorem tendstoUniformlyOn_of_sixVertexContinuousOffsetResidual
    {c : Real} (hc : 2 < c) {tau : Real → Real}
    {f : Nat → Real → Real} {ε : Nat → Real}
    (htau : Continuous tau) (hf : ∀ n, Continuous (f n))
    (htauOdd : Function.Odd tau) (hfOdd : ∀ n, Function.Odd (f n))
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    (hres : ∀ n x, x ∈ Set.Icc (-Real.pi) Real.pi →
      |sixVertexContinuousOffsetResidual c (f n) x| ≤ ε n)
    (hεzero : Tendsto ε atTop (nhds 0)) :
    TendstoUniformlyOn f tau atTop
      (Set.Icc (-Real.pi) Real.pi) := by
  let D := 2 * Real.pi *
    (1 - sixVertexRootDensityContractionRate c)
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr hrate.2)
  have hquot : Tendsto (fun n => ε n / D) atTop (nhds 0) := by
    simpa using hεzero.div_const D
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [(tendsto_order.1 hquot).2 δ hδ] with n hn
  intro x hx
  rw [Real.dist_eq]
  have hbound := sixVertexContinuousOffset_error_le_residual hc
    htau (hf n) htauOdd (hfOdd n) htauEq (hres n)
    x hx
  dsimp [D] at hn
  rw [abs_sub_comm]
  exact hbound.trans_lt hn

end

end StatMech.FrontierD
