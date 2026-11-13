/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBethePhysicalCoordinate
import Code.FrontierD.SixVertexBetheContinuumUniqueness





namespace StatMech.FrontierD

noncomputable section

private theorem neg_pi_le_pi : -Real.pi <= Real.pi := by
  linarith [Real.pi_pos]



def sixVertexRapidityMomentumOrderIso
    (lam : Real) (hlam : 0 < lam) :
    Set.Icc (-Real.pi) Real.pi ≃o Set.Icc (-Real.pi) Real.pi := by
  let f : Set.Icc (-Real.pi) Real.pi -> Set.Icc (-Real.pi) Real.pi :=
    fun alpha => ⟨sixVertexRapidityMomentum lam alpha,
      sixVertexRapidityMomentum_mem_Icc hlam alpha.property⟩
  have hfStrict : StrictMono f := by
    intro alpha beta hab
    exact strictMono_sixVertexRapidityMomentum hlam hab
  have hfSurj : Function.Surjective f := by
    intro x
    have hcontinuous : Continuous (sixVertexRapidityMomentum lam) :=
      continuous_iff_continuousAt.2 fun alpha =>
        (hasDerivAt_sixVertexRapidityMomentum hlam alpha).continuousAt
    have hcont : ContinuousOn (sixVertexRapidityMomentum lam)
        (Set.Icc (-Real.pi) Real.pi) :=
      hcontinuous.continuousOn
    have hxRange : (x : Real) ∈ Set.Icc
        (sixVertexRapidityMomentum lam (-Real.pi))
        (sixVertexRapidityMomentum lam Real.pi) := by
      rw [sixVertexRapidityMomentum_neg_pi hlam,
        sixVertexRapidityMomentum_pi hlam]
      exact x.property
    obtain ⟨alpha, halpha, heq⟩ :=
      intermediate_value_Icc neg_pi_le_pi hcont hxRange
    exact ⟨⟨alpha, halpha⟩, Subtype.ext heq⟩
  exact StrictMono.orderIsoOfSurjective f hfStrict hfSurj


def sixVertexMomentumRapidity
    (lam : Real) (hlam : 0 < lam) (x : Real) : Real :=
  ((sixVertexRapidityMomentumOrderIso lam hlam).symm
    (Set.projIcc (-Real.pi) Real.pi neg_pi_le_pi x) : Real)

theorem continuous_sixVertexMomentumRapidity
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexMomentumRapidity lam hlam) := by
  unfold sixVertexMomentumRapidity
  exact continuous_subtype_val.comp
    ((sixVertexRapidityMomentumOrderIso lam hlam).symm.continuous.comp
      continuous_projIcc)

theorem sixVertexMomentumRapidity_rapidityMomentum
    {lam : Real} (hlam : 0 < lam) {alpha : Real}
    (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexMomentumRapidity lam hlam
        (sixVertexRapidityMomentum lam alpha) = alpha := by
  unfold sixVertexMomentumRapidity
  rw [Set.projIcc_of_mem neg_pi_le_pi
    (sixVertexRapidityMomentum_mem_Icc hlam halpha)]
  exact congrArg Subtype.val
    ((sixVertexRapidityMomentumOrderIso lam hlam).symm_apply_apply
      ⟨alpha, halpha⟩)

theorem sixVertexRapidityMomentum_momentumRapidity
    {lam : Real} (hlam : 0 < lam) {x : Real}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRapidityMomentum lam
      (sixVertexMomentumRapidity lam hlam x) = x := by
  unfold sixVertexMomentumRapidity
  rw [Set.projIcc_of_mem neg_pi_le_pi hx]
  exact congrArg Subtype.val
    ((sixVertexRapidityMomentumOrderIso lam hlam).apply_symm_apply ⟨x, hx⟩)


def sixVertexFourierPhysicalDensity
    (c : Real) (hc : 2 < c) (x : Real) : Real :=
  let lam := sixVertexAntiferroelectricLambda c
  sixVertexFourierRootDensity lam
      (sixVertexMomentumRapidity lam
        (sixVertexAntiferroelectricLambda_pos hc) x) /
    (2 * Real.pi * sixVertexRootDensityWeight c x)

theorem continuous_sixVertexFourierPhysicalDensity
    {c : Real} (hc : 2 < c) :
    Continuous (sixVertexFourierPhysicalDensity c hc) := by
  let lam := sixVertexAntiferroelectricLambda c
  let hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  unfold sixVertexFourierPhysicalDensity
  apply Continuous.div
  · exact (continuous_sixVertexFourierRootDensity hlam).comp
      (continuous_sixVertexMomentumRapidity hlam)
  · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  · intro x
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (sixVertexRootDensityWeight_pos hc x).ne'

theorem sixVertexFourierPhysicalDensity_rapidityMomentum
    {c : Real} (hc : 2 < c) {alpha : Real}
    (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexFourierPhysicalDensity c hc
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexFourierRootDensity
          (sixVertexAntiferroelectricLambda c) alpha /
        (2 * Real.pi *
          sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha) := by
  dsimp only [sixVertexFourierPhysicalDensity]
  rw [sixVertexMomentumRapidity_rapidityMomentum
    (sixVertexAntiferroelectricLambda_pos hc) halpha,
    sixVertexRootDensityWeight_rapidityMomentum hc]

theorem intervalIntegral_sixVertexFourierPhysicalDensity
    {c : Real} (hc : 2 < c) :
    (∫ x in -Real.pi..Real.pi,
      sixVertexFourierPhysicalDensity c hc x) = 1 / 2 := by
  let lam := sixVertexAntiferroelectricLambda c
  let hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi)
    (f := sixVertexRapidityMomentum lam)
    (f' := sixVertexXiFourier lam)
    (g := sixVertexFourierPhysicalDensity c hc)
    (fun alpha _ => hasDerivAt_sixVertexRapidityMomentum hlam alpha)
    (continuous_sixVertexXiFourier hlam).continuousOn
    (continuous_sixVertexFourierPhysicalDensity hc)
  rw [sixVertexRapidityMomentum_neg_pi hlam,
    sixVertexRapidityMomentum_pi hlam] at hsubst
  rw [<- hsubst]
  have hintegral :
      (∫ alpha in -Real.pi..Real.pi,
        (sixVertexFourierPhysicalDensity c hc ∘
          sixVertexRapidityMomentum lam) alpha *
            sixVertexXiFourier lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        sixVertexFourierRootDensity lam alpha / (2 * Real.pi) := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    rw [Set.uIcc_of_le neg_pi_le_pi] at halpha
    dsimp only [Function.comp_apply]
    dsimp [lam]
    rw [sixVertexFourierPhysicalDensity_rapidityMomentum hc halpha]
    have hXi : sixVertexXiFourier lam alpha ≠ 0 :=
      (sixVertexXiFourier_pos hlam alpha).ne'
    field_simp [hXi, Real.pi_ne_zero]
    exact mul_div_cancel_right₀ _ hXi
  rw [hintegral]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral_sixVertexFourierRootDensity hlam]
  field_simp [Real.pi_ne_zero]



theorem sixVertexFourierPhysicalDensity_continuumEquation
    {c : Real} (hc : 2 < c) :
    SixVertexSatisfiesContinuousDensityEquation c
      (sixVertexFourierPhysicalDensity c hc) := by
  let lam := sixVertexAntiferroelectricLambda c
  let hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  intro x hx
  let alpha := sixVertexMomentumRapidity lam hlam x
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi neg_pi_le_pi x)).property
  have hxk : sixVertexRapidityMomentum lam alpha = x := by
    dsimp [alpha]
    exact sixVertexRapidityMomentum_momentumRapidity hlam hx
  have hweight : sixVertexRootDensityWeight c x =
      sixVertexXiFourier lam alpha := by
    rw [<- hxk]
    exact sixVertexRootDensityWeight_rapidityMomentum hc alpha
  let g : Real -> Real := fun y =>
    sixVertexRootDensityKernel c x y *
      sixVertexFourierPhysicalDensity c hc y
  have hg : Continuous g :=
    ((lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous).mul
      (continuous_sixVertexFourierPhysicalDensity hc)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi)
    (f := sixVertexRapidityMomentum lam)
    (f' := sixVertexXiFourier lam) (g := g)
    (fun beta _ => hasDerivAt_sixVertexRapidityMomentum hlam beta)
    (continuous_sixVertexXiFourier hlam).continuousOn hg
  rw [sixVertexRapidityMomentum_neg_pi hlam,
    sixVertexRapidityMomentum_pi hlam] at hsubst
  have hpulled :
      (∫ beta in -Real.pi..Real.pi,
        (g ∘ sixVertexRapidityMomentum lam) beta *
          sixVertexXiFourier lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        (sixVertexXiFourier (2 * lam) (alpha - beta) *
          sixVertexFourierRootDensity lam beta) / (2 * Real.pi) := by
    apply intervalIntegral.integral_congr
    intro beta hbeta
    rw [Set.uIcc_of_le neg_pi_le_pi] at hbeta
    dsimp only [Function.comp_apply, g]
    rw [<- hxk, sixVertexRootDensityKernel_rapidityMomentum hc,
      sixVertexFourierPhysicalDensity_rapidityMomentum hc hbeta]
    have hXi : sixVertexXiFourier lam beta ≠ 0 :=
      (sixVertexXiFourier_pos hlam beta).ne'
    field_simp [hXi, Real.pi_ne_zero]
    exact mul_div_cancel_right₀ _ hXi
  have hphysicalIntegral :
      (∫ y in -Real.pi..Real.pi,
        sixVertexRootDensityKernel c x y *
          sixVertexFourierPhysicalDensity c hc y) =
      (1 / (2 * Real.pi)) *
        ∫ beta in -Real.pi..Real.pi,
          sixVertexXiFourier (2 * lam) (alpha - beta) *
            sixVertexFourierRootDensity lam beta := by
    change (∫ y in -Real.pi..Real.pi, g y) = _
    rw [<- hsubst, hpulled]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const]
    ring
  have htrans := sixVertexFourierRootDensity_integralEquation hlam alpha
  have hrho : sixVertexFourierPhysicalDensity c hc x =
      sixVertexFourierRootDensity lam alpha /
        (2 * Real.pi * sixVertexXiFourier lam alpha) := by
    rw [← hxk]
    exact sixVertexFourierPhysicalDensity_rapidityMomentum hc halpha
  rw [hweight, hrho, hphysicalIntegral]
  have hXi : sixVertexXiFourier lam alpha ≠ 0 :=
    (sixVertexXiFourier_pos hlam alpha).ne'
  rw [htrans]
  field_simp [hXi, Real.pi_ne_zero]


theorem sixVertexTailRootDensity_eq_fourierPhysicalDensity
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      sixVertexTailRootDensity hc htail x =
        sixVertexFourierPhysicalDensity c hc x := by
  apply sixVertexRootDensity_continuumEquation_unique hc
  · exact continuous_sixVertexTailRootDensity hc htail
  · exact continuous_sixVertexFourierPhysicalDensity hc
  · exact intervalIntegral_sixVertexTailRootDensity hc htail
  · exact intervalIntegral_sixVertexFourierPhysicalDensity hc
  · intro x hx
    exact sixVertexTailRootDensity_continuumEquation hc htail hx
  · exact sixVertexFourierPhysicalDensity_continuumEquation hc

end

end StatMech.FrontierD
