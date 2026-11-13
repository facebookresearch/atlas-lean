/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheFourierPhysicalDensity
import Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate
import Mathlib.Topology.Homeomorph.Lemmas





namespace StatMech.FrontierD

noncomputable section

private theorem neg_pi_le_pi : -Real.pi ≤ Real.pi := by
  linarith [Real.pi_pos]

theorem continuous_sixVertexAntiferroelectricLambda_Icc
    {a b : Real} (ha : 2 < a) :
    Continuous (fun t : Set.Icc a b =>
      sixVertexAntiferroelectricLambda t.1) := by
  change Continuous (Real.arcosh ∘ fun t : Set.Icc a b =>
    (t.1 ^ 2 - 2) / 2)
  apply Real.continuousOn_arcosh.comp_continuous
  · fun_prop
  · intro t
    change 1 ≤ (t.1 ^ 2 - 2) / 2
    nlinarith [ha, t.2.1]

theorem sixVertexAntiferroelectricLambda_lower_Icc
    {a b : Real} (ha : 2 < a) (t : Set.Icc a b) :
    sixVertexAntiferroelectricLambda a ≤
      sixVertexAntiferroelectricLambda t.1 := by
  unfold sixVertexAntiferroelectricLambda
  rw [Real.arcosh_le_arcosh]
  · nlinarith [ha, t.2.1]
  · nlinarith [ha]
  · nlinarith [ha, t.2.1]

theorem continuous_sixVertexXiFourier_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexXiFourier
        (sixVertexAntiferroelectricLambda z.1.1) z.2) := by
  have hlam := continuous_sixVertexAntiferroelectricLambda_Icc (b := b) ha
  rw [show (fun z : Set.Icc a b × Real =>
      sixVertexXiFourier
        (sixVertexAntiferroelectricLambda z.1.1) z.2) =
      fun z => Real.sinh (sixVertexAntiferroelectricLambda z.1.1) /
        (Real.cosh (sixVertexAntiferroelectricLambda z.1.1) -
          Real.cos z.2) by
    funext z
    exact sixVertexXiFourier_eq
      (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2]
  apply Continuous.div
  · exact Real.continuous_sinh.comp (hlam.comp continuous_fst)
  · exact (Real.continuous_cosh.comp (hlam.comp continuous_fst)).sub
      (Real.continuous_cos.comp continuous_snd)
  · intro z
    have hcosh : 1 < Real.cosh
        (sixVertexAntiferroelectricLambda z.1.1) :=
      Real.one_lt_cosh.mpr
        (sixVertexAntiferroelectricLambda_pos
          (ha.trans_le z.1.2.1)).ne'
    nlinarith [Real.cos_le_one z.2]

theorem continuous_sixVertexRapidityMomentum_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Set.Icc (-Real.pi) Real.pi =>
      sixVertexRapidityMomentum
        (sixVertexAntiferroelectricLambda z.1.1) z.2.1) := by
  let X := Set.Icc a b × Set.Icc (-Real.pi) Real.pi
  let F : X → Real → Real := fun z t =>
    Real.sinh (sixVertexAntiferroelectricLambda z.1.1) /
      (Real.cosh (sixVertexAntiferroelectricLambda z.1.1) - Real.cos t)
  have hlam := continuous_sixVertexAntiferroelectricLambda_Icc (b := b) ha
  have hF : Continuous F.uncurry := by
    apply Continuous.div
    · exact Real.continuous_sinh.comp
        (hlam.comp continuous_fst.fst)
    · exact (Real.continuous_cosh.comp
        (hlam.comp continuous_fst.fst)).sub
          (Real.continuous_cos.comp continuous_snd)
    · intro z
      have hcosh : 1 < Real.cosh
          (sixVertexAntiferroelectricLambda z.1.1.1) :=
        Real.one_lt_cosh.mpr
          (sixVertexAntiferroelectricLambda_pos
            (ha.trans_le z.1.1.2.1)).ne'
      nlinarith [Real.cos_le_one z.2]
  have hparam :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0) (f := F) hF
        continuous_snd.subtype_val
  change Continuous (fun z : X =>
    ∫ t in (0 : Real)..z.2.1, sixVertexXiFourier
      (sixVertexAntiferroelectricLambda z.1.1) t)
  convert hparam using 1
  funext z
  apply intervalIntegral.integral_congr
  intro t _
  exact sixVertexXiFourier_eq
    (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) t

def sixVertexRapidityMomentumFamilyEquiv
    {a b : Real} (ha : 2 < a) :
    (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) ≃
      (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) where
  toFun z :=
    (z.1, ⟨sixVertexRapidityMomentum
      (sixVertexAntiferroelectricLambda z.1.1) z.2.1,
      sixVertexRapidityMomentum_mem_Icc
        (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2.2⟩)
  invFun z :=
    (z.1, (sixVertexRapidityMomentumOrderIso
      (sixVertexAntiferroelectricLambda z.1.1)
      (sixVertexAntiferroelectricLambda_pos
        (ha.trans_le z.1.2.1))).symm z.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · exact (sixVertexRapidityMomentumOrderIso
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexAntiferroelectricLambda_pos
          (ha.trans_le z.1.2.1))).symm_apply_apply z.2
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact (sixVertexRapidityMomentumOrderIso
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexAntiferroelectricLambda_pos
          (ha.trans_le z.1.2.1))).apply_symm_apply z.2

theorem continuous_sixVertexRapidityMomentumFamilyEquiv
    {a b : Real} (ha : 2 < a) :
    Continuous (sixVertexRapidityMomentumFamilyEquiv (b := b) ha) := by
  apply Continuous.prodMk continuous_fst
  exact Continuous.subtype_mk
    (continuous_sixVertexRapidityMomentum_family (b := b) ha) _

def sixVertexRapidityMomentumFamilyHomeomorph
    {a b : Real} (ha : 2 < a) :
    (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) ≃ₜ
      (Set.Icc a b × Set.Icc (-Real.pi) Real.pi) :=
  (sixVertexRapidityMomentumFamilyEquiv (b := b) ha).toHomeomorphOfContinuousClosed
    (continuous_sixVertexRapidityMomentumFamilyEquiv (b := b) ha)
    (continuous_sixVertexRapidityMomentumFamilyEquiv (b := b) ha).isClosedMap

def sixVertexMomentumRapidityFamily
    {a b : Real} (ha : 2 < a)
    (z : Set.Icc a b × Real) : Real :=
  ((sixVertexRapidityMomentumFamilyHomeomorph (b := b) ha).symm
    (z.1, Set.projIcc (-Real.pi) Real.pi neg_pi_le_pi z.2)).2.1

theorem continuous_sixVertexMomentumRapidityFamily
    {a b : Real} (ha : 2 < a) :
    Continuous (sixVertexMomentumRapidityFamily (b := b) ha :
      Set.Icc a b × Real → Real) := by
  unfold sixVertexMomentumRapidityFamily
  exact continuous_subtype_val.comp
    ((sixVertexRapidityMomentumFamilyHomeomorph (b := b) ha).symm.continuous.comp
      (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)) |>.snd)

theorem sixVertexMomentumRapidityFamily_eq
    {a b : Real} (ha : 2 < a) (z : Set.Icc a b × Real) :
    sixVertexMomentumRapidityFamily (b := b) ha z =
      sixVertexMomentumRapidity
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2 := by
  rfl

theorem continuous_sixVertexFourierRootDensity_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1) z.2) := by
  apply continuous_const.add
  apply continuous_tsum
  · intro n
    unfold sixVertexFourierRootDensityTerm
    apply Continuous.div
    · fun_prop
    · exact Real.continuous_cosh.comp
        (((continuous_sixVertexAntiferroelectricLambda_Icc (b := b) ha).comp
          continuous_fst).const_mul (n + 1 : Real))
    · intro z
      exact (Real.cosh_pos _).ne'
  · exact summable_sixVertexFourierRootDensityMajorant
      (sixVertexAntiferroelectricLambda_pos ha)
  · intro n z
    calc
      ‖sixVertexFourierRootDensityTerm
          (sixVertexAntiferroelectricLambda z.1.1) n z.2‖ ≤
          sixVertexFourierRootDensityMajorant
            (sixVertexAntiferroelectricLambda z.1.1) n :=
        norm_sixVertexFourierRootDensityTerm_le
          (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) n z.2
      _ ≤ sixVertexFourierRootDensityMajorant
          (sixVertexAntiferroelectricLambda a) n := by
        unfold sixVertexFourierRootDensityMajorant
        have hlam := sixVertexAntiferroelectricLambda_lower_Icc ha z.1
        gcongr

theorem continuous_sixVertexRootDensityWeight_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexRootDensityWeight z.1.1 z.2) := by
  unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
    sixVertexRootDensityScale sixVertexAnisotropyMagnitude sixVertexDelta
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact (sixVertexRootDensityScale_pos
      (ha.trans_le z.1.2.1)).ne'

theorem continuous_sixVertexFourierPhysicalDensityFamily_fun
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexFourierRootDensity
          (sixVertexAntiferroelectricLambda z.1.1)
          (sixVertexMomentumRapidityFamily (b := b) ha z) /
        (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2)) := by
  have harg : Continuous (fun z : Set.Icc a b × Real =>
      (z.1, sixVertexMomentumRapidityFamily (b := b) ha z)) :=
    continuous_fst.prodMk
      (continuous_sixVertexMomentumRapidityFamily (b := b) ha)
  have hnum :=
    (continuous_sixVertexFourierRootDensity_family (b := b) ha).comp harg
  have hden : Continuous (fun z : Set.Icc a b × Real =>
      2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2) :=
    continuous_const.mul (continuous_sixVertexRootDensityWeight_family ha)
  apply hnum.div hden
  intro z
  exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (sixVertexRootDensityWeight_pos (ha.trans_le z.1.2.1) z.2).ne'

def sixVertexFourierPhysicalDensityFamily
    {a b : Real} (ha : 2 < a) :
    C(Set.Icc a b × Real, Real) :=
  ⟨fun z =>
      sixVertexFourierRootDensity
          (sixVertexAntiferroelectricLambda z.1.1)
          (sixVertexMomentumRapidityFamily (b := b) ha z) /
        (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2),
    continuous_sixVertexFourierPhysicalDensityFamily_fun ha⟩

theorem sixVertexFourierPhysicalDensityFamily_apply
    {a b : Real} (ha : 2 < a) (z : Set.Icc a b × Real) :
    sixVertexFourierPhysicalDensityFamily ha z =
      sixVertexFourierPhysicalDensity z.1.1
        (ha.trans_le z.1.2.1) z.2 := by
  change sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexMomentumRapidityFamily (b := b) ha z) /
      (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2) = _
  unfold sixVertexFourierPhysicalDensity
  rw [sixVertexMomentumRapidityFamily_eq (b := b)]

theorem sixVertexFourierPhysicalDensityFamily_continuumEquation
    {a b : Real} (ha : 2 < a) (t : Set.Icc a b) :
    SixVertexSatisfiesContinuousDensityEquation t.1
      (sixVertexContinuumDensityAt
        (sixVertexFourierPhysicalDensityFamily ha) t) := by
  simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, sixVertexFourierPhysicalDensityFamily_apply] using
    sixVertexFourierPhysicalDensity_continuumEquation
      (ha.trans_le t.2.1)

theorem intervalIntegral_sixVertexFourierPhysicalDensityFamily
    {a b : Real} (ha : 2 < a) (t : Set.Icc a b) :
    (∫ x in -Real.pi..Real.pi,
      sixVertexContinuumDensityAt
        (sixVertexFourierPhysicalDensityFamily ha) t x) = 1 / 2 := by
  apply (intervalIntegral.integral_congr fun x _ => ?_).trans
    (intervalIntegral_sixVertexFourierPhysicalDensity
      (ha.trans_le t.2.1))
  exact sixVertexFourierPhysicalDensityFamily_apply ha (t, x)

end

end StatMech.FrontierD
