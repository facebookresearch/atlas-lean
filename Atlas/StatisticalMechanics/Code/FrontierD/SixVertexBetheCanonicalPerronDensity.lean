/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheEventualPerronBranch
import Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate









open Filter Topology

namespace StatMech.FrontierD

noncomputable section




noncomputable def sixVertexPerronGaugeThreshold
    {c : Real} (hc : 2 < c) (n : Nat) : Nat := by
  classical
  exact if hn : n = 0 then 0 else
    Classical.choose (eventually_atTop.1
      (eventually_exists_sixVertexHalfFilledPerronGaugeWitness
        (epsilon := (1 : Real) / (n : Real) ^ 8) hc
        (by
          apply one_div_pos.mpr
          positivity)))

theorem sixVertexPerronGaugeThreshold_spec
    {c : Real} (hc : 2 < c) {n : Nat} (hn : 0 < n) :
    ∀ k ≥ sixVertexPerronGaugeThreshold hc n,
      ∃ p, SixVertexHalfFilledPerronGaugeWitness hc k
        ((1 : Real) / (n : Real) ^ 8) p := by
  rw [sixVertexPerronGaugeThreshold, dif_neg hn.ne']
  exact Classical.choose_spec (eventually_atTop.1
    (eventually_exists_sixVertexHalfFilledPerronGaugeWitness
      (epsilon := (1 : Real) / (n : Real) ^ 8) hc
      (by
        apply one_div_pos.mpr
        positivity)))

@[simp] theorem sixVertexPerronGaugeThreshold_zero
    {c : Real} (hc : 2 < c) :
    sixVertexPerronGaugeThreshold hc 0 = 0 := by
  simp [sixVertexPerronGaugeThreshold]


noncomputable def sixVertexPerronGaugeStage
    {c : Real} (hc : 2 < c) (k : Nat) : Nat := by
  classical
  exact Nat.findGreatest
    (fun n => sixVertexPerronGaugeThreshold hc n ≤ k)
      (Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))))

theorem sixVertexPerronGaugeStage_le_eighthRoot (hc : 2 < c) (k : Nat) :
    sixVertexPerronGaugeStage hc k ≤
      Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) := by
  classical
  exact Nat.findGreatest_le _

theorem sixVertexPerronGaugeStage_le (hc : 2 < c) (k : Nat) :
    sixVertexPerronGaugeStage hc k ≤ k + 1 :=
  (sixVertexPerronGaugeStage_le_eighthRoot hc k).trans
    ((Nat.sqrt_le_self _).trans
      ((Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)))

theorem sixVertexPerronGaugeStage_pow_eight_le
    (hc : 2 < c) (k : Nat) :
    (sixVertexPerronGaugeStage hc k) ^ 8 ≤ k + 1 := by
  let a := sixVertexPerronGaugeStage hc k
  let b := Nat.sqrt (Nat.sqrt (k + 1))
  let d := k + 1
  have ha : a * a ≤ b := by
    calc
      a * a = a ^ 2 := by ring
      _ ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) ^ 2 := by
        dsimp [a]
        exact pow_le_pow_left₀ (Nat.zero_le _)
          (sixVertexPerronGaugeStage_le_eighthRoot hc k) 2
      _ = Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) *
          Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) := by ring
      _ ≤ b := by simpa [b] using Nat.sqrt_le (Nat.sqrt (Nat.sqrt (k + 1)))
  have hb : b * b ≤ Nat.sqrt (k + 1) := by
    simpa [b] using Nat.sqrt_le (Nat.sqrt (k + 1))
  have hd : Nat.sqrt (k + 1) * Nat.sqrt (k + 1) ≤ d := by
    simpa [d] using Nat.sqrt_le (k + 1)
  have ha4 : (a * a) * (a * a) ≤ b * b :=
    Nat.mul_le_mul ha ha
  have ha4' : a ^ 4 ≤ Nat.sqrt (k + 1) := by
    calc
      a ^ 4 = (a * a) * (a * a) := by ring
      _ ≤ b * b := ha4
      _ ≤ Nat.sqrt (k + 1) := hb
  calc
    a ^ 8 = a ^ 4 * a ^ 4 := by ring
    _ ≤ Nat.sqrt (k + 1) * Nat.sqrt (k + 1) :=
      Nat.mul_le_mul ha4' ha4'
    _ ≤ d := hd

theorem sixVertexPerronGaugeStage_threshold_le
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexPerronGaugeThreshold hc
        (sixVertexPerronGaugeStage hc k) ≤ k := by
  classical
  unfold sixVertexPerronGaugeStage
  exact Nat.findGreatest_spec
    (P := fun n => sixVertexPerronGaugeThreshold hc n ≤ k)
    (m := 0) (Nat.zero_le _) (by simp)

theorem tendsto_sixVertexPerronGaugeStage
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexPerronGaugeStage hc) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro n
  refine ⟨max (n ^ 8) (sixVertexPerronGaugeThreshold hc n), ?_⟩
  intro k hk
  classical
  apply Nat.le_findGreatest
  · rw [Nat.le_sqrt, Nat.le_sqrt, Nat.le_sqrt]
    have hn : n ^ 8 ≤ k + 1 :=
      (le_max_left _ _).trans hk |>.trans (Nat.le_add_right _ _)
    calc
      n * n * (n * n) * (n * n * (n * n)) = n ^ 8 := by ring
      _ ≤ k + 1 := hn
  · exact (le_max_right _ _).trans hk



noncomputable def sixVertexCanonicalDensityPerronBetheRoots
    {c : Real} (hc : 2 < c) (k : Nat) :
    Fin ((k + 1) + (k + 1)) → Real := by
  classical
  let stage := sixVertexPerronGaugeStage hc k
  exact if hs : 0 < stage then
      Classical.choose
        (sixVertexPerronGaugeThreshold_spec hc hs k
          (sixVertexPerronGaugeStage_threshold_le hc k))
    else
      sixVertexCanonicalPerronBetheRoots hc k

theorem sixVertexCanonicalDensityPerronBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexOpenRootSimplex
      (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
  let stage := sixVertexPerronGaugeStage hc k
  by_cases hs : 0 < stage
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_pos hs]
    exact (Classical.choose_spec
      (sixVertexPerronGaugeThreshold_spec hc hs k
        (sixVertexPerronGaugeStage_threshold_le hc k))).1.1
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_neg hs]
    exact sixVertexCanonicalPerronBetheRoots_mem_open hc k

theorem sixVertexCanonicalDensityPerronBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
  let stage := sixVertexPerronGaugeStage hc k
  by_cases hs : 0 < stage
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_pos hs]
    exact (Classical.choose_spec
      (sixVertexPerronGaugeThreshold_spec hc hs k
        (sixVertexPerronGaugeStage_threshold_le hc k))).1.2.1
  · rw [sixVertexCanonicalDensityPerronBetheRoots, dif_neg hs]
    exact sixVertexCanonicalPerronBetheRoots_is_solution hc k

theorem eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      SixVertexHalfFilledPerronGaugeWitness hc k
        ((1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 8)
        (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
  have hstagePos : ∀ᶠ k : Nat in atTop,
      0 < sixVertexPerronGaugeStage hc k :=
    (tendsto_sixVertexPerronGaugeStage hc).eventually (eventually_gt_atTop 0)
  filter_upwards [hstagePos] with k hk
  rw [sixVertexCanonicalDensityPerronBetheRoots, dif_pos hk]
  exact Classical.choose_spec
    (sixVertexPerronGaugeThreshold_spec hc hk k
      (sixVertexPerronGaugeStage_threshold_le hc k))

def sixVertexCanonicalDensityPerronGauge
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  sixVertexWeightedFiniteDensityGauge hc
    (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
    (sixVertexFourierPhysicalDensityMap hc)

theorem eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalDensityPerronGauge hc k <
        (1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 8 := by
  filter_upwards
    [eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc]
      with k hk
  exact hk.2

theorem tendsto_sixVertexCanonicalDensityPerronGauge
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalDensityPerronGauge hc) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hupper : Tendsto (fun k =>
      (1 : Real) / sixVertexPerronGaugeStage hc k) atTop (nhds 0) :=
    hstageReal.const_div_atTop 1
  have hstagePos : ∀ᶠ k : Nat in atTop,
      0 < sixVertexPerronGaugeStage hc k :=
    (tendsto_sixVertexPerronGaugeStage hc).eventually
      (eventually_gt_atTop 0)
  apply squeeze_zero'
  · filter_upwards [] with k
    exact norm_nonneg _
  · filter_upwards
      [hstagePos,
        eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc]
      with k hkPos hk
    have hstage : (1 : Real) ≤ sixVertexPerronGaugeStage hc k := by
      exact_mod_cast hkPos
    have hpow : (sixVertexPerronGaugeStage hc k : Real) ≤
        (sixVertexPerronGaugeStage hc k : Real) ^ 8 := by
      simpa using pow_le_pow_right₀ hstage (show 1 ≤ 8 by omega)
    exact hk.2.le.trans (by
      apply one_div_le_one_div_of_le (a :=
        (sixVertexPerronGaugeStage hc k : Real)) (by positivity)
      exact hpow)
  · exact hupper



theorem eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower
    {c : Real} (hc : 2 < c) :
    ∃ lower : Real, 0 < lower ∧
      ∀ᶠ k : Nat in atTop, ∀ x : Real,
        lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc k) x := by
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici hc
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  let lower := rhoLower / 2
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have htarget : 0 < rhoLower * wmin / 2 := by positivity
  have hgauge : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalDensityPerronGauge hc k < rhoLower * wmin / 2 :=
    (tendsto_sixVertexCanonicalDensityPerronGauge hc).eventually
      (Iio_mem_nhds htarget)
  refine ⟨lower, hlower, ?_⟩
  filter_upwards [hgauge] with k hk
  intro x
  let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1))
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
  let rho := sixVertexFourierPhysicalDensity c hc
  obtain ⟨y, hy, hxy⟩ :=
    (periodic_sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc k)).exists_mem_Ioc
        (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
  have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
    exact ⟨hy.1.le, by linarith [hy.2]⟩
  have hpoint := abs_weightedFiniteDensity_sub_le_gauge hc
    (N := sixVertexFourWidth 0 k)
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
    (sixVertexFourierPhysicalDensityMap hc)
    y hyIcc
  have hweighted : wmin * |rhoN y - rho y| < rhoLower * wmin / 2 := by
    calc
      wmin * |rhoN y - rho y| ≤
          sixVertexRootDensityWeight c y * |rhoN y - rho y| := by
        gcongr
        exact sixVertexRootDensityWeight_lower hc y
      _ = |sixVertexRootDensityWeight c y * (rhoN y - rho y)| := by
        rw [abs_mul, abs_of_pos (sixVertexRootDensityWeight_pos hc y)]
      _ ≤ sixVertexCanonicalDensityPerronGauge hc k := by
        simpa only [sixVertexCanonicalDensityPerronGauge, rhoN, rho,
          sixVertexFourierPhysicalDensityMap] using hpoint
      _ < rhoLower * wmin / 2 := hk
  have hdiff : |rhoN y - rho y| < rhoLower / 2 := by
    have hweighted' : wmin * |rhoN y - rho y| <
        wmin * (rhoLower / 2) := by
      convert hweighted using 1 <;> ring
    exact lt_of_mul_lt_mul_left hweighted' hwmin.le
  have hrho : rhoLower ≤ rho y := hrho c le_rfl y
  dsimp [lower]
  rw [hxy]
  linarith [neg_abs_le (rhoN y - rho y)]

def sixVertexCanonicalDensityPerronPositiveHalfRoots
    {c : Real} (hc : 2 < c) (k : Nat) : Fin (k + 1) → Real :=
  sixVertexEvenPositiveHalfProjection (k + 1)
    (sixVertexCanonicalDensityPerronBetheRoots hc k)

def sixVertexCanonicalDensityPerronPositiveHalfRootFamily
    {c : Real} (hc : 2 < c) : SixVertexSymmetricHalfFilledRoots :=
  fun k => sixVertexCanonicalDensityPerronPositiveHalfRoots hc k

theorem eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexLambdaAlongFour c 0 k =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k) := by
  filter_upwards
    [eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc]
      with k hk
  have hopen := hk.1.1
  have hpositive : ∀ j,
      sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j ∈
        Set.Ioo 0 Real.pi := by
    intro j
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    unfold sixVertexCanonicalDensityPerronPositiveHalfRoots
    rw [sixVertexEvenSymmetricLift_projection (k + 1) hopen.2.1]
    exact hopen
  have hkernel := sixVertexSymmetricBetheEigenvalueKernel_eq_value c
    (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k) hpositive
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  unfold SixVertexHalfFilledPerronGaugeWitness
    SixVertexHalfFilledPerronBranchWitness at hk
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero, hhalf] using hk.1.2.2.symm.trans hkernel


def sixVertexCanonicalDensityPerronEmpiricalObservable
    {c : Real} (hc : 2 < c) (f : Real → Real) (k : Nat) : Real :=
  (∑ j, f (sixVertexCanonicalDensityPerronBetheRoots hc k j)) /
    (sixVertexFourWidth 0 k : Real)

theorem abs_sixVertexCanonicalDensityIntegral_sub_fourier_le
    {c : Real} (hc : 2 < c) {f : Real → Real} {B : Real}
    (hf : Continuous f) (hB : 0 ≤ B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B)
    (k : Nat) :
    |(∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1))
            (sixVertexCanonicalDensityPerronBetheRoots hc k) y) -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFourierPhysicalDensity c hc y| ≤
      B * (sixVertexCanonicalDensityPerronGauge hc k /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) * (2 * Real.pi) := by
  let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1))
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
  let rho := sixVertexFourierPhysicalDensity c hc
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let gauge := sixVertexCanonicalDensityPerronGauge hc k
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hrhoN : Continuous rhoN :=
    continuous_sixVertexFiniteRootDensity hc _ _ _
  have hrho : Continuous rho := continuous_sixVertexFourierPhysicalDensity hc
  have hIN : IntervalIntegrable (fun y => f y * rhoN y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hf.mul hrhoN).intervalIntegrable _ _
  have hI : IntervalIntegrable (fun y => f y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hf.mul hrho).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hIN hI]
  have hnorm :
      ‖∫ y in -Real.pi..Real.pi,
          (f y * rhoN y - f y * rho y)‖ ≤
        (B * (gauge / wmin)) * |Real.pi - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hy
      exact ⟨hy.1.le, hy.2⟩
    have hpoint := abs_weightedFiniteDensity_sub_le_gauge hc
      (N := sixVertexFourWidth 0 k)
      (sixVertexCanonicalDensityPerronBetheRoots hc k)
      (sixVertexFourierPhysicalDensityMap hc) y hyIcc
    have hdiff : |rhoN y - rho y| ≤ gauge / wmin := by
      rw [le_div_iff₀ hwmin]
      calc
        |rhoN y - rho y| * wmin ≤
            |rhoN y - rho y| * sixVertexRootDensityWeight c y := by
          gcongr
          exact sixVertexRootDensityWeight_lower hc y
        _ = |sixVertexRootDensityWeight c y * (rhoN y - rho y)| := by
          rw [abs_mul, abs_of_pos (sixVertexRootDensityWeight_pos hc y)]
          ring
        _ ≤ gauge := by
          simpa only [rhoN, rho, gauge,
            sixVertexCanonicalDensityPerronGauge,
            sixVertexFourierPhysicalDensityMap] using hpoint
    calc
      ‖f y * rhoN y - f y * rho y‖ =
          |f y| * |rhoN y - rho y| := by
        rw [show f y * rhoN y - f y * rho y =
          f y * (rhoN y - rho y) by ring]
        simp only [Real.norm_eq_abs, abs_mul]
      _ ≤ B * (gauge / wmin) :=
        mul_le_mul (hfBound y hyIcc) hdiff (abs_nonneg _)
          hB
  rw [Real.norm_eq_abs] at hnorm
  rw [abs_of_pos (by nlinarith [Real.pi_pos] :
    0 < Real.pi - -Real.pi)] at hnorm
  dsimp only [rhoN, rho, gauge, wmin] at hnorm
  convert hnorm using 1 <;> ring



theorem tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable
    {c : Real} (hc : 2 < c)
    {f : Real → Real} {C : NNReal} {B : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi))
    (hB : 0 ≤ B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B) :
    Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc f)
      atTop (nhds (∫ y in -Real.pi..Real.pi,
        f y * sixVertexFourierPhysicalDensity c hc y)) := by
  obtain ⟨lower, hlower, hdensity⟩ :=
    eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  let qerr : Nat → Real := fun k =>
    (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      (1 / ((sixVertexFourWidth 0 k : Real) * lower)) * (2 * Real.pi)
  let derr : Nat → Real := fun k =>
    B * (sixVertexCanonicalDensityPerronGauge hc k / wmin) * (2 * Real.pi)
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  let Q := (C : Real) * sixVertexFiniteRootDensityUniformBound c *
    (1 / lower) * (2 * Real.pi)
  have hqerr : Tendsto qerr atTop (nhds 0) := by
    have h := hwidthReal.const_div_atTop Q
    convert h using 1
    funext k
    dsimp [qerr, Q]
    field_simp [hlower.ne']
  have hderr : Tendsto derr atTop (nhds 0) := by
    have h := (((tendsto_sixVertexCanonicalDensityPerronGauge hc).div_const
      wmin).const_mul B).mul_const (2 * Real.pi)
    simpa only [derr, zero_div, zero_mul, mul_zero] using h
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  apply squeeze_zero'
  · filter_upwards [] with k
    exact norm_nonneg _
  · filter_upwards [hdensity] with k hkDensity
    let p := sixVertexCanonicalDensityPerronBetheRoots hc k
    let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) p
    let I := ∫ y in -Real.pi..Real.pi, f y * rhoN y
    let target := ∫ y in -Real.pi..Real.pi,
      f y * sixVertexFourierPhysicalDensity c hc y
    have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
    have hn : 0 < (k + 1) + (k + 1) := by omega
    have hhalf : sixVertexFourWidth 0 k =
        2 * ((k + 1) + (k + 1)) := by
      unfold sixVertexFourWidth
      omega
    have hquad :=
      abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower
        hc hN hn hhalf (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
        (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k)
        hlower hkDensity hf hlip hperiodic
    have hint := abs_sixVertexCanonicalDensityIntegral_sub_fourier_le
      hc hf hB hfBound k
    change |sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - I| ≤
      qerr k at hquad
    change |I - target| ≤ derr k at hint
    change ‖sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - target‖ ≤
      qerr k + derr k
    rw [Real.norm_eq_abs]
    exact (abs_sub_le
      (sixVertexCanonicalDensityPerronEmpiricalObservable hc f k)
      I target).trans (add_le_add hquad hint)
  · simpa only [zero_add] using hqerr.add hderr

end

end StatMech.FrontierD
