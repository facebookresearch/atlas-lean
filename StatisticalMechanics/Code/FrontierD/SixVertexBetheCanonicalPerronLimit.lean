/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronTruncation
import Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction











open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronLogEpsilon
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  (1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 4

def sixVertexCanonicalPerronLogCutoff
    {c : Real} (hc : 2 < c) (k : Nat) : Nat :=
  (k + 1) / sixVertexPerronGaugeStage hc k + 1

def sixVertexCanonicalPerronRegularizedIntegral
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  ∫ y in -Real.pi..Real.pi,
    sixVertexRegularizedBetheLogKernel c
        (sixVertexCanonicalPerronLogEpsilon hc k) y *
      sixVertexFourierPhysicalDensity c hc y

theorem eventually_two_le_sixVertexPerronGaugeStage
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop, 2 ≤ sixVertexPerronGaugeStage hc k :=
  (tendsto_sixVertexPerronGaugeStage hc).eventually
    (eventually_ge_atTop 2)

theorem tendsto_sixVertexCanonicalPerronLogEpsilon
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalPerronLogEpsilon hc) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hinv : Tendsto (fun k =>
      (1 : Real) / sixVertexPerronGaugeStage hc k) atTop (nhds 0) :=
    hstageReal.const_div_atTop 1
  apply squeeze_zero' (g := fun k =>
    (1 : Real) / sixVertexPerronGaugeStage hc k)
  · filter_upwards [] with k
    exact div_nonneg zero_le_one
      (pow_nonneg (Nat.cast_nonneg _) 4)
  · filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc]
      with k hk
    let s : Real := sixVertexPerronGaugeStage hc k
    have hs : 1 ≤ s := by
      dsimp [s]
      exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
    have hpow : s ≤ s ^ 4 := by
      simpa using pow_le_pow_right₀ hs (show 1 ≤ 4 by omega)
    exact one_div_le_one_div_of_le (by positivity) hpow
  · exact hinv

theorem eventually_sixVertexCanonicalPerronLogEpsilon_pos
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop, 0 < sixVertexCanonicalPerronLogEpsilon hc k := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc] with k hk
  unfold sixVertexCanonicalPerronLogEpsilon
  positivity

theorem sixVertexCanonicalPerronLogCutoff_pos
    {c : Real} (hc : 2 < c) (k : Nat) :
    0 < sixVertexCanonicalPerronLogCutoff hc k := by
  unfold sixVertexCanonicalPerronLogCutoff
  exact Nat.zero_lt_succ _

theorem eventually_sixVertexCanonicalPerronLogCutoff_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalPerronLogCutoff hc k ≤ k + 1 := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc] with k hk
  unfold sixVertexCanonicalPerronLogCutoff
  have hm : 0 < k + 1 := by omega
  have hlt := Nat.div_lt_self hm (by omega : 1 < sixVertexPerronGaugeStage hc k)
  omega

theorem tendsto_sixVertexCanonicalPerronLogCutoff_div_width
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      (sixVertexCanonicalPerronLogCutoff hc k : Real) /
        (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
  let s : Nat → Real := fun k => sixVertexPerronGaugeStage hc k
  let m : Nat → Real := fun k => k + 1
  have hs : Tendsto s atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hm : Tendsto m atTop atTop :=
    by
      simpa [m, Function.comp_def] using
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsInv : Tendsto (fun k => (1 / 4 : Real) / s k)
      atTop (nhds 0) := hs.const_div_atTop (1 / 4)
  have hmInv : Tendsto (fun k => (1 / 4 : Real) / m k)
      atTop (nhds 0) := hm.const_div_atTop (1 / 4)
  have hupper : Tendsto (fun k =>
      (1 / 4 : Real) / s k + (1 / 4 : Real) / m k)
      atTop (nhds 0) := by simpa using hsInv.add hmInv
  apply squeeze_zero' (g := fun k =>
    (1 / 4 : Real) / s k + (1 / 4 : Real) / m k)
  · filter_upwards [] with k
    positivity
  · filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc]
      with k hk
    have hspos : (0 : Real) < s k := by
      dsimp [s]
      exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
    have hmpos : (0 : Real) < m k := by dsimp [m]; positivity
    have hcast :
        (sixVertexCanonicalPerronLogCutoff hc k : Real) ≤
          m k / s k + 1 := by
      dsimp [m, s]
      unfold sixVertexCanonicalPerronLogCutoff
      push_cast
      exact add_le_add
        (by simpa using
          (Nat.cast_div_le (m := k + 1)
            (n := sixVertexPerronGaugeStage hc k) (α := Real))) le_rfl
    rw [sixVertexFourWidth]
    push_cast
    simp only [zero_add]
    calc
      (sixVertexCanonicalPerronLogCutoff hc k : Real) / (4 * m k) ≤
          (m k / s k + 1) / (4 * m k) :=
        div_le_div_of_nonneg_right hcast (by positivity)
      _ = (1 / 4 : Real) / s k + (1 / 4 : Real) / m k := by
        field_simp [hspos.ne', hmpos.ne']
  · exact hupper

theorem tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronInitialLogContribution hc
        (sixVertexCanonicalPerronLogCutoff hc k) k)
      atTop (nhds 0) := by
  exact
    sixVertexCanonicalDensityPerronInitialLogContribution_tendsto_zero_of_sublinear
      hc
      (sixVertexCanonicalPerronLogCutoff hc)
      (Filter.Eventually.of_forall
        (sixVertexCanonicalPerronLogCutoff_pos hc))
      (eventually_sixVertexCanonicalPerronLogCutoff_le hc)
      (tendsto_sixVertexCanonicalPerronLogCutoff_div_width hc)

theorem tendsto_sixVertexCanonicalPerronRegularizedTailBound
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalPerronLogEpsilon hc k *
          (sixVertexFourWidth 0 k : Real) /
        (4 * (sixVertexCanonicalPerronLogCutoff hc k : Real)))
      atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hinv : Tendsto (fun k =>
      (1 : Real) / sixVertexPerronGaugeStage hc k) atTop (nhds 0) :=
    hstageReal.const_div_atTop 1
  apply squeeze_zero' (g := fun k =>
    (1 : Real) / sixVertexPerronGaugeStage hc k)
  · filter_upwards [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc]
      with k hk
    positivity
  · filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc]
      with k hk
    have hsNat : 0 < sixVertexPerronGaugeStage hc k := by omega
    have hs : (0 : Real) < sixVertexPerronGaugeStage hc k := by
      exact_mod_cast hsNat
    have hJ := sixVertexCanonicalPerronLogCutoff_pos hc k
    have hmulNat : k + 1 ≤ sixVertexPerronGaugeStage hc k *
        sixVertexCanonicalPerronLogCutoff hc k := by
      simpa [sixVertexCanonicalPerronLogCutoff] using
        (Nat.lt_mul_div_succ (k + 1) hsNat).le
    have hmul : ((k + 1 : Nat) : Real) ≤
        (sixVertexPerronGaugeStage hc k : Real) *
          (sixVertexCanonicalPerronLogCutoff hc k : Real) := by
      exact_mod_cast hmulNat
    have hsone : (1 : Real) ≤ sixVertexPerronGaugeStage hc k := by
      exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
    have hpow : (sixVertexPerronGaugeStage hc k : Real) ≤
        (sixVertexPerronGaugeStage hc k : Real) ^ 3 := by
      simpa using pow_le_pow_right₀ hsone (show 1 ≤ 3 by omega)
    have hmul3 : ((k : Real) + 1) ≤
        (sixVertexPerronGaugeStage hc k : Real) ^ 3 *
          (sixVertexCanonicalPerronLogCutoff hc k : Real) := by
      have hJnonneg : (0 : Real) ≤
          sixVertexCanonicalPerronLogCutoff hc k := by positivity
      have hscale := mul_le_mul_of_nonneg_right hpow hJnonneg
      norm_num at hmul ⊢
      exact hmul.trans hscale
    unfold sixVertexCanonicalPerronLogEpsilon
    rw [sixVertexFourWidth]
    push_cast
    simp only [zero_add, Nat.cast_add, Nat.cast_one]
    change ((1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 4) *
        (4 * ((k : Real) + 1)) /
        (4 * (sixVertexCanonicalPerronLogCutoff hc k : Real)) ≤
          1 / (sixVertexPerronGaugeStage hc k : Real)
    field_simp [hs.ne', (show
      (sixVertexCanonicalPerronLogCutoff hc k : Real) ≠ 0 by
        exact_mod_cast hJ.ne')]
    exact hmul3
  · exact hinv



theorem tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c
            (sixVertexCanonicalPerronLogEpsilon hc k)) k)
      atTop (nhds 0) := by
  let margin : Real := (c ^ 2 - 2) ^ 2 - 4
  have hmargin : 0 < margin := by
    dsimp [margin]
    have hc2 : 2 < c ^ 2 - 2 := by nlinarith [sq_nonneg (c - 2)]
    nlinarith
  have hepsUpper : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalPerronLogEpsilon hc k ≤ margin :=
    (tendsto_sixVertexCanonicalPerronLogEpsilon hc).eventually
      (Iic_mem_nhds hmargin)
  have hupper :=
    (tendsto_sixVertexCanonicalPerronInitialLogContribution_schedule hc).add
      (tendsto_sixVertexCanonicalPerronRegularizedTailBound hc)
  apply squeeze_zero'
  · filter_upwards
      [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc, hepsUpper]
      with k heps hepsLe
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc heps hepsLe
      (sixVertexCanonicalPerronLogCutoff_pos hc k) k).1
  · filter_upwards
      [eventually_sixVertexCanonicalPerronLogEpsilon_pos hc, hepsUpper]
      with k heps hepsLe
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc heps hepsLe
      (sixVertexCanonicalPerronLogCutoff_pos hc k) k).2
  · simpa using hupper

def sixVertexCanonicalPerronRegularizedBound
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  let epsilon := sixVertexCanonicalPerronLogEpsilon hc k
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  let C := sixVertexRegularizedBetheLogLipschitzConstant c epsilon
  |f 0| + (C : Real) * Real.pi



theorem abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le
    {c : Real} (hc : 2 < c) {lower : Real} (hlower : 0 < lower)
    {k : Nat}
    (hdensity : ∀ x : Real,
      lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc k) x)
    (hepsilon : 0 < sixVertexCanonicalPerronLogEpsilon hc k) :
    |sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c
            (sixVertexCanonicalPerronLogEpsilon hc k)) k -
        sixVertexCanonicalPerronRegularizedIntegral hc k| ≤
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) *
        sixVertexFiniteRootDensityUniformBound c *
        (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
        (2 * Real.pi) +
      sixVertexCanonicalPerronRegularizedBound hc k *
        (sixVertexCanonicalDensityPerronGauge hc k /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi) := by
  let epsilon := sixVertexCanonicalPerronLogEpsilon hc k
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  let C := sixVertexRegularizedBetheLogLipschitzConstant c epsilon
  let B := sixVertexCanonicalPerronRegularizedBound hc k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc k
  let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1)) p
  let I := ∫ y in -Real.pi..Real.pi, f y * rhoN y
  let target := sixVertexCanonicalPerronRegularizedIntegral hc k
  have hC : LipschitzWith C f := by
    exact lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon
  have hf : Continuous f := hC.continuous
  have hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B := by
    intro x hx
    have hdist : |f x - f 0| ≤ (C : Real) * |x| := by
      simpa only [Real.norm_eq_abs, sub_zero] using hC.norm_sub_le x 0
    have hxabs : |x| ≤ Real.pi := abs_le.mpr hx
    calc
      |f x| = |(f x - f 0) + f 0| := by ring_nf
      _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
      _ ≤ (C : Real) * |x| + |f 0| := by linarith
      _ ≤ (C : Real) * Real.pi + |f 0| := by gcongr
      _ = B := by
        dsimp [B, sixVertexCanonicalPerronRegularizedBound, f, C, epsilon]
        ring
  have hB : 0 ≤ B := by
    dsimp [B, sixVertexCanonicalPerronRegularizedBound]
    positivity
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
      hlower hdensity hf hC
      (periodic_sixVertexRegularizedBetheLogKernel c epsilon)
  have hint := abs_sixVertexCanonicalDensityIntegral_sub_fourier_le
    hc hf hB hbound k
  change |sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - I| ≤
    (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
        (2 * Real.pi) at hquad
  change |I - target| ≤ B *
    (sixVertexCanonicalDensityPerronGauge hc k /
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c)) * (2 * Real.pi) at hint
  change |sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - target| ≤ _
  exact (abs_sub_le
    (sixVertexCanonicalDensityPerronEmpiricalObservable hc f k)
    I target).trans (add_le_add hquad hint)

def sixVertexCanonicalPerronLipschitzBase (c : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2

theorem sixVertexCanonicalPerronLipschitzBase_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexCanonicalPerronLipschitzBase c := by
  unfold sixVertexCanonicalPerronLipschitzBase
  exact div_nonneg (by nlinarith [sq_nonneg c]) (sq_nonneg _)

theorem coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule
    {c : Real} (hc : 2 < c) {k : Nat}
    (hstage : 0 < sixVertexPerronGaugeStage hc k) :
    (sixVertexRegularizedBetheLogLipschitzConstant c
        (sixVertexCanonicalPerronLogEpsilon hc k) : Real) =
      sixVertexCanonicalPerronLipschitzBase c +
        (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
  let s : Real := sixVertexPerronGaugeStage hc k
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast hstage
  let A : Real := (1 / 2 : Real) *
    ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2 +
      2 / sixVertexCanonicalPerronLogEpsilon hc k)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hc1 : 0 ≤ 2 * (c ^ 2 - 1) := by nlinarith [sq_nonneg c]
    have heps : 0 < sixVertexCanonicalPerronLogEpsilon hc k := by
      unfold sixVertexCanonicalPerronLogEpsilon
      positivity
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hc1 (sq_nonneg _))
        (div_nonneg (by norm_num) heps.le))
  rw [sixVertexRegularizedBetheLogLipschitzConstant,
    Real.coe_toNNReal _ hA]
  change A = _
  dsimp [A, sixVertexCanonicalPerronLipschitzBase,
    sixVertexCanonicalPerronLogEpsilon, s]
  field_simp [hs.ne']

theorem abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule
    {c : Real} (hc : 2 < c) {k : Nat}
    (hstage : 2 ≤ sixVertexPerronGaugeStage hc k) :
    |sixVertexRegularizedBetheLogKernel c
        (sixVertexCanonicalPerronLogEpsilon hc k) 0| ≤
      (1 / 2 : Real) * |Real.log (c ^ 4)| +
        2 * (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
  let s : Real := sixVertexPerronGaugeStage hc k
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
  have hlogsNonneg : 0 ≤ Real.log s := Real.log_nonneg hsone
  have hlogsLe : Real.log s ≤ s := by
    have h := Real.log_le_sub_one_of_pos hs
    linarith
  have hsPow : s ≤ s ^ 4 := by
    simpa using pow_le_pow_right₀ hsone (show 1 ≤ 4 by omega)
  have hepsLog :
      |Real.log (sixVertexCanonicalPerronLogEpsilon hc k)| ≤
        4 * s ^ 4 := by
    have hsne : s ≠ 0 := hs.ne'
    unfold sixVertexCanonicalPerronLogEpsilon
    change |Real.log ((1 : Real) / s ^ 4)| ≤ 4 * s ^ 4
    rw [Real.log_div one_ne_zero (pow_ne_zero 4 hsne), Real.log_one,
      zero_sub, abs_neg, Real.log_pow]
    rw [abs_mul, abs_of_nonneg hlogsNonneg]
    norm_num
    nlinarith
  have hnum : sixVertexBetheLogNumerator c 0 = c ^ 4 := by
    unfold sixVertexBetheLogNumerator
    rw [Real.cos_zero]
    ring
  have hden : sixVertexBetheLogDenominator 0 = 0 := by
    simp [sixVertexBetheLogDenominator]
  unfold sixVertexRegularizedBetheLogKernel
  rw [hnum, hden, zero_add]
  calc
    |(1 / 2 : Real) *
        (Real.log (c ^ 4) -
          Real.log (sixVertexCanonicalPerronLogEpsilon hc k))| =
        (1 / 2 : Real) *
          |Real.log (c ^ 4) -
            Real.log (sixVertexCanonicalPerronLogEpsilon hc k)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
    _ ≤ (1 / 2 : Real) *
        (|Real.log (c ^ 4)| +
          |Real.log (sixVertexCanonicalPerronLogEpsilon hc k)|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ (1 / 2 : Real) *
        (|Real.log (c ^ 4)| + 4 * s ^ 4) := by gcongr
    _ = (1 / 2 : Real) * |Real.log (c ^ 4)| + 2 *
        (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
      dsimp [s]
      ring

theorem eventually_sixVertexCanonicalPerronLipschitz_div_width_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) /
          (sixVertexFourWidth 0 k : Real) ≤
        (sixVertexCanonicalPerronLipschitzBase c + 1) /
          (sixVertexPerronGaugeStage hc k : Real) := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc] with k hk
  let s : Real := sixVertexPerronGaugeStage hc k
  let m : Real := k + 1
  let base := sixVertexCanonicalPerronLipschitzBase c
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
  have hm : s ^ 8 ≤ m := by
    dsimp [s, m]
    exact_mod_cast sixVertexPerronGaugeStage_pow_eight_le hc k
  have hbase : 0 ≤ base :=
    sixVertexCanonicalPerronLipschitzBase_nonneg hc
  have hs8 : s ≤ s ^ 8 := by
    simpa using pow_le_pow_right₀ hsone (show 1 ≤ 8 by omega)
  have hs5 : s ^ 5 ≤ s ^ 8 :=
    pow_le_pow_right₀ hsone (show 5 ≤ 8 by omega)
  have hbaseScale : base * s ≤ base * s ^ 8 :=
    mul_le_mul_of_nonneg_left hs8 hbase
  have hnum : (base + s ^ 4) * s ≤ (base + 1) * m := by
    calc
      (base + s ^ 4) * s = base * s + s ^ 5 := by ring
      _ ≤ base * s ^ 8 + s ^ 8 := add_le_add hbaseScale hs5
      _ = (base + 1) * s ^ 8 := by ring
      _ ≤ (base + 1) * m :=
        mul_le_mul_of_nonneg_left hm (by positivity)
  rw [coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule hc
    (show 0 < sixVertexPerronGaugeStage hc k by omega)]
  rw [sixVertexFourWidth]
  push_cast
  simp only [zero_add]
  change (base + s ^ 4) / (4 * m) ≤ (base + 1) / s
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith [mul_nonneg (show 0 ≤ base + 1 by positivity)
    (show 0 ≤ m by positivity)]

theorem tendsto_sixVertexCanonicalPerronLipschitz_div_width
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) /
        (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hupper := hstageReal.const_div_atTop
    (sixVertexCanonicalPerronLipschitzBase c + 1)
  apply squeeze_zero'
  · filter_upwards [] with k
    exact div_nonneg (NNReal.coe_nonneg _)
      (Nat.cast_nonneg _)
  · exact eventually_sixVertexCanonicalPerronLipschitz_div_width_le hc
  · exact hupper

theorem tendsto_sixVertexCanonicalPerronQuadratureError
    {c : Real} (hc : 2 < c) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun k =>
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) *
        sixVertexFiniteRootDensityUniformBound c *
        (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
        (2 * Real.pi)) atTop (nhds 0) := by
  have hcore :=
    (tendsto_sixVertexCanonicalPerronLipschitz_div_width hc).const_mul
      (sixVertexFiniteRootDensityUniformBound c / lower * (2 * Real.pi))
  convert hcore using 1
  · funext k
    field_simp [hlower.ne']
  · norm_num

def sixVertexCanonicalPerronDensityBoundConstant
    (c : Real) : Real :=
  (1 / 2 : Real) * |Real.log (c ^ 4)| +
    sixVertexCanonicalPerronLipschitzBase c * Real.pi +
      (2 + Real.pi)

theorem sixVertexCanonicalPerronDensityBoundConstant_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexCanonicalPerronDensityBoundConstant c := by
  unfold sixVertexCanonicalPerronDensityBoundConstant
  have hbase := sixVertexCanonicalPerronLipschitzBase_nonneg hc
  positivity

theorem eventually_sixVertexCanonicalPerronBound_mul_gauge_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalPerronRegularizedBound hc k *
          sixVertexCanonicalDensityPerronGauge hc k ≤
        sixVertexCanonicalPerronDensityBoundConstant c /
          (sixVertexPerronGaugeStage hc k : Real) := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc,
    eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow hc]
      with k hk hGauge
  let s : Real := sixVertexPerronGaugeStage hc k
  let base := sixVertexCanonicalPerronLipschitzBase c
  let D : Real := (1 / 2 : Real) * |Real.log (c ^ 4)| +
    base * Real.pi
  let A : Real := 2 + Real.pi
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
  have hbase : 0 ≤ base :=
    sixVertexCanonicalPerronLipschitzBase_nonneg hc
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs8 : s ≤ s ^ 8 := by
    simpa using pow_le_pow_right₀ hsone (show 1 ≤ 8 by omega)
  have hs5 : s ^ 5 ≤ s ^ 8 :=
    pow_le_pow_right₀ hsone (show 5 ≤ 8 by omega)
  have hB : sixVertexCanonicalPerronRegularizedBound hc k ≤
      D + A * s ^ 4 := by
    dsimp only [sixVertexCanonicalPerronRegularizedBound]
    rw [coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule hc
      (show 0 < sixVertexPerronGaugeStage hc k by omega)]
    have hzero :=
      abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule hc hk
    dsimp [s, base, D, A] at hzero ⊢
    nlinarith [mul_nonneg
      (sixVertexCanonicalPerronLipschitzBase_nonneg hc) Real.pi_pos.le]
  have hGaugeNonneg : 0 ≤ sixVertexCanonicalDensityPerronGauge hc k :=
    norm_nonneg _
  have hfirst :
      sixVertexCanonicalPerronRegularizedBound hc k *
          sixVertexCanonicalDensityPerronGauge hc k ≤
        (D + A * s ^ 4) * (1 / s ^ 8) := by
    calc
      _ ≤ (D + A * s ^ 4) *
          sixVertexCanonicalDensityPerronGauge hc k :=
        mul_le_mul_of_nonneg_right hB hGaugeNonneg
      _ ≤ (D + A * s ^ 4) * (1 / s ^ 8) := by
        gcongr
  have hsecond : (D + A * s ^ 4) * (1 / s ^ 8) ≤
      (D + A) / s := by
    rw [div_eq_mul_inv]
    field_simp [hs.ne']
    have hone7 : (1 : Real) ≤ s ^ 7 := by
      simpa using pow_le_pow_right₀ hsone (show 0 ≤ 7 by omega)
    have hs47 : s ^ 4 ≤ s ^ 7 :=
      pow_le_pow_right₀ hsone (show 4 ≤ 7 by omega)
    have hDscale : D ≤ D * s ^ 7 := by
      nlinarith [mul_le_mul_of_nonneg_left hone7 hD]
    have hAscale : A * s ^ 4 ≤ A * s ^ 7 :=
      mul_le_mul_of_nonneg_left hs47 hA
    calc
      D + A * s ^ 4 ≤ D * s ^ 7 + A * s ^ 7 :=
        add_le_add hDscale hAscale
      _ = s ^ 7 * (D + A) := by ring
  exact hfirst.trans (by
    simpa [sixVertexCanonicalPerronDensityBoundConstant, D, A, base]
      using hsecond)

theorem tendsto_sixVertexCanonicalPerronBound_mul_gauge
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexCanonicalPerronRegularizedBound hc k *
      sixVertexCanonicalDensityPerronGauge hc k) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hupper := hstageReal.const_div_atTop
    (sixVertexCanonicalPerronDensityBoundConstant c)
  apply squeeze_zero'
  · filter_upwards [] with k
    exact mul_nonneg (by
      unfold sixVertexCanonicalPerronRegularizedBound
      positivity) (norm_nonneg _)
  · exact eventually_sixVertexCanonicalPerronBound_mul_gauge_le hc
  · exact hupper

theorem tendsto_sixVertexCanonicalPerronDensityError
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalPerronRegularizedBound hc k *
        (sixVertexCanonicalDensityPerronGauge hc k /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi))
      atTop (nhds 0) := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have h := ((tendsto_sixVertexCanonicalPerronBound_mul_gauge hc).div_const
    wmin).mul_const (2 * Real.pi)
  convert h using 1
  · funext k
    dsimp [wmin]
    ring
  · norm_num

theorem tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c
            (sixVertexCanonicalPerronLogEpsilon hc k)) k -
        sixVertexCanonicalPerronRegularizedIntegral hc k)
      atTop (nhds 0) := by
  obtain ⟨lower, hlower, hdensity⟩ :=
    eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc
  let qerr : Nat → Real := fun k =>
    (sixVertexRegularizedBetheLogLipschitzConstant c
        (sixVertexCanonicalPerronLogEpsilon hc k) : Real) *
      sixVertexFiniteRootDensityUniformBound c *
      (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
      (2 * Real.pi)
  let derr : Nat → Real := fun k =>
    sixVertexCanonicalPerronRegularizedBound hc k *
      (sixVertexCanonicalDensityPerronGauge hc k /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) * (2 * Real.pi)
  have hq : Tendsto qerr atTop (nhds 0) := by
    exact tendsto_sixVertexCanonicalPerronQuadratureError hc hlower
  have hd : Tendsto derr atTop (nhds 0) := by
    exact tendsto_sixVertexCanonicalPerronDensityError hc
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero' (g := fun k => qerr k + derr k)
  · filter_upwards [] with k
    exact abs_nonneg _
  · filter_upwards [hdensity,
      eventually_sixVertexCanonicalPerronLogEpsilon_pos hc]
      with k hkDensity hkEpsilon
    exact abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le
      hc hlower hkDensity hkEpsilon
  · simpa using hq.add hd



theorem tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalPerronRegularizedIntegral hc k)
      atTop (nhds 0) := by
  have hroot :=
    tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized hc
  have hemp :=
    tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral hc
  convert hroot.add hemp using 1
  · funext k
    ring
  · norm_num

end

end StatMech.FrontierD
