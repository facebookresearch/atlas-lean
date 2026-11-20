/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheGaugeUniform









open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem sixVertexRootDensityScale_bounds
    {c : Real} (hc : 2 < c) :
    sixVertexAnisotropyMagnitude c - 1 ≤ sixVertexRootDensityScale c ∧
      sixVertexRootDensityScale c ≤ sixVertexAnisotropyMagnitude c := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hs_sq : s ^ 2 = d ^ 2 - 1 := by
    dsimp [s, sixVertexRootDensityScale]
    rw [Real.sq_sqrt]
    nlinarith
  constructor <;> nlinarith


theorem abs_sixVertexRootDensityKernel_sub_one_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexRootDensityKernel c x y - 1| ≤
      1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2 := by
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let q := d - 1
  let Fx := sixVertexBetheIntegratingFactor c x
  let Fy := sixVertexBetheIntegratingFactor c y
  let A := 4 * Fx * Fy
  let B := 2 * (1 - Real.cos (x - y))
  let D := A + B
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hq : 0 < q := by dsimp [q]; linarith
  have hFx : 0 < Fx := sixVertexBetheIntegratingFactor_pos hc x
  have hFy : 0 < Fy := sixVertexBetheIntegratingFactor_pos hc y
  have hA : 0 < A := by dsimp [A]; positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    linarith [Real.cos_le_one (x - y)]
  have hB4 : B ≤ 4 := by
    dsimp [B]
    linarith [Real.neg_one_le_cos (x - y)]
  have hD : 0 < D := add_pos_of_pos_of_nonneg hA hB0
  have hFxLower : q ≤ Fx := by
    dsimp [q, d, Fx]
    exact sixVertexBetheIntegratingFactor_bounds hc x |>.1
  have hFyLower : q ≤ Fy := by
    dsimp [q, d, Fy]
    exact sixVertexBetheIntegratingFactor_bounds hc y |>.1
  have hAq : 4 * q ^ 2 ≤ A := by
    have hprod : q ^ 2 ≤ Fx * Fy := by
      nlinarith [mul_le_mul hFxLower hFyLower hq.le hFx.le]
    dsimp [A]
    nlinarith
  have hsBounds := sixVertexRootDensityScale_bounds hc
  have hqs : q ≤ s := by
    dsimp [q, d, s]
    exact hsBounds.1
  have hsd : s ≤ d := by
    dsimp [d, s]
    exact hsBounds.2
  have hs_sq : s ^ 2 = d ^ 2 - 1 := by
    dsimp [s, sixVertexRootDensityScale]
    rw [Real.sq_sqrt]
    nlinarith
  have hds : (d - s) * (d + s) = 1 := by nlinarith
  have hds0 : 0 ≤ d - s := sub_nonneg.mpr hsd
  have hqsum : q ≤ d + s := by
    dsimp [q]
    nlinarith
  have hqprod : q ^ 2 ≤ s * (d + s) := by
    nlinarith [mul_le_mul hqs hqsum hq.le hs.le]
  have hratio : d / s ≤ 1 + 1 / q ^ 2 := by
    have hscaled : (d - s) * q ^ 2 ≤ s := by
      calc
        (d - s) * q ^ 2 ≤ (d - s) * (s * (d + s)) :=
          mul_le_mul_of_nonneg_left hqprod hds0
        _ = s := by rw [show (d - s) * (s * (d + s)) =
            s * ((d - s) * (d + s)) by ring, hds, mul_one]
    have hsmall : (d - s) / s ≤ 1 / q ^ 2 := by
      rw [div_le_div_iff₀ hs (sq_pos_of_pos hq)]
      simpa [mul_comm] using hscaled
    calc
      d / s = 1 + (d - s) / s := by field_simp; ring
      _ ≤ 1 + 1 / q ^ 2 := by linarith
  have hBdiv : B / D ≤ 1 / q ^ 2 := by
    rw [div_le_div_iff₀ hD (sq_pos_of_pos hq)]
    have hBq : B * q ^ 2 ≤ 4 * q ^ 2 :=
      mul_le_mul_of_nonneg_right hB4 (sq_nonneg q)
    nlinarith [hBq, hAq]
  have hAD : A / D = 1 - B / D := by
    dsimp [D]
    field_simp [hD.ne']
    ring
  have hfrac0 : 0 ≤ A / D := div_nonneg hA.le hD.le
  have hfrac1 : A / D ≤ 1 := by
    rw [div_le_one hD]
    dsimp [D]
    linarith
  have hdovers : 1 ≤ d / s := by
    rw [le_div_iff₀ hs]
    simpa only [one_mul] using hsd
  have hkernel : sixVertexRootDensityKernel c x y = (d / s) * (A / D) := by
    unfold sixVertexRootDensityKernel
    rw [sixVertexThetaDerivativeDenominator_eq]
    change 4 * d * Fx * Fy /
        (s * (4 * Fx * Fy + 2 * (1 - Real.cos (x - y)))) =
      (d / s) * (A / D)
    rw [show 4 * Fx * Fy + 2 * (1 - Real.cos (x - y)) = D by rfl]
    field_simp [hs.ne', hD.ne']
    dsimp [A]
  have hlower : 1 - 1 / q ^ 2 ≤ sixVertexRootDensityKernel c x y := by
    rw [hkernel]
    calc
      1 - 1 / q ^ 2 ≤ A / D := by rw [hAD]; linarith
      _ ≤ (d / s) * (A / D) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hdovers hfrac0
  have hupper : sixVertexRootDensityKernel c x y ≤ 1 + 1 / q ^ 2 := by
    rw [hkernel]
    calc
      (d / s) * (A / D) ≤ d / s := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hfrac1
            (div_nonneg (zero_le_one.trans hd.le) hs.le)
      _ ≤ 1 + 1 / q ^ 2 := hratio
  rw [abs_le]
  dsimp [q, d] at hlower hupper ⊢
  constructor <;> linarith



theorem sixVertexWeightedFiniteDensityGauge_le_anisotropyError
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : (n : Real) / N = 1 / 2) (p : Fin n → Real)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    (hrhoNonneg : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, 0 ≤ rho y) :
    sixVertexWeightedFiniteDensityGauge hc N n p rho ≤
      (1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) /
        (2 * Real.pi) := by
  let E := 1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2
  have hd := one_lt_sixVertexAnisotropyMagnitude hc
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  apply sixVertexWeightedFiniteDensityGauge_le_of_pointwise hc p rho
    (div_nonneg hE (by positivity))
  intro x hx
  let K : Real → Real := fun y => sixVertexRootDensityKernel c x y
  let e : Real → Real := fun y => K y - 1
  have hKcont : Continuous K :=
    (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous
  have hecont : Continuous e := hKcont.sub continuous_const
  have hrhoInt : IntervalIntegrable rho MeasureTheory.volume
      (-Real.pi) Real.pi := rho.continuous.intervalIntegrable _ _
  have herrInt : IntervalIntegrable (fun y => e y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hecont.mul rho.continuous).intervalIntegrable _ _
  have hErhoInt : IntervalIntegrable (fun y => E * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (continuous_const.mul rho.continuous).intervalIntegrable _ _
  have herrIntegral :
      |∫ y in -Real.pi..Real.pi, e y * rho y| ≤ E / 2 := by
    calc
      |∫ y in -Real.pi..Real.pi, e y * rho y| ≤
          ∫ y in -Real.pi..Real.pi, |e y * rho y| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ y in -Real.pi..Real.pi, E * rho y := by
        apply intervalIntegral.integral_mono_on hab
        · exact (hecont.mul rho.continuous).abs.intervalIntegrable _ _
        · exact hErhoInt
        · intro y hy
          rw [abs_mul, abs_of_nonneg (hrhoNonneg y hy)]
          exact mul_le_mul_of_nonneg_right
            (by simpa only [e, K, E] using
              abs_sixVertexRootDensityKernel_sub_one_le hc x y)
            (hrhoNonneg y hy)
      _ = E / 2 := by
        rw [intervalIntegral.integral_const_mul, hrhoMass]
        ring
  let err : Fin n → Real := fun j => K (p j) - 1
  have herrTerm (j : Fin n) : |err j| ≤ E := by
    simpa only [err, K, E] using
      abs_sixVertexRootDensityKernel_sub_one_le hc x (p j)
  have herrSum : |∑ j, err j| ≤ (n : Real) * E := by
    calc
      |∑ j, err j| ≤ ∑ j, |err j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, E := Finset.sum_le_sum fun j _ => herrTerm j
      _ = (n : Real) * E := by simp
  have herrSumScaled : |(∑ j, err j) / (N : Real)| ≤ E / 2 := by
    rw [abs_div, abs_of_pos hNreal]
    calc
      |∑ j, err j| / (N : Real) ≤ ((n : Real) * E) / N :=
        div_le_div_of_nonneg_right herrSum hNreal.le
      _ = ((n : Real) / N) * E := by ring
      _ = E / 2 := by rw [hhalf]; ring
  have hsum : (∑ j, K (p j)) = (n : Real) + ∑ j, err j := by
    calc
      (∑ j, K (p j)) = ∑ j, (1 + err j) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [err, K]
        ring
      _ = (n : Real) + ∑ j, err j := by simp [Finset.sum_add_distrib]
  have hintegral :
      (∫ y in -Real.pi..Real.pi, K y * rho y) =
        1 / 2 + ∫ y in -Real.pi..Real.pi, e y * rho y := by
    rw [show (fun y => K y * rho y) =
        fun y => rho y + e y * rho y by
      funext y
      dsimp [e]
      ring]
    rw [intervalIntegral.integral_add hrhoInt herrInt, hrhoMass]
  have hdiff :
      sixVertexRootDensityWeight c x *
          (sixVertexFiniteRootDensity c N n p x - rho x) =
        ((∫ y in -Real.pi..Real.pi, K y * rho y) -
          (∑ j, K (p j)) / N) / (2 * Real.pi) := by
    rw [mul_sub, sixVertexRootDensityWeight_mul_finiteRootDensity hc hN p x,
      hrhoEq x hx]
    dsimp [K]
    ring
  have hcancel :
      ((∫ y in -Real.pi..Real.pi, K y * rho y) -
          (∑ j, K (p j)) / N) =
        (∫ y in -Real.pi..Real.pi, e y * rho y) -
          (∑ j, err j) / N := by
    rw [hintegral, hsum]
    have hn : ((n : Real) + ∑ j, err j) / (N : Real) =
        1 / 2 + (∑ j, err j) / N := by
      rw [add_div, hhalf]
    rw [hn]
    ring
  rw [hdiff, hcancel, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * Real.pi)
  calc
    |(∫ y in -Real.pi..Real.pi, e y * rho y) -
        (∑ j, err j) / N| ≤
      |∫ y in -Real.pi..Real.pi, e y * rho y| +
        |(∑ j, err j) / N| := abs_sub _ _
    _ ≤ E / 2 + E / 2 := add_le_add herrIntegral herrSumScaled
    _ = E := by ring



theorem sixVertexHalfFilledContinuationGauge_le_anisotropyError
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (k : Nat) :
    sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexHalfFilledBetheContinuationPoint ha hc k) ≤
      (1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) /
        (2 * Real.pi) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  unfold sixVertexContinuationWeightedFiniteDensityGauge
  apply sixVertexWeightedFiniteDensityGauge_le_anisotropyError
    hc2 (sixVertexFourWidth_pos 0 k)
  · norm_num [sixVertexFourWidth]
    field_simp
    ring
  · exact sixVertexFourierPhysicalDensityFamily_continuumEquation ha ⟨c, hc⟩
  · exact intervalIntegral_sixVertexFourierPhysicalDensityFamily ha ⟨c, hc⟩
  · intro y hy
    exact (sixVertexFourierPhysicalDensityFamily_pos ha (⟨c, hc⟩, y)).le

theorem sixVertexFourierRootDensity_ge_quarter_of_nine_le
    {c : Real} (hc : 2 < c) (hd9 : 9 ≤ sixVertexAnisotropyMagnitude c)
    (alpha : Real) :
    1 / 4 ≤ sixVertexFourierRootDensity
      (sixVertexAntiferroelectricLambda c) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let q := Real.exp (-lam)
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdexp : sixVertexAnisotropyMagnitude c ≤ Real.exp lam := by
    rw [sixVertexAnisotropyMagnitude_eq_cosh_lambda hc]
    rw [← Real.cosh_add_sinh]
    exact le_add_of_nonneg_right (Real.sinh_pos_iff.mpr hlam).le
  have hq : q ≤ 1 / 9 := by
    have hdpos : 0 < sixVertexAnisotropyMagnitude c := by linarith
    have hexppos : 0 < Real.exp lam := Real.exp_pos _
    have hqmag : q ≤ 1 / sixVertexAnisotropyMagnitude c := by
      dsimp [q]
      rw [Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le hdpos hdexp
    exact hqmag.trans (one_div_le_one_div_of_le (by norm_num) hd9)
  have hmajorSum : (∑' n : Nat,
      sixVertexFourierRootDensityMajorant lam n) = 2 * q / (1 - q) := by
    rw [show (fun n : Nat => sixVertexFourierRootDensityMajorant lam n) =
        fun n => (2 * q) * q ^ n by
      funext n
      dsimp [sixVertexFourierRootDensityMajorant, q]
      rw [pow_succ]
      ring]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    field_simp [(sub_pos.mpr hq1).ne']
  have hmajorQuarter : (∑' n : Nat,
      sixVertexFourierRootDensityMajorant lam n) ≤ 1 / 4 := by
    rw [hmajorSum, div_le_iff₀ (sub_pos.mpr hq1)]
    nlinarith
  have hterm := summable_sixVertexFourierRootDensityTerm hlam alpha
  have hmajor := summable_sixVertexFourierRootDensityMajorant hlam
  have hnorm : |∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha| ≤
      ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n := by
    calc
      |∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha| =
          ‖∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha‖ :=
        by rw [Real.norm_eq_abs]
      _ ≤ ∑' n : Nat,
          ‖sixVertexFourierRootDensityTerm lam n alpha‖ :=
        norm_tsum_le_tsum_norm hterm.norm
      _ ≤ ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n :=
        Summable.tsum_le_tsum
          (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha)
          hterm.norm hmajor
  unfold sixVertexFourierRootDensity
  linarith [hnorm.trans hmajorQuarter,
    neg_abs_le (∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha)]

theorem sixVertexFourierPhysicalDensity_ge_tail
    {c : Real} (hc5 : 5 ≤ c) (x : Real) :
    1 / (16 * Real.pi) ≤
      sixVertexFourierPhysicalDensity c (by linarith) x := by
  have hc : 2 < c := by linarith
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  have hd9 : 9 ≤ d := by
    dsimp [d, sixVertexAnisotropyMagnitude, sixVertexDelta]
    nlinarith [sq_nonneg (c - 5)]
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hsLower : d - 1 ≤ s := by
    dsimp [d, s]
    exact (sixVertexRootDensityScale_bounds hc).1
  have hweight : sixVertexRootDensityWeight c x ≤ 2 := by
    calc
      sixVertexRootDensityWeight c x ≤ (d + 1) / s :=
        sixVertexRootDensityWeight_le hc x
      _ ≤ 2 := by
        rw [div_le_iff₀ hs]
        nlinarith
  have hweightPos := sixVertexRootDensityWeight_pos hc x
  have hnum := sixVertexFourierRootDensity_ge_quarter_of_nine_le hc hd9
    (sixVertexMomentumRapidity (sixVertexAntiferroelectricLambda c)
      (sixVertexAntiferroelectricLambda_pos hc) x)
  unfold sixVertexFourierPhysicalDensity
  rw [div_le_div_iff₀ (by positivity : 0 < 16 * Real.pi)
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hweightPos)]
  nlinarith [Real.pi_pos]



theorem exists_uniformLower_sixVertexFourierPhysicalDensity_Ici
    {a : Real} (ha : 2 < a) :
    ∃ rhoLower : Real, 0 < rhoLower ∧
      ∀ (c) (hac : a ≤ c) (x),
        rhoLower ≤ sixVertexFourierPhysicalDensity c (ha.trans_le hac) x := by
  let b := max a 5
  have hab : a ≤ b := le_max_left _ _
  obtain ⟨rhoCompact, hrhoCompact, hcompact⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensityFamily ha hab
  let rhoTail := 1 / (16 * Real.pi)
  let rhoLower := min rhoCompact rhoTail
  have hrhoTail : 0 < rhoTail := by dsimp [rhoTail]; positivity
  refine ⟨rhoLower, lt_min hrhoCompact hrhoTail, ?_⟩
  intro c hac x
  by_cases hcb : c ≤ b
  · have hcIcc : c ∈ Set.Icc a b := ⟨hac, hcb⟩
    have h := hcompact ⟨c, hcIcc⟩ x
    simp only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
      sixVertexFourierPhysicalDensityFamily_apply] at h
    exact (min_le_left rhoCompact rhoTail).trans h
  · have hc5 : 5 ≤ c := by
      have hbc : b < c := lt_of_not_ge hcb
      exact (le_max_right a 5).trans hbc.le
    exact (min_le_right rhoCompact rhoTail).trans
      (sixVertexFourierPhysicalDensity_ge_tail hc5 x)

theorem tendsto_sixVertexAnisotropyGaugeError :
    Tendsto (fun c : Real =>
      (1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) /
        (2 * Real.pi)) atTop (nhds 0) := by
  have hd : Tendsto (fun c : Real =>
      sixVertexAnisotropyMagnitude c - 1) atTop atTop := by
    rw [tendsto_atTop]
    intro R
    filter_upwards [eventually_ge_atTop (2 * |R| + 4)] with c hc
    have hc0 : 0 ≤ c := by nlinarith [abs_nonneg R]
    have hR : R ≤ |R| := le_abs_self R
    have hsquare : (2 * |R| + 4) ^ 2 ≤ c ^ 2 := by
      simpa only [pow_two] using
        mul_self_le_mul_self (by positivity : 0 ≤ 2 * |R| + 4) hc
    have htarget : 2 * R + 4 ≤ c ^ 2 := by
      calc
        2 * R + 4 ≤ 2 * |R| + 4 := by linarith
        _ ≤ (2 * |R| + 4) ^ 2 := by
          rw [pow_two]
          have hT0 : 0 ≤ 2 * |R| + 4 := by positivity
          have hT1 : 1 ≤ 2 * |R| + 4 := by
            nlinarith [abs_nonneg R]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hT1 hT0
        _ ≤ c ^ 2 := hsquare
    unfold sixVertexAnisotropyMagnitude sixVertexDelta
    linarith
  have hsq : Tendsto (fun c : Real =>
      (sixVertexAnisotropyMagnitude c - 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : Nat) ≠ 0)).comp hd
  have hone : Tendsto (fun c : Real =>
      1 / (sixVertexAnisotropyMagnitude c - 1) ^ 2) atTop (nhds 0) :=
    hsq.const_div_atTop 1
  simpa using hone.div_const (2 * Real.pi)



theorem exists_uniform_sixVertexCoefficientBounds_Ici
    {a : Real} (ha : 2 < a) :
    ∃ kernelB thetaB ratioB boundaryB : Real,
      0 < kernelB ∧ 0 < thetaB ∧ 0 < ratioB ∧
      boundaryB < 2 * Real.pi ∧
      ∀ c, a ≤ c →
        sixVertexRootDensityKernelLipschitzBound c ≤ kernelB ∧
        sixVertexThetaLeftKernelLipschitzBound c ≤ thetaB ∧
        sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1) ≤ ratioB ∧
        sixVertexSymmetricScatteringBoundaryBound c ≤ boundaryB := by
  let d₀ := sixVertexAnisotropyMagnitude a
  let q₀ := d₀ - 1
  let R₀ := d₀ / q₀
  let C₀ := (d₀ + 1) / q₀
  let L₀ := 4 * C₀ + 2 / q₀
  let thetaB := R₀ * C₀ * L₀ / (4 * q₀)
  let kernelB := R₀ * C₀ / q₀ + R₀ * C₀ ^ 2 * L₀ / (4 * q₀)
  let boundaryB := 4 * Real.arctan (1 / (2 * d₀ * q₀))
  have hd₀ : 1 < d₀ := one_lt_sixVertexAnisotropyMagnitude ha
  have hq₀ : 0 < q₀ := by dsimp [q₀]; linarith
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  have hthetaB : 0 < thetaB := by dsimp [thetaB]; positivity
  have hkernelB : 0 < kernelB := by dsimp [kernelB]; positivity
  have hboundaryB : boundaryB < 2 * Real.pi := by
    have h := Real.arctan_lt_pi_div_two (1 / (2 * d₀ * q₀))
    dsimp [boundaryB]
    linarith
  refine ⟨kernelB, thetaB, R₀, boundaryB, hkernelB, hthetaB, hR₀,
    hboundaryB, ?_⟩
  intro c hac
  have hc : 2 < c := ha.trans_le hac
  let d := sixVertexAnisotropyMagnitude c
  let q := d - 1
  let s := sixVertexRootDensityScale c
  let L := 4 * (d + 1) + 2
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hq : 0 < q := by dsimp [q]; linarith
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hdmono : d₀ ≤ d := by
    dsimp [d₀, d]
    exact sixVertexAnisotropyMagnitude_mono (by linarith) hac
  have hqmono : q₀ ≤ q := by dsimp [q₀, q]; linarith
  have hR : d / q ≤ R₀ := by
    dsimp [R₀]
    rw [div_le_div_iff₀ hq hq₀]
    dsimp [q, q₀]
    nlinarith
  have hC : (d + 1) / q ≤ C₀ := by
    dsimp [C₀]
    rw [div_le_div_iff₀ hq hq₀]
    dsimp [q, q₀]
    nlinarith
  have hinvq : 1 / q ≤ 1 / q₀ := by
    exact one_div_le_one_div_of_le hq₀ hqmono
  have hL : L / q ≤ L₀ := by
    calc
      L / q = 4 * ((d + 1) / q) + 2 * (1 / q) := by
        dsimp [L]
        field_simp [hq.ne']
      _ ≤ 4 * C₀ + 2 * (1 / q₀) := by gcongr
      _ = L₀ := by dsimp [L₀]; ring
  have hqs : q ≤ s := by
    dsimp [q, d, s]
    exact (sixVertexRootDensityScale_bounds hc).1
  have hqdivs : q / s ≤ 1 := by
    rw [div_le_one hs]
    exact hqs
  have htheta : sixVertexThetaLeftKernelLipschitzBound c ≤ thetaB := by
    change 4 * d * (d + 1) * L / (16 * q ^ 4) ≤ thetaB
    rw [show 4 * d * (d + 1) * L / (16 * q ^ 4) =
        (d / q) * ((d + 1) / q) * (L / q) * (1 / (4 * q)) by
      field_simp [hq.ne']
      ring]
    dsimp [thetaB]
    calc
      (d / q) * ((d + 1) / q) * (L / q) * (1 / (4 * q)) ≤
          R₀ * C₀ * L₀ * (1 / (4 * q₀)) := by gcongr
      _ = R₀ * C₀ * L₀ / (4 * q₀) := by ring
  have hkernel : sixVertexRootDensityKernelLipschitzBound c ≤ kernelB := by
    change (4 * d * (d + 1) / s) *
      (1 / (4 * q ^ 2) + (d + 1) * L / (4 * q ^ 2) ^ 2) ≤ kernelB
    rw [show (4 * d * (d + 1) / s) *
        (1 / (4 * q ^ 2) + (d + 1) * L / (4 * q ^ 2) ^ 2) =
      (d / q) * ((d + 1) / q) * (q / s) * (1 / q) +
        (d / q) * ((d + 1) / q) ^ 2 * (L / q) *
          (q / s) * (1 / (4 * q)) by
      field_simp [hq.ne', hs.ne']
      ]
    dsimp [kernelB]
    have hqdivs0 : 0 ≤ q / s := div_nonneg hq.le hs.le
    calc
      (d / q) * ((d + 1) / q) * (q / s) * (1 / q) +
          (d / q) * ((d + 1) / q) ^ 2 * (L / q) *
            (q / s) * (1 / (4 * q)) ≤
        R₀ * C₀ * 1 * (1 / q₀) +
          R₀ * C₀ ^ 2 * L₀ * 1 * (1 / (4 * q₀)) := by gcongr
      _ = R₀ * C₀ / q₀ + R₀ * C₀ ^ 2 * L₀ / (4 * q₀) := by ring
  have hboundary :
      sixVertexSymmetricScatteringBoundaryBound c ≤ boundaryB := by
    have hds : d₀ * q₀ ≤ d * s := by
      have hsd₀ : d₀ ≤ d := hdmono
      have hq₀s : q₀ ≤ s := hqmono.trans hqs
      exact mul_le_mul hsd₀ hq₀s hq₀.le (zero_le_one.trans hd.le)
    have hden : 0 < 2 * d₀ * q₀ := by positivity
    have hden' : 0 < 2 * d * s := by positivity
    have harg : 1 / (2 * d * s) ≤ 1 / (2 * d₀ * q₀) := by
      apply one_div_le_one_div_of_le hden
      nlinarith
    unfold sixVertexSymmetricScatteringBoundaryBound
    dsimp [boundaryB, d₀, q₀, d, s] at harg ⊢
    exact mul_le_mul_of_nonneg_left
      (Real.arctan_le_arctan_iff.2 harg) (by norm_num)
  exact ⟨hkernel, htheta, hR, hboundary⟩

theorem sixVertexRootDensityWeightFloor_ge_inv_of_ratio_le
    {c R : Real} (hc : 2 < c) (hR : 0 < R)
    (hratio : sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1) ≤ R) :
    1 / R ≤ (sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c := by
  let d := sixVertexAnisotropyMagnitude c
  let q := d - 1
  let s := sixVertexRootDensityScale c
  have hd : 0 < d := (one_lt_sixVertexAnisotropyMagnitude hc).trans' zero_lt_one
  have hq : 0 < q := by
    dsimp [q]
    linarith [one_lt_sixVertexAnisotropyMagnitude hc]
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hds : s ≤ d := by
    dsimp [d, s]
    exact (sixVertexRootDensityScale_bounds hc).2
  have hdRq : d ≤ R * q := by
    rw [← div_le_iff₀ hq]
    simpa only [d, q] using hratio
  have hqd : 1 / R ≤ q / d := by
    rw [le_div_iff₀ hd, div_mul_eq_mul_div, div_le_iff₀ hR]
    simpa only [one_mul, mul_comm] using hdRq
  have hqds : q / d ≤ q / s :=
    div_le_div_of_nonneg_left hq.le hs hds
  simpa only [d, q, s] using hqd.trans hqds

theorem sixVertexRootDensityContractionRate_le_of_ratio_le
    {c R : Real} (hc : 2 < c) (hR : 0 < R)
    (hratio : sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1) ≤ R) :
    sixVertexRootDensityContractionRate c ≤ 1 - 1 / (10 * R ^ 3) := by
  let d := sixVertexAnisotropyMagnitude c
  let q := d - 1
  let s := sixVertexRootDensityScale c
  let den := (4 * (d + 1) ^ 2 + 4) * (d + 1)
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hq : 0 < q := by dsimp [q]; linarith
  have hs : 0 < s := sixVertexRootDensityScale_pos hc
  have hRone : 1 ≤ R := by
    have hratioOne : 1 ≤ d / q := by
      rw [le_div_iff₀ hq]
      dsimp [q]
      linarith
    exact hratioOne.trans hratio
  have hdRq : d ≤ R * q := by
    rw [← div_le_iff₀ hq]
    simpa only [d, q] using hratio
  have hdp1 : d + 1 ≤ 2 * R * q := by
    calc
      d + 1 ≤ 2 * d := by linarith
      _ ≤ 2 * (R * q) := by gcongr
      _ = 2 * R * q := by ring
  have hden : 0 < den := by dsimp [den]; positivity
  have hdenBound : den ≤ 40 * R ^ 3 * q ^ 3 := by
    calc
      den ≤ 5 * (d + 1) ^ 3 := by
        dsimp [den]
        have hsquare : 1 ≤ (d + 1) ^ 2 := by nlinarith [sq_nonneg d]
        nlinarith
      _ ≤ 5 * (2 * R * q) ^ 3 := by gcongr
      _ = 40 * R ^ 3 * q ^ 3 := by ring
  have hscaled : (1 / (10 * R ^ 3)) * den ≤ 4 * d * q ^ 2 := by
    calc
      (1 / (10 * R ^ 3)) * den ≤
          (1 / (10 * R ^ 3)) * (40 * R ^ 3 * q ^ 3) := by
        gcongr
      _ = 4 * q ^ 3 := by field_simp [hR.ne']; ring
      _ ≤ 4 * d * q ^ 2 := by
        have hqd : q ≤ d := by dsimp [q]; linarith
        nlinarith [mul_le_mul_of_nonneg_right hqd (sq_nonneg q)]
  have hmargin : 1 / (10 * R ^ 3) ≤
      4 * d * q ^ 2 / den := by
    rw [le_div_iff₀ hden]
    exact hscaled
  unfold sixVertexRootDensityContractionRate
    sixVertexRootDensityKernelFloor
  change 1 - (4 * d * q ^ 2 / (s * (4 * (d + 1) ^ 2 + 4))) * s /
      (d + 1) ≤ 1 - 1 / (10 * R ^ 3)
  have hcancel :
      (4 * d * q ^ 2 / (s * (4 * (d + 1) ^ 2 + 4))) * s /
          (d + 1) = 4 * d * q ^ 2 / den := by
    dsimp [den]
    field_simp [hs.ne']
  rw [hcancel]
  linarith




theorem exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici
    {a rhoLower : Real} (ha : 2 < a) (hrhoLower : 0 < rhoLower) :
    ∃ inner outer : Real,
      0 < outer ∧ inner < outer ∧
      (∀ c, a ≤ c → outer ≤ rhoLower *
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) / 2) ∧
      ∀ᶠ N : Nat in atTop, ∀ c, a ≤ c →
        sixVertexRootDensityContractionRate c * outer +
            sixVertexFiniteDensityContinuumErrorOfLower
              c N (rhoLower / 2) ≤ inner ∧
          sixVertexSymmetricScatteringBoundaryBound c +
              2 * sixVertexSymmetricJacobianTotalErrorOfLower
                c N (rhoLower / 2) < 2 * Real.pi := by
  obtain ⟨kernelB, thetaB, R, boundaryB, hkernelB, hthetaB, hR,
      hboundaryB, hcoeff⟩ :=
    exists_uniform_sixVertexCoefficientBounds_Ici ha
  let lower := rhoLower / 2
  let gap := 1 / (10 * R ^ 3)
  let outer := rhoLower / (8 * R)
  let inner := (1 - gap / 2) * outer
  let densityB := kernelB * ((1 + R) / (2 * Real.pi)) *
    (1 / lower) * (2 * Real.pi) / (2 * Real.pi)
  let jacobianB :=
    (4 * Real.pi * (thetaB / (2 * Real.pi)) * (1 / lower) ^ 2 +
      2 * R * (1 / lower)) +
    ((2 * Real.pi) * (2 * thetaB) + 2 * R) * (1 / lower)
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hRone : 1 ≤ R := by
    have haRatio := (hcoeff a le_rfl).2.2.1
    have hd := one_lt_sixVertexAnisotropyMagnitude ha
    have hone : 1 ≤ sixVertexAnisotropyMagnitude a /
        (sixVertexAnisotropyMagnitude a - 1) := by
      rw [le_div_iff₀ (sub_pos.mpr hd)]
      linarith
    exact hone.trans haRatio
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hgapLe : gap ≤ 1 / 10 := by
    dsimp [gap]
    have hRpow : 1 ≤ R ^ 3 := by nlinarith [sq_nonneg R]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have houterPos : 0 < outer := by dsimp [outer]; positivity
  have hinnerOuter : inner < outer := by
    dsimp [inner]
    nlinarith [mul_pos hgap houterPos]
  have hdensityB : 0 < densityB := by dsimp [densityB]; positivity
  have hjacobianB : 0 < jacobianB := by dsimp [jacobianB]; positivity
  have houter : ∀ c, a ≤ c → outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2 := by
    intro c hac
    have hfloor := sixVertexRootDensityWeightFloor_ge_inv_of_ratio_le
      (ha.trans_le hac) hR (hcoeff c hac).2.2.1
    dsimp [outer]
    have hscaled := mul_le_mul_of_nonneg_left hfloor hrhoLower.le
    have hpos : 0 < rhoLower / R := div_pos hrhoLower hR
    calc
      rhoLower / (8 * R) = (rhoLower / R) / 8 := by ring
      _ ≤ (rhoLower / R) / 2 := by nlinarith
      _ = rhoLower * (1 / R) / 2 := by ring
      _ ≤ rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) / 2 := by gcongr
  have herrorOne : ∀ c, a ≤ c →
      sixVertexFiniteDensityContinuumErrorOfLower c 1 lower ≤ densityB := by
    intro c hac
    obtain ⟨hkernel, htheta, hratio, _⟩ := hcoeff c hac
    have hc := ha.trans_le hac
    have htheta0 := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
    have huniform : sixVertexFiniteRootDensityUniformBound c ≤
        (1 + R) / (2 * Real.pi) := by
      unfold sixVertexFiniteRootDensityUniformBound
      gcongr
    have huniform0 : 0 ≤ sixVertexFiniteRootDensityUniformBound c := by
      unfold sixVertexFiniteRootDensityUniformBound
      have hd := one_lt_sixVertexAnisotropyMagnitude hc
      exact div_nonneg
        (by positivity)
        (by positivity)
    unfold sixVertexFiniteDensityContinuumErrorOfLower
    dsimp [densityB]
    norm_num
    gcongr
  have hjacobianOne : ∀ c, a ≤ c →
      sixVertexSymmetricJacobianTotalErrorOfLower c 1 lower ≤ jacobianB := by
    intro c hac
    obtain ⟨_, htheta, hratio, _⟩ := hcoeff c hac
    have hc := ha.trans_le hac
    have htheta0 := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
    have hfiniteLip :
        (sixVertexFiniteRootDensityLipschitzConstant c : Real) ≤
          thetaB / (2 * Real.pi) := by
      unfold sixVertexFiniteRootDensityLipschitzConstant
      rw [Real.coe_toNNReal]
      · exact div_le_div_of_nonneg_right htheta (by positivity)
      · exact div_nonneg htheta0 (by positivity)
    have hscatterLip :
        (sixVertexSymmetricScatteringLipschitzConstant c : Real) ≤
          2 * thetaB := by
      unfold sixVertexSymmetricScatteringLipschitzConstant
      change (2 : Real) * (Real.toNNReal
        (sixVertexThetaLeftKernelLipschitzBound c) : Real) ≤ 2 * thetaB
      have hcoe : (Real.toNNReal
          (sixVertexThetaLeftKernelLipschitzBound c) : Real) =
          sixVertexThetaLeftKernelLipschitzBound c := by
        rw [Real.coe_toNNReal]
        exact htheta0
      rw [hcoe]
      gcongr
    unfold sixVertexSymmetricJacobianTotalErrorOfLower
      sixVertexSymmetricJacobianDiagonalErrorOfLower
      sixVertexSymmetricJacobianOffDiagonalErrorOfLower
    dsimp [jacobianB]
    norm_num
    gcongr
  have hdensityTendsto : Tendsto (fun N : Nat => densityB / N)
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat densityB
  have hjacobianTendsto : Tendsto (fun N : Nat => jacobianB / N)
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat jacobianB
  have hdensityGap : 0 < gap * outer / 2 := by positivity
  have hjacobianGap : 0 < (2 * Real.pi - boundaryB) / 2 := by linarith
  have hdensityEventually : ∀ᶠ N : Nat in atTop,
      densityB / N < gap * outer / 2 :=
    hdensityTendsto.eventually (Iio_mem_nhds hdensityGap)
  have hjacobianEventually : ∀ᶠ N : Nat in atTop,
      jacobianB / N < (2 * Real.pi - boundaryB) / 2 :=
    hjacobianTendsto.eventually (Iio_mem_nhds hjacobianGap)
  refine ⟨inner, outer, houterPos, hinnerOuter, houter, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hdensityEventually,
    hjacobianEventually] with N hN hNE hNJ
  intro c hac
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hrate := sixVertexRootDensityContractionRate_le_of_ratio_le
    (ha.trans_le hac) hR (hcoeff c hac).2.2.1
  have hdensityDiv :
      sixVertexFiniteDensityContinuumErrorOfLower c N lower ≤ densityB / N := by
    rw [sixVertexFiniteDensityContinuumErrorOfLower_eq_one_div c lower hN]
    exact div_le_div_of_nonneg_right (herrorOne c hac) hNreal.le
  have hjacobianDiv :
      sixVertexSymmetricJacobianTotalErrorOfLower c N lower ≤ jacobianB / N := by
    rw [sixVertexSymmetricJacobianTotalErrorOfLower_eq_one_div c lower hN]
    exact div_le_div_of_nonneg_right (hjacobianOne c hac) hNreal.le
  constructor
  · dsimp [inner]
    have houter0 := houterPos.le
    calc
      sixVertexRootDensityContractionRate c * outer +
          sixVertexFiniteDensityContinuumErrorOfLower c N lower ≤
        (1 - gap) * outer + densityB / N := by gcongr
      _ ≤ (1 - gap / 2) * outer := by nlinarith
  · have hboundary := (hcoeff c hac).2.2.2
    calc
      sixVertexSymmetricScatteringBoundaryBound c +
          2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower ≤
        boundaryB + 2 * (jacobianB / N) := by gcongr
      _ < 2 * Real.pi := by linarith



theorem eventually_sixVertexHalfFilledContinuationGauge_lt
    {a outer : Real} (ha : 2 < a) (houter : 0 < outer) (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ (b) (hc : c ∈ Set.Icc a b),
      sixVertexContinuationWeightedFiniteDensityGauge ha
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
          (sixVertexFourierPhysicalDensityFamily ha)
          (sixVertexHalfFilledBetheContinuationPoint ha hc k) <
        outer := by
  have herr := tendsto_sixVertexAnisotropyGaugeError.eventually
    (Iio_mem_nhds houter)
  filter_upwards [eventually_ge_atTop a, herr] with c hca hcerror
  intro b hc
  exact (sixVertexHalfFilledContinuationGauge_le_anisotropyError
    ha hc k).trans_lt hcerror

end

end StatMech.FrontierD
