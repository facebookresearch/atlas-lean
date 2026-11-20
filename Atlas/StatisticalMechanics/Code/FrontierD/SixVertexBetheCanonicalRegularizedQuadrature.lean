/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRegularizedLogTaylor





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexLogNonperiodicQuadratureError
    (c : Real) (N r : Nat) (lower : Real) (C : NNReal) (F : Real) : Real :=
  (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) +
    (2 * (r : Real) / N) * F + 2 * F / N +
    sixVertexFiniteRootDensityUniformBound c * F *
      ((2 * (r : Real) + 1) / ((N : Real) * lower))

theorem tendsto_sixVertexLogNonperiodicQuadratureError
    (c : Real) (r : Nat) {lower : Real} (hlower : 0 < lower)
    (C : NNReal) (F : Real) :
    Tendsto (fun k => sixVertexLogNonperiodicQuadratureError c
      (sixVertexFourWidth r k) r lower C F) atTop (nhds 0) := by
  let E := (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
    2 * (r : Real) * F + 2 * F +
    sixVertexFiniteRootDensityUniformBound c * F *
      ((2 * (r : Real) + 1) / lower)
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth r k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hbase : Tendsto
      (fun k => E / (sixVertexFourWidth r k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  apply hbase.congr'
  filter_upwards [] with k
  unfold sixVertexLogNonperiodicQuadratureError
  dsimp [E]
  have hN : (sixVertexFourWidth r k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos r k).ne'
  field_simp [hN, hlower.ne']

theorem tendsto_sixVertexCanonicalEvenRegularizedDerivativeProfileQuotient
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
          sixVertexContinuousOffsetFourier c hc
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) /
          sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
            ((s + k + 1) + (s + k + 1))
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) /
        (sixVertexFourWidth (2 * s) k : Real)) atTop
      (nhds (∫ x in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogNormDerivative c epsilon x *
          sixVertexContinuousOffsetFourier c hc x)) := by
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  let u := sixVertexRegularizedBetheLogNormDerivative c epsilon
  let tau := sixVertexContinuousOffsetFourier c hc
  let U := sixVertexRegularizedBetheLogNormDerivativeBound c epsilon
  let G := sixVertexContinuousOffsetFourierBound c
  let Lu := sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon
  let D := sixVertexContinuousOffsetFourierLipschitzNNReal c
  let C := sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D
  let F := U * G / lower
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have hU : 0 <= U := by
    dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  have hG : 0 <= G := by
    dsimp [G, sixVertexContinuousOffsetFourierBound]
    positivity
  have herror := tendsto_sixVertexLogNonperiodicQuadratureError
    c (2 * s) hlower C F
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ herror
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  let N := sixVertexFourWidth (2 * s) k
  let n := (s + k + 1) + (s + k + 1)
  let p := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let rho := sixVertexFiniteRootDensity c N n p
  let f : Real -> Real := fun y => u y * tau y / rho y
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hn : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  have hcharge : N = 2 * n + 2 * (2 * s) := by
    dsimp [N, n]
    unfold sixVertexFourWidth
    omega
  have huLip : LipschitzWith Lu u := by
    exact lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon
  have huBound (y : Real) : |u y| <= U :=
    abs_sixVertexRegularizedBetheLogNormDerivative_le hc hepsilon
  have htauLip : LipschitzWith D tau :=
    lipschitzWith_sixVertexContinuousOffsetFourier hc
  have htauBound (y : Real) : |tau y| <= G :=
    abs_sixVertexContinuousOffsetFourier_le hc y
  have hfLip : LipschitzWith C f := by
    exact lipschitzWith_mul_div_sixVertexFiniteRootDensity hc hN hn p
      hlower hU hG hk.2 huLip huBound htauLip htauBound
  have hfBound (y : Real) : |f y| <= F := by
    have hry : 0 < rho y := hlower.trans_le (hk.2 y)
    dsimp [f, F]
    rw [abs_div, abs_mul, abs_of_pos hry]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul (huBound y) (htauBound y) (abs_nonneg _) hU) hry.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hU hG) hlower (hk.2 y))
  have hquad :=
    abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
      hc hN hcharge hk.1.1 hk.1.2.1 hlower hk.2
      hfLip.continuous hfLip hfBound
  change |(∑ j, f (p j)) / N -
      ∫ y in -Real.pi..Real.pi, f y * rho y| <= _ at hquad
  have hintegral : (∫ y in -Real.pi..Real.pi, f y * rho y) =
      ∫ y in -Real.pi..Real.pi, u y * tau y := by
    apply intervalIntegral.integral_congr
    intro y _
    have hry : rho y ≠ 0 := (hlower.trans_le (hk.2 y)).ne'
    dsimp only [f]
    field_simp [hry]
  rw [hintegral] at hquad
  simpa [Real.norm_eq_abs, f, p, rho, u, tau, N, n, C, F, lower,
    sixVertexLogNonperiodicQuadratureError] using hquad

theorem tendsto_sixVertexCanonicalOddRegularizedDerivativeProfileQuotient
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
          sixVertexContinuousOffsetFourier c hc
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) /
          sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
            (((s + k + 1) + 1) + (s + k + 1))
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) atTop
      (nhds (∫ x in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogNormDerivative c epsilon x *
          sixVertexContinuousOffsetFourier c hc x)) := by
  let lower := sixVertexCanonicalFixedOddDensityFloor hc s
  let u := sixVertexRegularizedBetheLogNormDerivative c epsilon
  let tau := sixVertexContinuousOffsetFourier c hc
  let U := sixVertexRegularizedBetheLogNormDerivativeBound c epsilon
  let G := sixVertexContinuousOffsetFourierBound c
  let Lu := sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon
  let D := sixVertexContinuousOffsetFourierLipschitzNNReal c
  let C := sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D
  let F := U * G / lower
  have hlower : 0 < lower := sixVertexCanonicalFixedOddDensityFloor_pos hc s
  have hU : 0 <= U := by
    dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  have hG : 0 <= G := by
    dsimp [G, sixVertexContinuousOffsetFourierBound]
    positivity
  have herror := tendsto_sixVertexLogNonperiodicQuadratureError
    c (2 * s + 1) hlower C F
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ herror
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let p := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let rho := sixVertexFiniteRootDensity c N n p
  let f : Real -> Real := fun y => u y * tau y / rho y
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hn : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  have hcharge : N = 2 * n + 2 * (2 * s + 1) := by
    dsimp [N, n]
    unfold sixVertexFourWidth
    omega
  have huLip : LipschitzWith Lu u := by
    exact lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon
  have huBound (y : Real) : |u y| <= U :=
    abs_sixVertexRegularizedBetheLogNormDerivative_le hc hepsilon
  have htauLip : LipschitzWith D tau :=
    lipschitzWith_sixVertexContinuousOffsetFourier hc
  have htauBound (y : Real) : |tau y| <= G :=
    abs_sixVertexContinuousOffsetFourier_le hc y
  have hfLip : LipschitzWith C f := by
    exact lipschitzWith_mul_div_sixVertexFiniteRootDensity hc hN hn p
      hlower hU hG hk.2 huLip huBound htauLip htauBound
  have hfBound (y : Real) : |f y| <= F := by
    have hry : 0 < rho y := hlower.trans_le (hk.2 y)
    dsimp [f, F]
    rw [abs_div, abs_mul, abs_of_pos hry]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul (huBound y) (htauBound y) (abs_nonneg _) hU) hry.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hU hG) hlower (hk.2 y))
  have hquad :=
    abs_empiricalLipschitz_sub_finiteDensityIntegral_fixedCharge_nonperiodic
      hc hN hcharge hk.1.1 hk.1.2.1 hlower hk.2
      hfLip.continuous hfLip hfBound
  change |(∑ j, f (p j)) / N -
      ∫ y in -Real.pi..Real.pi, f y * rho y| <= _ at hquad
  have hintegral : (∫ y in -Real.pi..Real.pi, f y * rho y) =
      ∫ y in -Real.pi..Real.pi, u y * tau y := by
    apply intervalIntegral.integral_congr
    intro y _
    have hry : rho y ≠ 0 := (hlower.trans_le (hk.2 y)).ne'
    dsimp only [f]
    field_simp [hry]
  rw [hintegral] at hquad
  simpa [Real.norm_eq_abs, f, p, rho, u, tau, N, n, C, F, lower,
    sixVertexLogNonperiodicQuadratureError] using hquad

theorem tendsto_sixVertexCanonicalEvenRegularizedLinearizedOffset
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
        sixVertexCanonicalEvenChargeOffset hc s k j) /
          (sixVertexFourWidth (2 * s) k : Real)) atTop
      (nhds ((2 * s : Real) *
        ∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x)) := by
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  let u := sixVertexRegularizedBetheLogNormDerivative c epsilon
  let tau := sixVertexContinuousOffsetFourier c hc
  let U := sixVertexRegularizedBetheLogNormDerivativeBound c epsilon
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have hU : 0 < U := by
    dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  let Q : Nat -> Real := fun k =>
    (∑ j, u (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
        tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) /
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1))
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) /
      (sixVertexFourWidth (2 * s) k : Real)
  have hQ : Tendsto Q atTop (nhds (∫ x in -Real.pi..Real.pi,
      u x * tau x)) := by
    exact tendsto_sixVertexCanonicalEvenRegularizedDerivativeProfileQuotient
      hc s hepsilon
  have hdiff : Tendsto (fun k =>
      (∑ j, u (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
        sixVertexCanonicalEvenChargeOffset hc s k j) /
          (sixVertexFourWidth (2 * s) k : Real) - (2 * s : Real) * Q k)
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro eta heta
    let delta := eta * lower / (2 * U)
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hnodal :=
      eventually_uniform_sixVertexCanonicalEvenDensityOffset_fourier
        hc s hdelta
    have hwitness :=
      eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s
    rw [eventually_atTop] at hwitness hnodal
    obtain ⟨Kw, hKw⟩ := hwitness
    obtain ⟨Kn, hKn⟩ := hnodal
    refine ⟨max Kw Kn, ?_⟩
    intro k hkmax
    have hk := hKw k ((le_max_left Kw Kn).trans hkmax)
    have hkNodal := hKn k ((le_max_right Kw Kn).trans hkmax)
    let N := sixVertexFourWidth (2 * s) k
    let n := (s + k + 1) + (s + k + 1)
    let p := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    let rho := sixVertexFiniteRootDensity c N n p
    let off := sixVertexCanonicalEvenChargeOffset hc s k
    have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hn : n <= N := by
      dsimp [n, N]
      unfold sixVertexFourWidth
      omega
    have hnreal : (n : Real) <= N := by exact_mod_cast hn
    have hterm (j : Fin n) :
        |(u (p j) / rho (p j)) *
          (rho (p j) * off j - (2 * s : Real) * tau (p j))| <=
            (U / lower) * delta := by
      have hrho : 0 < rho (p j) := hlower.trans_le (hk.2 (p j))
      have hu := abs_sixVertexRegularizedBetheLogNormDerivative_le
        hc hepsilon (x := p j)
      have hratio : |u (p j) / rho (p j)| <= U / lower := by
        rw [abs_div, abs_of_pos hrho]
        exact (div_le_div_of_nonneg_right hu hrho.le).trans
          (div_le_div_of_nonneg_left hU.le hlower (hk.2 (p j)))
      rw [abs_mul]
      exact mul_le_mul hratio (hkNodal j).le (abs_nonneg _)
        (div_nonneg hU.le hlower.le)
    have heq :
        (∑ j, u (p j) * off j) / (N : Real) - (2 * s : Real) * Q k =
          (∑ j, (u (p j) / rho (p j)) *
            (rho (p j) * off j - (2 * s : Real) * tau (p j))) / N := by
      change (∑ j, u (p j) * off j) / (N : Real) -
          (2 * s : Real) *
            ((∑ j, u (p j) * tau (p j) / rho (p j)) / N) = _
      rw [show (∑ j, u (p j) * off j) / (N : Real) -
          (2 * s : Real) *
            ((∑ j, u (p j) * tau (p j) / rho (p j)) / N) =
        ((∑ j, u (p j) * off j) -
          (2 * s : Real) *
            (∑ j, u (p j) * tau (p j) / rho (p j))) / N by ring]
      congr 1
      rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hrho : rho (p j) ≠ 0 := (hlower.trans_le (hk.2 (p j))).ne'
      field_simp [hrho]
    rw [Real.dist_eq, sub_zero, heq, abs_div, abs_of_pos hNreal]
    calc
      |∑ j, (u (p j) / rho (p j)) *
          (rho (p j) * off j - (2 * s : Real) * tau (p j))| / N <=
          (∑ j, |(u (p j) / rho (p j)) *
            (rho (p j) * off j - (2 * s : Real) * tau (p j))|) / N := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ <= (∑ _j : Fin n, (U / lower) * delta) / N := by
        gcongr with j
        exact hterm j
      _ = ((n : Real) / N) * ((U / lower) * delta) := by
        simp
        ring
      _ <= 1 * ((U / lower) * delta) := by
        gcongr
        exact (div_le_one hNreal).2 hnreal
      _ = eta / 2 := by
        dsimp [delta]
        field_simp [hlower.ne', hU.ne']
      _ < eta := by linarith
  have hadd := hdiff.add (hQ.const_mul (2 * s : Real))
  change Tendsto (fun k =>
    (∑ j, u (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
      sixVertexCanonicalEvenChargeOffset hc s k j) /
        (sixVertexFourWidth (2 * s) k : Real)) atTop
    (nhds ((2 * s : Real) *
      ∫ x in -Real.pi..Real.pi, u x * tau x))
  convert hadd using 1
  · funext k
    ring
  · ring

theorem tendsto_sixVertexCanonicalEvenRegularizedRootDisplacement
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalEvenAlignedHalfRoots hc s k j))) atTop
      (nhds ((2 * s : Real) *
        ∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x)) := by
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  let u := sixVertexRegularizedBetheLogNormDerivative c epsilon
  let L := sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon
  let B := sixVertexCanonicalEvenOffsetUniformBound c hc s
  let linear : Nat -> Real := fun k =>
    (∑ j, u (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
      sixVertexCanonicalEvenChargeOffset hc s k j) /
        (sixVertexFourWidth (2 * s) k : Real)
  have hlinear : Tendsto linear atTop
      (nhds ((2 * s : Real) *
        ∫ x in -Real.pi..Real.pi, u x *
          sixVertexContinuousOffsetFourier c hc x)) := by
    exact tendsto_sixVertexCanonicalEvenRegularizedLinearizedOffset
      hc s hepsilon
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hright : Tendsto (fun k => (L : Real) * B ^ 2 /
      (sixVertexFourWidth (2 * s) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hdiff : Tendsto (fun k =>
      (∑ j, (f (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) -
        f (sixVertexCanonicalEvenAlignedHalfRoots hc s k j))) - linear k)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hright
    filter_upwards
      [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s,
        eventually_abs_sixVertexCanonicalEvenChargeOffset_le hc s]
        with k hk hkoff
    let N := sixVertexFourWidth (2 * s) k
    let n := (s + k + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
    let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
    let off := sixVertexCanonicalEvenChargeOffset hc s k
    have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hn : n <= N := by
      dsimp [n, N]
      unfold sixVertexFourWidth
      omega
    have hnreal : (n : Real) <= N := by exact_mod_cast hn
    have hB : 0 <= B := sixVertexCanonicalEvenOffsetUniformBound_nonneg hc s
    have hterm (j : Fin n) :
        |f (q j) - f (p j) - u (q j) * (q j - p j)| <=
          (L : Real) * (B / N) ^ 2 := by
      have htaylor :=
        abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le
          hc hepsilon (q j) (p j)
      have hdelta : |q j - p j| <= B / N := by
        have hdef : off j = (N : Real) * (q j - p j) := rfl
        have hoff' : |off j| <= B := by simpa [off, B] using hkoff j
        rw [hdef, abs_mul, abs_of_pos hNreal] at hoff'
        exact (le_div_iff₀ hNreal).2 (by simpa [mul_comm] using hoff')
      have hnonneg : 0 <= (L : Real) := NNReal.coe_nonneg _
      calc
        |f (q j) - f (p j) - u (q j) * (q j - p j)| =
            |-(f (p j) - f (q j) - u (q j) * (p j - q j))| := by
              congr 1
              ring
        _ = |f (p j) - f (q j) - u (q j) * (p j - q j)| := abs_neg _
        _ <= (L : Real) * |p j - q j| ^ 2 := htaylor
        _ <= (L : Real) * (B / N) ^ 2 := by
          gcongr
          simpa [abs_sub_comm] using hdelta
    have heq :
        (∑ j, (f (q j) - f (p j))) - linear k =
          ∑ j, (f (q j) - f (p j) - u (q j) * (q j - p j)) := by
      have hoff (j : Fin n) : q j - p j = off j / N := by
        have hdef : off j = (N : Real) * (q j - p j) := rfl
        rw [hdef]
        field_simp [hNreal.ne']
      have hlin : (∑ j, u (q j) * (q j - p j)) = linear k := by
        dsimp [linear]
        calc
          (∑ j, u (q j) * (q j - p j)) =
              ∑ j, (u (q j) * off j) / N := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hoff]
            ring
          _ = (∑ j, u (q j) * off j) / N := by rw [Finset.sum_div]
      rw [<- hlin, <- Finset.sum_sub_distrib]
    rw [Real.norm_eq_abs, sub_zero, heq]
    calc
      |∑ j, (f (q j) - f (p j) - u (q j) * (q j - p j))| <=
          ∑ j, |f (q j) - f (p j) - u (q j) * (q j - p j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _j : Fin n, (L : Real) * (B / N) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact hterm j
      _ = (n : Real) * (L : Real) * B ^ 2 / N ^ 2 := by
        simp
        field_simp [hNreal.ne']
      _ <= (N : Real) * (L : Real) * B ^ 2 / N ^ 2 := by
        gcongr
      _ = (L : Real) * B ^ 2 / N := by
        field_simp [hNreal.ne']
  have hadd := hdiff.add hlinear
  change Tendsto (fun k =>
    ∑ j, (f (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) -
      f (sixVertexCanonicalEvenAlignedHalfRoots hc s k j))) atTop
    (nhds ((2 * s : Real) *
      ∫ x in -Real.pi..Real.pi, u x *
        sixVertexContinuousOffsetFourier c hc x))
  convert hadd using 1
  · funext k
    ring
  · ring

theorem sum_sixVertexCanonicalEvenRegularizedRootDisplacement_eq_positive
    {c : Real} (hc : 2 < c) (s k : Nat) (epsilon : Real)
    (hfixed : SixVertexCanonicalFixedEvenDensityWitness hc s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) :
    (∑ j,
      (sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) -
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k j))) =
      2 * ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalEvenCommonHalfRoot hc s k j)) := by
  let m := s + k + 1
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let g : Fin (m + m) -> Real := fun j =>
    sixVertexRegularizedBetheLogKernel c epsilon (q j) -
      sixVertexRegularizedBetheLogKernel c epsilon (p j)
  have hindex (j : Fin m) :
      Fin.castAdd m j = (Fin.natAdd m j.rev).rev := by
    apply Fin.ext
    simp [Fin.rev, Fin.castAdd, Fin.natAdd]
    omega
  have hneg (j : Fin m) :
      g (Fin.castAdd m j) = g (Fin.natAdd m j.rev) := by
    rw [hindex]
    dsimp [g, q, p]
    rw [hfixed.1.1.2.1,
      sixVertexCanonicalEvenAlignedHalfRoots_rev,
      even_sixVertexRegularizedBetheLogKernel,
      even_sixVertexRegularizedBetheLogKernel]
  have hnegSum : (∑ j : Fin m, g (Fin.castAdd m j)) =
      ∑ j : Fin m, g (Fin.natAdd m j) := by
    simp_rw [hneg]
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin m => g (Fin.natAdd m j)))
  have hpos : (∑ j : Fin m, g (Fin.natAdd m j)) =
      ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalEvenCommonHalfRoot hc s k j)) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g, q, p, m, sixVertexCanonicalFixedEvenDensityPositiveRoots]
    rw [sixVertexCanonicalEvenAlignedHalfRoots_positive]
  change (∑ j : Fin (m + m), g j) = _
  rw [Fin.sum_univ_add, hnegSum, hpos]
  ring

theorem tendsto_sixVertexCanonicalEvenPositiveRegularizedRootDisplacement
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      2 * ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalEvenCommonHalfRoot hc s k j))) atTop
      (nhds ((2 * s : Real) *
        ∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x)) := by
  apply (tendsto_sixVertexCanonicalEvenRegularizedRootDisplacement
    hc s hepsilon).congr'
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  exact sum_sixVertexCanonicalEvenRegularizedRootDisplacement_eq_positive
    hc s k epsilon hk

theorem tendsto_sixVertexCanonicalOddRegularizedLinearizedOffset
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      (∑ j, sixVertexRegularizedBetheLogNormDerivative c epsilon
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
        sixVertexCanonicalOddChargeOffset hc s k j) /
          (sixVertexFourWidth (2 * s + 1) k : Real)) atTop
      (nhds ((2 * s + 1 : Real) *
        ∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x)) := by
  let lower := sixVertexCanonicalFixedOddDensityFloor hc s
  let u := sixVertexRegularizedBetheLogNormDerivative c epsilon
  let tau := sixVertexContinuousOffsetFourier c hc
  let U := sixVertexRegularizedBetheLogNormDerivativeBound c epsilon
  have hlower : 0 < lower := sixVertexCanonicalFixedOddDensityFloor_pos hc s
  have hU : 0 < U := by
    dsimp [U, sixVertexRegularizedBetheLogNormDerivativeBound]
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  let Q : Nat -> Real := fun k =>
    (∑ j, u (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
        tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) /
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) /
      (sixVertexFourWidth (2 * s + 1) k : Real)
  have hQ : Tendsto Q atTop (nhds (∫ x in -Real.pi..Real.pi,
      u x * tau x)) := by
    exact tendsto_sixVertexCanonicalOddRegularizedDerivativeProfileQuotient
      hc s hepsilon
  have hdiff : Tendsto (fun k =>
      (∑ j, u (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
        sixVertexCanonicalOddChargeOffset hc s k j) /
          (sixVertexFourWidth (2 * s + 1) k : Real) -
        (2 * s + 1 : Real) * Q k) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro eta heta
    let delta := eta * lower / (2 * U)
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hnodal :=
      eventually_uniform_sixVertexCanonicalOddDensityOffset_fourier
        hc s hdelta
    have hwitness :=
      eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s
    rw [eventually_atTop] at hwitness hnodal
    obtain ⟨Kw, hKw⟩ := hwitness
    obtain ⟨Kn, hKn⟩ := hnodal
    refine ⟨max Kw Kn, ?_⟩
    intro k hkmax
    have hk := hKw k ((le_max_left Kw Kn).trans hkmax)
    have hkNodal := hKn k ((le_max_right Kw Kn).trans hkmax)
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := ((s + k + 1) + 1) + (s + k + 1)
    let p := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
    let rho := sixVertexFiniteRootDensity c N n p
    let off := sixVertexCanonicalOddChargeOffset hc s k
    have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hn : n <= N := by
      dsimp [n, N]
      unfold sixVertexFourWidth
      omega
    have hnreal : (n : Real) <= N := by exact_mod_cast hn
    have hterm (j : Fin n) :
        |(u (p j) / rho (p j)) *
          (rho (p j) * off j - (2 * s + 1 : Real) * tau (p j))| <=
            (U / lower) * delta := by
      have hrho : 0 < rho (p j) := hlower.trans_le (hk.2 (p j))
      have hu := abs_sixVertexRegularizedBetheLogNormDerivative_le
        hc hepsilon (x := p j)
      have hratio : |u (p j) / rho (p j)| <= U / lower := by
        rw [abs_div, abs_of_pos hrho]
        exact (div_le_div_of_nonneg_right hu hrho.le).trans
          (div_le_div_of_nonneg_left hU.le hlower (hk.2 (p j)))
      rw [abs_mul]
      exact mul_le_mul hratio (hkNodal j).le (abs_nonneg _)
        (div_nonneg hU.le hlower.le)
    have heq :
        (∑ j, u (p j) * off j) / (N : Real) -
            (2 * s + 1 : Real) * Q k =
          (∑ j, (u (p j) / rho (p j)) *
            (rho (p j) * off j -
              (2 * s + 1 : Real) * tau (p j))) / N := by
      change (∑ j, u (p j) * off j) / (N : Real) -
          (2 * s + 1 : Real) *
            ((∑ j, u (p j) * tau (p j) / rho (p j)) / N) = _
      rw [show (∑ j, u (p j) * off j) / (N : Real) -
          (2 * s + 1 : Real) *
            ((∑ j, u (p j) * tau (p j) / rho (p j)) / N) =
        ((∑ j, u (p j) * off j) -
          (2 * s + 1 : Real) *
            (∑ j, u (p j) * tau (p j) / rho (p j))) / N by ring]
      congr 1
      rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hrho : rho (p j) ≠ 0 := (hlower.trans_le (hk.2 (p j))).ne'
      field_simp [hrho]
    rw [Real.dist_eq, sub_zero, heq, abs_div, abs_of_pos hNreal]
    calc
      |∑ j, (u (p j) / rho (p j)) *
          (rho (p j) * off j - (2 * s + 1 : Real) * tau (p j))| / N <=
          (∑ j, |(u (p j) / rho (p j)) *
            (rho (p j) * off j -
              (2 * s + 1 : Real) * tau (p j))|) / N := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ <= (∑ _j : Fin n, (U / lower) * delta) / N := by
        gcongr with j
        exact hterm j
      _ = ((n : Real) / N) * ((U / lower) * delta) := by
        simp
        ring
      _ <= 1 * ((U / lower) * delta) := by
        gcongr
        exact (div_le_one hNreal).2 hnreal
      _ = eta / 2 := by
        dsimp [delta]
        field_simp [hlower.ne', hU.ne']
      _ < eta := by linarith
  have hadd := hdiff.add (hQ.const_mul (2 * s + 1 : Real))
  change Tendsto (fun k =>
    (∑ j, u (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
      sixVertexCanonicalOddChargeOffset hc s k j) /
        (sixVertexFourWidth (2 * s + 1) k : Real)) atTop
    (nhds ((2 * s + 1 : Real) *
      ∫ x in -Real.pi..Real.pi, u x * tau x))
  convert hadd using 1
  · funext k
    ring
  · ring

theorem tendsto_sixVertexCanonicalOddRegularizedRootDisplacement
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalOddAlignedHalfRoots hc s k j))) atTop
      (nhds ((2 * s + 1 : Real) *
        ∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x)) := by
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  let u := sixVertexRegularizedBetheLogNormDerivative c epsilon
  let L := sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon
  let B := sixVertexCanonicalOddOffsetUniformBound c hc s
  let linear : Nat -> Real := fun k =>
    (∑ j, u (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
      sixVertexCanonicalOddChargeOffset hc s k j) /
        (sixVertexFourWidth (2 * s + 1) k : Real)
  have hlinear : Tendsto linear atTop
      (nhds ((2 * s + 1 : Real) *
        ∫ x in -Real.pi..Real.pi, u x *
          sixVertexContinuousOffsetFourier c hc x)) := by
    exact tendsto_sixVertexCanonicalOddRegularizedLinearizedOffset
      hc s hepsilon
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hright : Tendsto (fun k => (L : Real) * B ^ 2 /
      (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hdiff : Tendsto (fun k =>
      (∑ j, (f (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) -
        f (sixVertexCanonicalOddAlignedHalfRoots hc s k j))) - linear k)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hright
    filter_upwards
      [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s,
        eventually_abs_sixVertexCanonicalOddChargeOffset_le hc s]
        with k hk hkoff
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := ((s + k + 1) + 1) + (s + k + 1)
    let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
    let p := sixVertexCanonicalOddAlignedHalfRoots hc s k
    let off := sixVertexCanonicalOddChargeOffset hc s k
    have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hn : n <= N := by
      dsimp [n, N]
      unfold sixVertexFourWidth
      omega
    have hnreal : (n : Real) <= N := by exact_mod_cast hn
    have hB : 0 <= B := sixVertexCanonicalOddOffsetUniformBound_nonneg hc s
    have hterm (j : Fin n) :
        |f (q j) - f (p j) - u (q j) * (q j - p j)| <=
          (L : Real) * (B / N) ^ 2 := by
      have htaylor :=
        abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le
          hc hepsilon (q j) (p j)
      have hdelta : |q j - p j| <= B / N := by
        have hdef : off j = (N : Real) * (q j - p j) := rfl
        have hoff' : |off j| <= B := by simpa [off, B] using hkoff j
        rw [hdef, abs_mul, abs_of_pos hNreal] at hoff'
        exact (le_div_iff₀ hNreal).2 (by simpa [mul_comm] using hoff')
      have hnonneg : 0 <= (L : Real) := NNReal.coe_nonneg _
      calc
        |f (q j) - f (p j) - u (q j) * (q j - p j)| =
            |-(f (p j) - f (q j) - u (q j) * (p j - q j))| := by
              congr 1
              ring
        _ = |f (p j) - f (q j) - u (q j) * (p j - q j)| := abs_neg _
        _ <= (L : Real) * |p j - q j| ^ 2 := htaylor
        _ <= (L : Real) * (B / N) ^ 2 := by
          gcongr
          simpa [abs_sub_comm] using hdelta
    have heq :
        (∑ j, (f (q j) - f (p j))) - linear k =
          ∑ j, (f (q j) - f (p j) - u (q j) * (q j - p j)) := by
      have hoff (j : Fin n) : q j - p j = off j / N := by
        have hdef : off j = (N : Real) * (q j - p j) := rfl
        rw [hdef]
        field_simp [hNreal.ne']
      have hlin : (∑ j, u (q j) * (q j - p j)) = linear k := by
        dsimp [linear]
        calc
          (∑ j, u (q j) * (q j - p j)) =
              ∑ j, (u (q j) * off j) / N := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hoff]
            ring
          _ = (∑ j, u (q j) * off j) / N := by rw [Finset.sum_div]
      rw [<- hlin, <- Finset.sum_sub_distrib]
    rw [Real.norm_eq_abs, sub_zero, heq]
    calc
      |∑ j, (f (q j) - f (p j) - u (q j) * (q j - p j))| <=
          ∑ j, |f (q j) - f (p j) - u (q j) * (q j - p j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _j : Fin n, (L : Real) * (B / N) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact hterm j
      _ = (n : Real) * (L : Real) * B ^ 2 / N ^ 2 := by
        simp
        field_simp [hNreal.ne']
      _ <= (N : Real) * (L : Real) * B ^ 2 / N ^ 2 := by
        gcongr
      _ = (L : Real) * B ^ 2 / N := by
        field_simp [hNreal.ne']
  have hadd := hdiff.add hlinear
  change Tendsto (fun k =>
    ∑ j, (f (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) -
      f (sixVertexCanonicalOddAlignedHalfRoots hc s k j))) atTop
    (nhds ((2 * s + 1 : Real) *
      ∫ x in -Real.pi..Real.pi, u x *
        sixVertexContinuousOffsetFourier c hc x))
  convert hadd using 1
  · funext k
    ring
  · ring

theorem sum_sixVertexCanonicalOddRegularizedRootDisplacement_eq_positive
    {c : Real} (hc : 2 < c) (s k : Nat) (epsilon : Real)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    (∑ j,
      (sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) -
        sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexCanonicalOddAlignedHalfRoots hc s k j))) =
      2 * ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) := by
  let m := s + k + 1
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalOddAlignedHalfRoots hc s k
  let g : Fin ((m + 1) + m) -> Real := fun j =>
    sixVertexRegularizedBetheLogKernel c epsilon (q j) -
      sixVertexRegularizedBetheLogKernel c epsilon (p j)
  have hqzero : q (sixVertexOddCentralIndex m) = 0 := by
    exact sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
      hc s k hfixed
  have hpzero : p (sixVertexOddCentralIndex m) = 0 := by
    have hsym := sixVertexCanonicalOddAlignedHalfRoots_rev hc s k
      (sixVertexOddCentralIndex m)
    rw [sixVertexOddCentralIndex_rev] at hsym
    dsimp [p, m] at hsym ⊢
    linarith
  have hgzero : g (sixVertexOddCentralIndex m) = 0 := by
    dsimp [g]
    rw [hqzero, hpzero]
    ring
  have hindex (j : Fin m) :
      sixVertexOddNegativeIndex m j =
        (sixVertexOddPositiveIndex m j.rev).rev := by
    apply Fin.ext
    simp [sixVertexOddNegativeIndex, sixVertexOddPositiveIndex,
      Fin.rev, Fin.castAdd, Fin.natAdd]
    omega
  have hnegTerm (j : Fin m) :
      g (sixVertexOddNegativeIndex m j) =
        g (sixVertexOddPositiveIndex m j.rev) := by
    rw [hindex]
    dsimp [g, q, p, m]
    rw [hfixed.1.1.2.1,
      sixVertexCanonicalOddAlignedHalfRoots_rev,
      even_sixVertexRegularizedBetheLogKernel,
      even_sixVertexRegularizedBetheLogKernel]
  have hnegSum :
      (∑ j : Fin m, g (sixVertexOddNegativeIndex m j)) =
        ∑ j : Fin m, g (sixVertexOddPositiveIndex m j) := by
    simp_rw [hnegTerm]
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin m => g (sixVertexOddPositiveIndex m j)))
  have hneg : (∑ j : Fin (m + 1), g (Fin.castAdd m j)) =
      ∑ j : Fin m, g (Fin.natAdd (m + 1) j) := by
    rw [Fin.sum_univ_castSucc]
    have hterms :
        (∑ j : Fin m, g (Fin.castAdd m j.castSucc)) =
          ∑ j : Fin m, g (sixVertexOddNegativeIndex m j) := by
      rfl
    rw [hterms, hnegSum]
    have hlast : g (Fin.castAdd m (Fin.last m)) = 0 := by
      change g (sixVertexOddCentralIndex m) = 0
      exact hgzero
    rw [hlast, add_zero]
    rfl
  have hpos : (∑ j : Fin m, g (Fin.natAdd (m + 1) j)) =
      ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g, q, p, m, sixVertexCanonicalFixedOddDensityPositiveRoots,
      sixVertexOddPositiveIndex]
    have hp := sixVertexCanonicalOddAlignedHalfRoots_positive hc s k j
    simpa [sixVertexOddPositiveIndex, Nat.add_assoc] using congrArg
      (fun x => sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
          (Fin.natAdd (s + k + 1 + 1) j)) -
          sixVertexRegularizedBetheLogKernel c epsilon x) hp
  change (∑ j : Fin ((m + 1) + m), g j) = _
  rw [Fin.sum_univ_add, hneg, hpos]
  ring

theorem tendsto_sixVertexCanonicalOddPositiveRegularizedRootDisplacement
    {c : Real} (hc : 2 < c) (s : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Tendsto (fun k =>
      2 * ∑ j,
        (sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
          sixVertexRegularizedBetheLogKernel c epsilon
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) atTop
      (nhds ((2 * s + 1 : Real) *
        ∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x)) := by
  apply (tendsto_sixVertexCanonicalOddRegularizedRootDisplacement
    hc s hepsilon).congr'
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  exact sum_sixVertexCanonicalOddRegularizedRootDisplacement_eq_positive
    hc s k epsilon hk

end

end StatMech.FrontierD
