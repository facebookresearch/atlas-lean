/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalLogUnregularization
import Code.FrontierD.SixVertexBetheCanonicalOddOffsetLinear
import Code.FrontierD.SixVertexBetheCanonicalOddLogInterface





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddRegularizedBulkLogDisplacement
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalOddMidpointHalfRoot hc s k j))

def sixVertexCanonicalOddEffectiveOffsetLinearBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  sixVertexCanonicalOddOffsetLinearBound c hc s +
    sixVertexCanonicalOddOffsetRemainderBound c hc s / Real.pi

theorem sixVertexCanonicalOddEffectiveOffsetLinearBound_nonneg
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 <= sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s := by
  unfold sixVertexCanonicalOddEffectiveOffsetLinearBound
  exact add_nonneg (sixVertexCanonicalOddOffsetLinearBound_nonneg hc s)
    (div_nonneg (sixVertexCanonicalOddOffsetRemainderBound_nonneg hc s)
      Real.pi_pos.le)

theorem sixVertexCanonicalOddMidpointHalfRoot_quantile_lower
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth (2 * s + 1) k : Real) *
        sixVertexCanonicalOddMidpointHalfRoot hc s k j := by
  have hleft :=
    sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc
      (2 * s + 1 + k) ⟨j.val, by omega⟩
  have hright :=
    sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc
      (2 * s + 1 + k) ⟨j.val + 1, by omega⟩
  have hwidth : sixVertexFourWidth 0 (2 * s + 1 + k) =
      sixVertexFourWidth (2 * s + 1) k := by
    unfold sixVertexFourWidth
    omega
  rw [hwidth] at hleft
  rw [hwidth] at hright
  have hleft' : Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth (2 * s + 1) k : Real) *
        sixVertexCanonicalOddLeftHalfRoot hc s k j := by
    simpa [sixVertexCanonicalOddLeftHalfRoot] using hleft
  have hright' : Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth (2 * s + 1) k : Real) *
        sixVertexCanonicalOddRightHalfRoot hc s k j := by
    have := hright
    simp only [sixVertexCanonicalOddRightHalfRoot] at this ⊢
    push_cast at this
    nlinarith [Real.pi_pos]
  unfold sixVertexCanonicalOddMidpointHalfRoot
  nlinarith

theorem eventually_abs_sixVertexCanonicalOddPositiveRoot_sub_midpoint_le
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop, forall j : Fin (s + k + 1),
      |sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j -
          sixVertexCanonicalOddMidpointHalfRoot hc s k j| <=
        sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s *
          sixVertexCanonicalOddMidpointHalfRoot hc s k j /
            sixVertexFourWidth (2 * s + 1) k := by
  filter_upwards
    [eventually_abs_sixVertexCanonicalOddChargeOffset_le_linear_add hc s]
      with k hk
  intro j
  let N := sixVertexFourWidth (2 * s + 1) k
  let p := sixVertexCanonicalOddMidpointHalfRoot hc s k j
  let q := sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j
  let i := sixVertexOddPositiveIndex (s + k + 1) j
  let C := sixVertexCanonicalOddOffsetLinearBound c hc s
  let R := sixVertexCanonicalOddOffsetRemainderBound c hc s
  have hN : 0 < (N : Real) := by
    exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
  have hp : 0 < p := by
    have hquant := sixVertexCanonicalOddMidpointHalfRoot_quantile_lower hc s k j
    nlinarith [Real.pi_pos]
  have hquant := sixVertexCanonicalOddMidpointHalfRoot_quantile_lower hc s k j
  have hRp : R / N <= (R / Real.pi) * p := by
    have hR : 0 <= R := sixVertexCanonicalOddOffsetRemainderBound_nonneg hc s
    have hpiN : Real.pi < (N : Real) * p := by
      have hj0 : 0 <= (j : Real) := by positivity
      have hj : 1 <= 2 * (j : Real) + 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hj Real.pi_pos.le]
    rw [div_le_iff₀ hN]
    calc
      R <= (R / Real.pi) * ((N : Real) * p) := by
        have := mul_le_mul_of_nonneg_left hpiN.le
          (div_nonneg hR Real.pi_pos.le)
        simpa [div_mul_eq_mul_div, Real.pi_ne_zero] using this
      _ = (R / Real.pi) * p * (N : Real) := by ring
  have hi := hk i
  have haligned : sixVertexCanonicalOddAlignedHalfRoots hc s k i = p :=
    sixVertexCanonicalOddAlignedHalfRoots_positive hc s k j
  have hfixed : sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i = q :=
    rfl
  rw [sixVertexCanonicalOddChargeOffset, haligned, hfixed,
    abs_mul, abs_of_pos hN, abs_of_pos hp] at hi
  have hscaled : (N : Real) * |q - p| <=
      (C + R / Real.pi) * p := by
    calc
      (N : Real) * |q - p| <= C * p + R / N := hi
      _ <= C * p + (R / Real.pi) * p := add_le_add le_rfl hRp
      _ = (C + R / Real.pi) * p := by ring
  exact (le_div_iff₀ hN).2 (by
    simpa [sixVertexCanonicalOddEffectiveOffsetLinearBound, C, R,
      mul_comm] using hscaled)

theorem eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_simple
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s + 1) k
      let n := s + k + 1
      let C := sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s
      |∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
            sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalOddMidpointHalfRoot hc s k j))| <=
        2 * Real.pi * C * (1 / M + 1 / N) +
          epsilon * C * Real.pi * M ^ 4 / 16 := by
  let C := sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s
  have hC : 0 <= C :=
    sixVertexCanonicalOddEffectiveOffsetLinearBound_nonneg hc s
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have hwide : ∀ᶠ k : Nat in atTop,
      2 * C <= (sixVertexFourWidth (2 * s + 1) k : Real) :=
    hwidth.eventually (eventually_ge_atTop (2 * C))
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s,
      eventually_abs_sixVertexCanonicalOddPositiveRoot_sub_midpoint_le hc s,
      hwide] with k hk hdiff hNk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := s + k + 1
  let p : Fin n -> Real := sixVertexCanonicalOddMidpointHalfRoot hc s k
  let q : Fin n -> Real :=
    sixVertexCanonicalFixedOddDensityPositiveRoots hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hMreal : 0 < (M : Real) := by exact_mod_cast hM
  have hp (j : Fin n) : p j ∈ Set.Ioo 0 Real.pi := by
    have hl := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val, by dsimp [n]; omega⟩
    have hr := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val + 1, by dsimp [n]; omega⟩
    dsimp [p, sixVertexCanonicalOddMidpointHalfRoot,
      sixVertexCanonicalOddLeftHalfRoot, sixVertexCanonicalOddRightHalfRoot]
    constructor
    · change 0 < (_ + _) / 2
      linarith [hl.1, hr.1]
    · change (_ + _) / 2 < Real.pi
      linarith [hl.2, hr.2]
  have hq (j : Fin n) : q j ∈ Set.Ioo 0 Real.pi := by
    let i := sixVertexOddPositiveIndex (s + k + 1) j
    have hcentral :=
      sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
        hc s k hk
    have hindex : sixVertexOddCentralIndex (s + k + 1) < i := by
      rw [Fin.lt_def]
      dsimp [i, sixVertexOddCentralIndex, sixVertexOddPositiveIndex,
        Fin.castAdd, Fin.natAdd]
      omega
    have hpositive := hk.1.1.1 hindex
    have hqeq : sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i =
        q j := rfl
    constructor
    · rw [<- hqeq, <- hcentral]
      exact hpositive
    · rw [<- hqeq]
      exact (hk.1.1.2.2 i).2
  have hclose (j : Fin n) : |q j - p j| <= p j / 2 := by
    calc
      |q j - p j| <= C * p j / N := by simpa [q, p, C, n] using hdiff j
      _ <= p j / 2 := by
        apply (div_le_iff₀ hNreal).2
        have hp0 := (hp j).1
        have hCN : 2 * C <= (N : Real) := by simpa [N, C] using hNk
        nlinarith
  have hfar (j : Fin n) (hj : N / M + 1 <= j.val) :
      2 * Real.pi / M <= p j := by
    have hjdiv : N / M < j.val := by omega
    have hNjM : N < j.val * M := (Nat.div_lt_iff_lt_mul hM).1 hjdiv
    have hNjMreal : (N : Real) < (j.val : Real) * M := by exact_mod_cast hNjM
    have hjpos : 0 < (j.val : Real) := by exact_mod_cast
      (lt_of_lt_of_le (Nat.zero_lt_succ _) hj)
    have hquant := sixVertexCanonicalOddMidpointHalfRoot_quantile_lower hc s k j
    have hNp : (N : Real) * p j < ((j.val : Real) * M) * p j :=
      mul_lt_mul_of_pos_right hNjMreal (hp j).1
    apply (div_le_iff₀ hMreal).2
    by_contra hbad
    rw [not_le] at hbad
    have hbad' : (M : Real) * p j < 2 * Real.pi := by
      simpa [mul_comm] using hbad
    have hjbad := mul_lt_mul_of_pos_left hbad' hjpos
    nlinarith
  have hraw := abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff
    hc hepsilon (div_pos (mul_pos (by norm_num) Real.pi_pos) hMreal)
    hC hN hp hq hclose (by intro j; simpa [q, p, C, n] using hdiff j) hfar
  have hnN : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  have hcastDiv : ((N / M : Nat) : Real) <= (N : Real) / M :=
    Nat.cast_div_le
  have hfirst :
      ((N / M + 1 : Nat) : Real) * (2 * Real.pi * C / N) <=
        2 * Real.pi * C * (1 / M + 1 / N) := by
    calc
      _ = (((N / M : Nat) : Real) + 1) *
          (2 * Real.pi * C / N) := by push_cast; ring
      _ <= ((N : Real) / M + 1) * (2 * Real.pi * C / N) := by
        gcongr
      _ = _ := by field_simp [hMreal.ne', hNreal.ne']
  have hsecond :
      (n : Real) *
          ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
            (C * Real.pi / N)) <=
        epsilon * C * Real.pi * M ^ 4 / 16 := by
    calc
      _ <= (N : Real) *
          ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
            (C * Real.pi / N)) := by gcongr
      _ = _ := by
        field_simp [hMreal.ne', hNreal.ne', Real.pi_ne_zero]
        ring
  exact hraw.trans (add_le_add hfirst hsecond)

theorem eventually_abs_sixVertexCanonicalOddBulkLogDisplacement_sub_regularized_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s + 1) k
      let C := sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s
      |sixVertexCanonicalOddBulkLogDisplacement hc s k -
          sixVertexCanonicalOddRegularizedBulkLogDisplacement
            hc epsilon s k| <=
        2 * Real.pi * C * (1 / M + 1 / N) +
          epsilon * C * Real.pi * M ^ 4 / 16 := by
  filter_upwards
    [eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_simple
      hc hepsilon s hM,
      eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness
        hc s] with k hk hfixed
  let n := s + k + 1
  let q : Fin n -> Real :=
    sixVertexCanonicalFixedOddDensityPositiveRoots hc s k
  let p : Fin n -> Real := sixVertexCanonicalOddMidpointHalfRoot hc s k
  have hp (j : Fin n) : p j ∈ Set.Ioo 0 Real.pi := by
    have hl := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val, by dsimp [n]; omega⟩
    have hr := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val + 1, by dsimp [n]; omega⟩
    dsimp [p, sixVertexCanonicalOddMidpointHalfRoot,
      sixVertexCanonicalOddLeftHalfRoot, sixVertexCanonicalOddRightHalfRoot]
    constructor
    · change 0 < (_ + _) / 2
      linarith [hl.1, hr.1]
    · change (_ + _) / 2 < Real.pi
      linarith [hl.2, hr.2]
  have hq (j : Fin n) : q j ∈ Set.Ioo 0 Real.pi := by
    let i := sixVertexOddPositiveIndex (s + k + 1) j
    have hcentral :=
      sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
        hc s k hfixed
    have hindex : sixVertexOddCentralIndex (s + k + 1) < i := by
      rw [Fin.lt_def]
      dsimp [i, sixVertexOddCentralIndex, sixVertexOddPositiveIndex,
        Fin.castAdd, Fin.natAdd]
      omega
    have hpositive := hfixed.1.1.1 hindex
    have hqeq : sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i =
        q j := rfl
    constructor
    · rw [<- hqeq, <- hcentral]
      exact hpositive
    · rw [<- hqeq]
      exact (hfixed.1.1.2.2 i).2
  have heq :
      sixVertexCanonicalOddBulkLogDisplacement hc s k -
          sixVertexCanonicalOddRegularizedBulkLogDisplacement
            hc epsilon s k =
        ∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon (q j) -
            sixVertexBetheLogRegularizationError c epsilon (p j)) := by
    unfold sixVertexCanonicalOddBulkLogDisplacement
      sixVertexCanonicalOddRegularizedBulkLogDisplacement
      sixVertexBetheLogRegularizationError
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [sixVertexBetheLogObservable_eq_logNormKernel hc (hq j),
      sixVertexBetheLogObservable_eq_logNormKernel hc (hp j)]
    ring
  rw [heq]
  simpa [q, p, n] using hk

theorem tendsto_sixVertexCanonicalOddRegularizedBulkLogDisplacement
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) (s : Nat) :
    Tendsto (sixVertexCanonicalOddRegularizedBulkLogDisplacement
      hc epsilon s) atTop
      (nhds ((2 * s + 1 : Real) / 2 *
        (∫ x in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogNormDerivative c epsilon x *
            sixVertexContinuousOffsetFourier c hc x))) := by
  have h := (tendsto_sixVertexCanonicalOddPositiveRegularizedRootDisplacement
    hc s hepsilon).const_mul (1 / 2 : Real)
  convert h using 1
  · funext k
    unfold sixVertexCanonicalOddRegularizedBulkLogDisplacement
    rw [Finset.sum_sub_distrib]
    ring
  · ring

theorem tendsto_sixVertexCanonicalOddBulkLogDisplacement
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalOddBulkLogDisplacement hc s) atTop
      (nhds ((2 * s + 1 : Real) / 2 *
        (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))) := by
  let raw := sixVertexCanonicalOddBulkLogDisplacement hc s
  let reg : Nat -> Nat -> Real := fun m =>
    sixVertexCanonicalOddRegularizedBulkLogDisplacement hc
      (sixVertexLogRegularizationSchedule m) s
  let value : Nat -> Real := fun m => (2 * s + 1 : Real) / 2 *
    (∫ x in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogNormDerivative c
          (sixVertexLogRegularizationSchedule m) x *
        sixVertexContinuousOffsetFourier c hc x)
  let target : Real := (2 * s + 1 : Real) / 2 *
    (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
      sixVertexAntiferroelectricGapRate
        (sixVertexAntiferroelectricLambda c))
  have hreg (m : Nat) : Tendsto (reg m) atTop (nhds (value m)) := by
    exact tendsto_sixVertexCanonicalOddRegularizedBulkLogDisplacement hc
      (sixVertexLogRegularizationSchedule_pos m) s
  have hvalue : Tendsto value atTop (nhds target) := by
    exact (tendsto_sixVertexRegularizedLogPairing_schedule hc).const_mul
      ((2 * s + 1 : Real) / 2)
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have happrox : forall eta : Real, 0 < eta -> exists m : Nat,
      dist (value m) target < eta ∧
        ∀ᶠ k : Nat in atTop, dist (raw k) (reg m k) < eta := by
    intro eta heta
    let C := sixVertexCanonicalOddEffectiveOffsetLinearBound c hc s
    let A := 2 * Real.pi * C
    have hC : 0 <= C :=
      sixVertexCanonicalOddEffectiveOffsetLinearBound_nonneg hc s
    have hA : 0 <= A := by dsimp [A]; positivity
    obtain ⟨M0, hM0⟩ : exists M0 : Nat,
        A * (1 / ((M0 + 1 : Nat) : Real)) < eta / 3 := by
      by_cases hAzero : A = 0
      · exact ⟨0, by simp [hAzero, heta]⟩
      · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
        obtain ⟨M0, hM0⟩ := exists_nat_one_div_lt
          (show 0 < eta / (3 * A) by positivity)
        refine ⟨M0, ?_⟩
        calc
          A * (1 / ((M0 + 1 : Nat) : Real)) <
              A * (eta / (3 * A)) := by
            apply mul_lt_mul_of_pos_left _ hApos
            simpa only [Nat.cast_add, Nat.cast_one] using hM0
          _ = eta / 3 := by field_simp [hApos.ne']
    let M := M0 + 1
    have hM : 0 < M := Nat.succ_pos _
    let K := C * Real.pi * (M : Real) ^ 4 / 16
    have hK : 0 <= K := by dsimp [K]; positivity
    have hepsK : Tendsto
        (fun m => sixVertexLogRegularizationSchedule m * K) atTop
        (nhds 0) := by
      simpa using tendsto_sixVertexLogRegularizationSchedule.mul_const K
    have hevValue : ∀ᶠ m : Nat in atTop, dist (value m) target < eta :=
      hvalue.eventually (Metric.ball_mem_nhds target heta)
    have hevK : ∀ᶠ m : Nat in atTop,
        sixVertexLogRegularizationSchedule m * K < eta / 3 := by
      have hz : 0 < eta / 3 := by positivity
      filter_upwards [hepsK.eventually (Metric.ball_mem_nhds 0 hz)]
        with m hm
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg
          (sixVertexLogRegularizationSchedule_pos m).le hK)] at hm
      exact hm
    obtain ⟨m, hm⟩ := eventually_atTop.1 (hevValue.and hevK)
    have hm' := hm m le_rfl
    refine ⟨m, hm'.1, ?_⟩
    have hcut :=
      eventually_abs_sixVertexCanonicalOddBulkLogDisplacement_sub_regularized_le
        hc (sixVertexLogRegularizationSchedule_pos m) s hM
    have htail : ∀ᶠ k : Nat in atTop,
        A / (sixVertexFourWidth (2 * s + 1) k : Real) < eta / 3 := by
      have ht : Tendsto (fun k : Nat =>
          A / (sixVertexFourWidth (2 * s + 1) k : Real)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hwidth
      have hz : 0 < eta / 3 := by positivity
      filter_upwards [ht.eventually (Metric.ball_mem_nhds 0 hz)] with k hk
      have hN : 0 < (sixVertexFourWidth (2 * s + 1) k : Real) := by
        exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (div_nonneg hA hN.le)] at hk
      exact hk
    filter_upwards [hcut, htail] with k hk hkTail
    rw [Real.dist_eq]
    have hfirst : A * (1 / (M : Real)) < eta / 3 := by
      simpa [A, M] using hM0
    have hthird :
        sixVertexLogRegularizationSchedule m * C * Real.pi *
          (M : Real) ^ 4 / 16 < eta / 3 := by
      convert hm'.2 using 1 <;> dsimp [K] <;> ring
    have hbound :
        2 * Real.pi * C *
              (1 / (M : Real) +
                1 / (sixVertexFourWidth (2 * s + 1) k : Real)) +
            sixVertexLogRegularizationSchedule m * C * Real.pi *
              (M : Real) ^ 4 / 16 < eta := by
      dsimp [A] at hkTail hfirst
      calc
        _ = (2 * Real.pi * C * (1 / (M : Real))) +
            (2 * Real.pi * C /
              (sixVertexFourWidth (2 * s + 1) k : Real)) +
            sixVertexLogRegularizationSchedule m * C * Real.pi *
              (M : Real) ^ 4 / 16 := by ring
        _ < eta := by linarith
    exact hk.trans_lt hbound
  rw [Metric.tendsto_atTop]
  intro eta heta
  obtain ⟨m, hmValue, hmClose⟩ := happrox (eta / 3) (by positivity)
  obtain ⟨Kclose, hKclose⟩ := eventually_atTop.1 hmClose
  have hregm := hreg m
  rw [Metric.tendsto_atTop] at hregm
  obtain ⟨Kreg, hKreg⟩ := hregm (eta / 3) (by positivity)
  refine ⟨max Kclose Kreg, ?_⟩
  intro k hk
  have hclose := hKclose k ((le_max_left _ _).trans hk)
  have hregk := hKreg k ((le_max_right _ _).trans hk)
  exact (dist_triangle4 (raw k) (reg m k) (value m) target).trans_lt
    (by linarith)

end

end StatMech.FrontierD
