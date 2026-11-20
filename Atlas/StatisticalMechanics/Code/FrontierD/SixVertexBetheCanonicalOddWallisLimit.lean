/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge
import Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed
import Code.FrontierD.SixVertexBetheCanonicalOddAveragedDensityEndpoints








namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

private def sixVertexCanonicalOddFixedHalfIncrementSum
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  2 * ∑ j : Fin (s + k + 1),
    (sixVertexBetheDesingularizedLogObservable c
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
      sixVertexBetheDesingularizedLogObservable c
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))

private theorem tendsto_sixVertexCanonicalOddFixedHalfIncrementSum
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalOddFixedHalfIncrementSum hc s) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
        Real.log Real.pi - Real.log (c ^ 2))) := by
  exact tendsto_sixVertexCanonicalOddFixedHalfIncrement hc s

private def sixVertexCanonicalOddAveragedHalfIncrementSum
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  2 * ∑ j : Fin (s + k + 1),
    (Real.log (sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
      Real.log (sixVertexCanonicalOddCountingAverage hc s k
        (sixVertexCanonicalOddLeftHalfRoot hc s k j)))

private theorem tendsto_sixVertexCanonicalOddAveragedHalfIncrementSum
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalOddAveragedHalfIncrementSum hc s) atTop
      (nhds (Real.log (1 / (4 * Real.pi)) -
        Real.log (sixVertexFourierPhysicalDensity c hc 0))) := by
  exact tendsto_sixVertexCanonicalOddAveragedDensityHalfIncrement hc s

private theorem eventually_sixVertexCanonicalOddSmoothWallisLog_eq
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k in atTop,
      sixVertexCanonicalOddSmoothWallisLog hc s k =
        sixVertexCanonicalOddFixedHalfIncrementSum hc s k +
          sixVertexCanonicalOddAveragedHalfIncrementSum hc s k := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hlower : 0 < lower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hfloor := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  filter_upwards [hfloor] with k hk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let F := sixVertexBetheCountingFunction c N n p
  let rho := sixVertexFiniteRootDensity c N n p
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hpSymm : SixVertexRootSymmetric p :=
    (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
      (2 * s + 1 + k)).2.1
  have hF : ∀ x, HasDerivAt F (rho x) x := fun x =>
    hasDerivAt_sixVertexBetheCountingFunction hc hN p x
  have hF0 : F 0 = 0 :=
    sixVertexBetheCountingFunction_zero_of_symmetric c N hpSymm
  have hrho : Continuous rho := continuous_sixVertexFiniteRootDensity hc N n p
  have hdensity : ∀ x, lower <= rho x := by
    simpa [lower, rho, N, n, p, sixVertexFourWidth] using hk
  have haveragePos (x : Real) (hx : 0 < x) : 0 < F x / x :=
    hlower.trans_le (primitive_div_id_lower hF hF0 hrho hx
      (fun y => hdensity y))
  have hsplit (x : Real) (hx : x ∈ Set.Ioo (0 : Real) Real.pi) :
      sixVertexBetheLogObservable c x + Real.log (F x) =
        sixVertexBetheDesingularizedLogObservable c x +
          Real.log (sixVertexCanonicalOddCountingAverage hc s k x) := by
    have hpos := haveragePos x hx.1
    have hFne : F x ≠ 0 := by
      intro hzero
      rw [hzero, zero_div] at hpos
      linarith
    rw [sixVertexBetheDesingularizedLogObservable_eq hc hx]
    change sixVertexBetheLogObservable c x + Real.log (F x) =
      sixVertexBetheLogObservable c x + Real.log x + Real.log (F x / x)
    rw [Real.log_div hFne hx.1.ne']
    ring
  have hleftMem (j : Fin (s + k + 1)) :
      sixVertexCanonicalOddLeftHalfRoot hc s k j ∈
        Set.Ioo (0 : Real) Real.pi := by
    dsimp [sixVertexCanonicalOddLeftHalfRoot]
    exact sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val, by omega⟩
  have hmidMem (j : Fin (s + k + 1)) :
      sixVertexCanonicalOddMidpointHalfRoot hc s k j ∈
        Set.Ioo (0 : Real) Real.pi := by
    have hl := hleftMem j
    have hr := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val + 1, by omega⟩
    dsimp [sixVertexCanonicalOddMidpointHalfRoot,
      sixVertexCanonicalOddLeftHalfRoot,
      sixVertexCanonicalOddRightHalfRoot] at hl hr ⊢
    constructor <;> nlinarith [hl.1, hl.2, hr.1, hr.2]
  calc
    sixVertexCanonicalOddSmoothWallisLog hc s k =
        2 * ∑ j : Fin (s + k + 1),
          ((sixVertexBetheDesingularizedLogObservable c
                (sixVertexCanonicalOddMidpointHalfRoot hc s k j) +
              Real.log (sixVertexCanonicalOddCountingAverage hc s k
                (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) -
            (sixVertexBetheDesingularizedLogObservable c
                (sixVertexCanonicalOddLeftHalfRoot hc s k j) +
              Real.log (sixVertexCanonicalOddCountingAverage hc s k
                (sixVertexCanonicalOddLeftHalfRoot hc s k j)))) := by
      dsimp [sixVertexCanonicalOddSmoothWallisLog, N, n, p, F]
      congr 2
      funext j
      rw [← hsplit _ (hmidMem j), ← hsplit _ (hleftMem j)]
    _ = sixVertexCanonicalOddFixedHalfIncrementSum hc s k +
          sixVertexCanonicalOddAveragedHalfIncrementSum hc s k := by
      dsimp [sixVertexCanonicalOddFixedHalfIncrementSum,
        sixVertexCanonicalOddAveragedHalfIncrementSum]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring

theorem sixVertexCanonicalOddSmoothWallisLimit
    {c : Real} (hc : 2 < c) (s : Nat) :
    SixVertexCanonicalOddSmoothWallisLimit hc s := by
  let rho0 := sixVertexFourierPhysicalDensity c hc 0
  let ch := Real.cosh (sixVertexAntiferroelectricLambda c)
  have hfixed := tendsto_sixVertexCanonicalOddFixedHalfIncrementSum hc s
  have havg := tendsto_sixVertexCanonicalOddAveragedHalfIncrementSum hc s
  have hsum := hfixed.add havg
  have hch : 0 < ch := Real.cosh_pos _
  have hc0 : 0 < c := by linarith
  have hrho : 0 < rho0 := sixVertexFourierPhysicalDensity_pos hc 0
  have hlimit :
      (Real.log ch + Real.log Real.pi - Real.log (c ^ 2)) +
          (Real.log (1 / (4 * Real.pi)) - Real.log rho0) =
        Real.log (ch / (4 * c ^ 2 * rho0)) := by
    rw [Real.log_div hch.ne'
        (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hc0)) hrho).ne',
      Real.log_mul (mul_pos (by norm_num) (sq_pos_of_pos hc0)).ne' hrho.ne',
      Real.log_mul (by norm_num : (4 : Real) ≠ 0) (sq_pos_of_pos hc0).ne',
      Real.log_div one_ne_zero
        (mul_pos (by norm_num) Real.pi_pos).ne',
      Real.log_one,
      Real.log_mul (by norm_num : (4 : Real) ≠ 0) Real.pi_ne_zero]
    ring
  rw [hlimit] at hsum
  unfold SixVertexCanonicalOddSmoothWallisLimit
  apply hsum.congr'
  exact (eventually_sixVertexCanonicalOddSmoothWallisLog_eq hc s).mono
    (fun k hk => hk.symm)

theorem sixVertexCanonicalOddGeneralizedWallisComparison
    {c : Real} (hc : 2 < c) (s : Nat) :
    SixVertexCanonicalOddGeneralizedWallisComparison hc s :=
  sixVertexCanonicalOddGeneralizedWallisComparison_of_smooth hc s
    (sixVertexCanonicalOddSmoothWallisLimit hc s)

theorem sixVertexCanonicalOddZeroModeWallisLimit
    {c : Real} (hc : 2 < c) (s : Nat) :
    SixVertexCanonicalOddZeroModeWallisLimit hc s :=
  sixVertexCanonicalOddZeroModeWallisLimit_of_comparison hc s
    (sixVertexCanonicalOddGeneralizedWallisComparison hc s)

theorem sixVertexCanonicalFixedOddCharge_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (s : Nat) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc
      (2 * s + 1) :=
  sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_comparison hc s
    (sixVertexCanonicalOddGeneralizedWallisComparison hc s)

theorem sixVertexCanonicalFixedCharge_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨s, rfl⟩ := hr
    simpa [two_mul] using
      sixVertexCanonicalFixedEvenCharge_matchesOffsetFourier hc s
  · obtain ⟨s, rfl⟩ := hr
    exact sixVertexCanonicalFixedOddCharge_matchesOffsetFourier hc s

theorem sixVertexAntiferroelectricTransferConclusion
    {c : Real} (hc : 2 < c) :
    SixVertexAntiferroelectricTransferConclusion c
      (sixVertexAntiferroelectricLambda c) := by
  exact sixVertexAntiferroelectricTransferConclusion_of_canonicalFixedCharge
    hc
    (fun r _ => sixVertexEventuallyFixedChargeBethePerronIdentification hc r)
    (fun r _ => sixVertexCanonicalFixedCharge_matchesOffsetFourier hc r)

theorem sixVertexAntiferroelectricTransferConclusion_of_parameter
    {c lam : Real} (hc : 2 < c) (hlam : 0 < lam)
    (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2) :
    SixVertexAntiferroelectricTransferConclusion c lam := by
  rw [sixVertexAntiferroelectricLambda_unique hlam hcosh]
  exact sixVertexAntiferroelectricTransferConclusion hc

end

end StatMech.FrontierD
