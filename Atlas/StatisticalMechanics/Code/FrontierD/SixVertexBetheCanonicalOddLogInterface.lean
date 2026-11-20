/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition










namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalOddBulkLogDisplacement
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∑ j, (sixVertexBetheLogObservable c
      (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
    sixVertexBetheLogObservable c
      (sixVertexCanonicalOddMidpointHalfRoot hc s k j))

def sixVertexCanonicalOddZeroModeWallisCorrection
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexZeroPhaseBethePrefactor c
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
      (sixVertexOddCentralIndex (s + k + 1))) - Real.log 2 +
    2 * ∑ j, (sixVertexBetheLogObservable c
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
      sixVertexBetheLogObservable c
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))

def sixVertexCanonicalOddBoundaryLogSum
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∑ i, sixVertexBetheLogObservable c
    (sixVertexCanonicalOddBoundaryHalfRoot hc s k i)

theorem eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density
    {c : Real} (hc : 2 < c) (s : Nat) :
    (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc
      (2 * s + 1) k) =ᶠ[atTop]
      sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq hc s]
      with k hk
  unfold sixVertexCanonicalFixedChargeBetheCandidateLogRatio
    sixVertexFixedChargeBetheEigenvalueValue
    sixVertexCanonicalFixedOddDensityCandidateLogRatio
  rw [dif_neg (Nat.not_even_iff_odd.2 ⟨s, rfl⟩)]
  have hindex : (2 * s + 1 - 1) / 2 = s := by omega
  rw [hindex, <- hk]

theorem eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k =
        sixVertexCanonicalOddZeroModeWallisCorrection hc s k +
          2 * sixVertexCanonicalOddBulkLogDisplacement hc s k -
          2 * sixVertexCanonicalOddBoundaryLogSum hc s k := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  rw [sixVertexCanonicalFixedOddDensityCandidateLogRatio_decomposition
    hc s k hk]
  simp only [sixVertexCanonicalOddZeroModeWallisCorrection,
    sixVertexCanonicalOddBulkLogDisplacement,
    sixVertexCanonicalOddBoundaryLogSum]
  ring


def SixVertexCanonicalOddZeroModeWallisLimit
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  Tendsto (sixVertexCanonicalOddZeroModeWallisCorrection hc s) atTop
    (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))))



theorem sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits
    {c : Real} (hc : 2 < c) (s : Nat)
    (hbulk : Tendsto (sixVertexCanonicalOddBulkLogDisplacement hc s) atTop
      (nhds (((2 * s + 1 : Nat) : Real) / 2 *
        (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))))
    (hwallis : SixVertexCanonicalOddZeroModeWallisLimit hc s)
    (hboundary : Tendsto (sixVertexCanonicalOddBoundaryLogSum hc s) atTop
      (nhds ((s + 1 : Nat) *
        Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))))) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc
      (2 * s + 1) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hdensity : Tendsto
      (sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s) atTop
      (nhds (-((2 * s + 1 : Nat) : Real) *
        sixVertexAntiferroelectricGapRate lam)) := by
    have hcomb := hwallis.add (hbulk.const_mul 2) |>.sub
      (hboundary.const_mul 2)
    have hdecomp :=
      (eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition
        hc s).mono fun k hk => hk.symm
    have hdensity' := hcomb.congr' hdecomp
    have hvalue :
        Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
            2 * (((2 * s + 1 : Nat) : Real) / 2 *
              (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
                sixVertexAntiferroelectricGapRate
                  (sixVertexAntiferroelectricLambda c))) -
            2 * ((s + 1 : Nat) *
              Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))) =
          -((2 * s + 1 : Nat) : Real) *
            sixVertexAntiferroelectricGapRate lam := by
      dsimp [lam]
      push_cast
      ring
    rw [hvalue] at hdensity'
    exact hdensity'
  have hcanonical : Tendsto
      (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc
        (2 * s + 1) k) atTop
      (nhds (-((2 * s + 1 : Nat) : Real) *
        sixVertexAntiferroelectricGapRate lam)) :=
    hdensity.congr'
      (eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density hc s).symm
  unfold SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier
  have hpartial := (sixVertexOffsetFourierPartialSum_tendsto
    (sixVertexAntiferroelectricLambda_pos hc)).const_mul
      ((2 * s + 1 : Nat) : Real)
  have hadd := hcanonical.add hpartial
  have hzero :
      -((2 * s + 1 : Nat) : Real) *
          sixVertexAntiferroelectricGapRate lam +
        ((2 * s + 1 : Nat) : Real) *
          sixVertexAntiferroelectricGapRate lam = 0 := by ring
  rw [hzero] at hadd
  simpa [lam] using hadd

end

end StatMech.FrontierD
