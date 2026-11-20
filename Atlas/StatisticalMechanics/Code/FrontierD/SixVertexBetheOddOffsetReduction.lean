/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheZeroPhase
import Code.FrontierD.SixVertexBetheFourierEvaluation

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeRatio_zero
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexFixedChargeRatio c 0 k = 1 := by
  unfold sixVertexFixedChargeRatio sixVertexLambdaAlongFour
  apply div_self
  exact (sixVertexLambda_isPerronFrobenius
    (sixVertexFourWidth 0 k) 0 (sixVertexFourWidth_even 0 k)
    (Nat.zero_le _) hc).1.ne'

theorem sixVertexFixedChargeLogRatio_zero
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexFixedChargeLogRatio c 0 k = 0 := by
  rw [sixVertexFixedChargeLogRatio, sixVertexFixedChargeRatio_zero hc,
    Real.log_one]



theorem sixVertexFixedChargeMatchesOffsetFourier_zero
    {c : Real} (hc : 0 < c) :
    SixVertexFixedChargeMatchesOffsetFourier c 0 := by
  simp [SixVertexFixedChargeMatchesOffsetFourier,
    sixVertexFixedChargeLogRatio_zero hc]



def sixVertexOddChargeBetheCandidateLogRatio
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  Real.log (sixVertexFixedOddChargeBetheEigenvalueValue hc r k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc (r + k)))



theorem sixVertexOddChargeBetheCandidateLogRatio_eq
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexOddChargeBetheCandidateLogRatio hc r k =
      Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k)) +
      ∑ j ∈ (Finset.univ.erase
          (sixVertexFixedChargeBetheCentralIndex r k)),
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j))‖ -
      (Real.log 2 + 2 * ∑ j,
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexPositiveHalfBetheRoots hc (r + k) j))‖) := by
  rw [sixVertexOddChargeBetheCandidateLogRatio,
    sixVertexFixedOddChargeBetheEigenvalueValue_log hc hr k,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]



def SixVertexOddChargeBethePerronIdentification
    (c : Real) (r : Nat) : Prop :=
  ∀ hc : 2 < c, ∀ k,
    sixVertexFixedOddChargeBetheEigenvalueValue hc r k =
      sixVertexLambdaAlongFour c r k



def SixVertexOddChargeBetheCandidateMatchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  Tendsto (fun k => sixVertexOddChargeBetheCandidateLogRatio hc r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)

theorem sixVertexFourWidth_zero_add (r k : Nat) :
    sixVertexFourWidth 0 (r + k) = sixVertexFourWidth r k := by
  unfold sixVertexFourWidth
  omega

theorem sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron
    {c : Real} (hc : 2 < c) (r k : Nat)
    (hhalf : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc)) :
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc (r + k)) =
      sixVertexLambda (sixVertexFourWidth r k) 0
        (sixVertexFourWidth_even r k) (Nat.zero_le _) c := by
  have h := hhalf (r + k)
  unfold sixVertexPositiveHalfBetheRootFamily at h
  unfold sixVertexLambdaAlongFour at h
  simpa only [sixVertexFourWidth_zero_add r k, Nat.sub_zero] using h.symm



theorem sixVertexFixedChargeLogRatio_eq_oddBetheCandidate
    {c : Real} (hc : 2 < c) {r : Nat} (k : Nat)
    (hhalf : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc))
    (hodd : SixVertexOddChargeBethePerronIdentification c r) :
    sixVertexFixedChargeLogRatio c r k =
      sixVertexOddChargeBetheCandidateLogRatio hc r k := by
  rw [sixVertexFixedChargeLogRatio_eq (by linarith),
    sixVertexOddChargeBetheCandidateLogRatio,
    ← hodd hc k,
    ← sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron
      hc r k hhalf]




theorem sixVertexFixedChargeMatchesOffsetFourier_iff_oddBetheCandidate
    {c : Real} (hc : 2 < c) {r : Nat}
    (hhalf : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc))
    (hodd : SixVertexOddChargeBethePerronIdentification c r) :
    SixVertexFixedChargeMatchesOffsetFourier c r ↔
      SixVertexOddChargeBetheCandidateMatchesOffsetFourier hc r := by
  apply tendsto_congr'
  filter_upwards [] with k
  rw [sixVertexFixedChargeLogRatio_eq_oddBetheCandidate hc k hhalf hodd]

end

end StatMech.FrontierD
