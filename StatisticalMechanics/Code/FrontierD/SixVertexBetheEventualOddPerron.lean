/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheEventualPerron
import Code.FrontierD.SixVertexBetheOddOffsetReduction

open Filter Topology

namespace StatMech.FrontierD

noncomputable section



def SixVertexEventuallyOddChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexFixedOddChargeBetheEigenvalueValue hc r k =
      sixVertexLambdaAlongFour c r k

theorem sixVertexEventuallyOddChargeBethePerronIdentification_of_all
    {c : Real} (hc : 2 < c) (r : Nat)
    (h : SixVertexOddChargeBethePerronIdentification c r) :
    SixVertexEventuallyOddChargeBethePerronIdentification hc r :=
  Eventually.of_forall (h hc)



theorem sixVertexFixedChargeLogRatio_eventuallyEq_oddBetheCandidate
    {c : Real} (hc : 2 < c) (r : Nat)
    (hhalf : SixVertexEventuallyHasSymmetricBetheIdentification hc)
    (hodd : SixVertexEventuallyOddChargeBethePerronIdentification hc r) :
    sixVertexFixedChargeLogRatio c r =ᶠ[atTop]
      sixVertexOddChargeBetheCandidateLogRatio hc r := by
  have hhalfShift := (tendsto_add_atTop_nat r).eventually hhalf
  filter_upwards [hhalfShift, hodd] with k hkhalf hkodd
  rw [sixVertexFixedChargeLogRatio_eq (by linarith),
    sixVertexOddChargeBetheCandidateLogRatio, ← hkodd]
  rw [Nat.add_comm k r] at hkhalf
  have hkhalf' :
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc (r + k)) =
        sixVertexLambda (sixVertexFourWidth r k) 0
          (sixVertexFourWidth_even r k) (Nat.zero_le _) c := by
    simpa [sixVertexLambdaAlongFour, sixVertexFourWidth, Nat.add_assoc] using
      hkhalf.symm
  rw [← hkhalf']



theorem sixVertexFixedChargeMatchesOffsetFourier_iff_eventualOddBetheCandidate
    {c : Real} (hc : 2 < c) (r : Nat)
    (hhalf : SixVertexEventuallyHasSymmetricBetheIdentification hc)
    (hodd : SixVertexEventuallyOddChargeBethePerronIdentification hc r) :
    SixVertexFixedChargeMatchesOffsetFourier c r ↔
      SixVertexOddChargeBetheCandidateMatchesOffsetFourier hc r := by
  apply tendsto_congr'
  filter_upwards
    [sixVertexFixedChargeLogRatio_eventuallyEq_oddBetheCandidate
      hc r hhalf hodd] with k hk
  rw [hk]

end

end StatMech.FrontierD
