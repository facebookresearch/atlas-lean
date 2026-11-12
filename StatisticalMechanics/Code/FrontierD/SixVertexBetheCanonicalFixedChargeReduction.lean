/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Code.FrontierD.SixVertexBetheEventualOddPerron
import Code.FrontierD.SixVertexBetheEvenCandidate
import Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch
import Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch









open Filter Topology

namespace StatMech.FrontierD

noncomputable section




def sixVertexFixedChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  if _hr : Even r then
    sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc (r / 2) k
  else
    sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc ((r - 1) / 2) k



def SixVertexEventuallyFixedChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexFixedChargeBetheEigenvalueValue hc r k =
      sixVertexLambdaAlongFour c r k

def SixVertexEventuallyEvenChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  ∀ᶠ k : Nat in atTop,
    sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s k =
      sixVertexLambdaAlongFour c (2 * s) k

theorem sixVertexEventuallyFixedChargeBethePerronIdentification_of_even
    {c : Real} (hc : 2 < c) (s : Nat)
    (h : SixVertexEventuallyEvenChargeBethePerronIdentification hc s) :
    SixVertexEventuallyFixedChargeBethePerronIdentification hc (2 * s) := by
  filter_upwards [h] with k hk
  unfold sixVertexFixedChargeBetheEigenvalueValue
  rw [dif_pos ⟨s, by ring⟩]
  simpa using hk

theorem sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd
    {c : Real} (hc : 2 < c) (s : Nat)
    (h : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s k =
        sixVertexLambdaAlongFour c (2 * s + 1) k) :
    SixVertexEventuallyFixedChargeBethePerronIdentification hc
      (2 * s + 1) := by
  filter_upwards [h] with k hk
  unfold sixVertexFixedChargeBetheEigenvalueValue
  rw [dif_neg (Nat.not_even_iff_odd.2 ⟨s, rfl⟩)]
  simpa using hk



theorem sixVertexEventuallyFixedChargeBethePerronIdentification
    {c : Real} (hc : 2 < c) (r : Nat) :
    SixVertexEventuallyFixedChargeBethePerronIdentification hc r := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨s, rfl⟩ := hr
    have heven : SixVertexEventuallyEvenChargeBethePerronIdentification hc s := by
      filter_upwards
        [eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top
          hc s]
      with k hk
      rw [hk]
      unfold sixVertexLambdaAlongFour sixVertexLambda sixVertexFourWidth
      congr 1 <;> omega
    simpa [two_mul] using
      (sixVertexEventuallyFixedChargeBethePerronIdentification_of_even
        hc s heven)
  · obtain ⟨s, rfl⟩ := hr
    apply sixVertexEventuallyFixedChargeBethePerronIdentification_of_odd hc s
    filter_upwards
      [eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top
        hc s]
        with k hk
    rw [hk]
    unfold sixVertexLambdaAlongFour sixVertexLambda sixVertexFourWidth
    congr 1 <;> omega



def sixVertexCanonicalFixedChargeBetheCandidateLogRatio
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  Real.log (sixVertexFixedChargeBetheEigenvalueValue hc r k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (r + k)))



def SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) : Prop :=
  Tendsto (fun k =>
      sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc r k +
        (r : Real) * sixVertexOffsetFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k)
    atTop (nhds 0)



theorem sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate
    {c : Real} (hc : 2 < c) (r : Nat)
    (hfixed : SixVertexEventuallyFixedChargeBethePerronIdentification hc r) :
    sixVertexFixedChargeLogRatio c r =ᶠ[atTop]
      sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc r := by
  have hcentralShift := (tendsto_add_atTop_nat r).eventually
    (eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue hc)
  filter_upwards [hfixed, hcentralShift] with k hkfixed hkcentral
  rw [Nat.add_comm k r] at hkcentral
  have hkcentral' :
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (r + k)) =
        sixVertexLambda (sixVertexFourWidth r k) 0
          (sixVertexFourWidth_even r k) (Nat.zero_le _) c := by
    simpa [sixVertexLambdaAlongFour, sixVertexFourWidth, Nat.add_assoc] using
      hkcentral.symm
  rw [sixVertexFixedChargeLogRatio_eq (by linarith),
    sixVertexCanonicalFixedChargeBetheCandidateLogRatio,
    ← hkfixed, ← hkcentral']



theorem sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate
    {c : Real} (hc : 2 < c) (r : Nat)
    (hfixed : SixVertexEventuallyFixedChargeBethePerronIdentification hc r) :
    SixVertexFixedChargeMatchesOffsetFourier c r ↔
      SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r := by
  apply tendsto_congr'
  filter_upwards
    [sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate
      hc r hfixed] with k hk
  rw [hk]




theorem sixVertexAntiferroelectricTransferConclusion_of_canonicalFixedCharge
    {c : Real} (hc : 2 < c)
    (hbranch : ∀ r : Nat, 1 ≤ r →
      SixVertexEventuallyFixedChargeBethePerronIdentification hc r)
    (hoffset : ∀ r : Nat, 1 ≤ r →
      SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r) :
    SixVertexAntiferroelectricTransferConclusion c
      (sixVertexAntiferroelectricLambda c) := by
  refine ⟨sixVertexBalanced_iteratedLimit_of_canonicalPerron hc, ?_⟩
  intro r hr
  apply (sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier hc r).2
  exact (sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate
    hc r (hbranch r hr)).2 (hoffset r hr)

end

end StatMech.FrontierD
