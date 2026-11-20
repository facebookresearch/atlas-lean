/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexSymmetricBetheEigenvalueValue c
    (sixVertexEvenPositiveHalfProjection (s + k + 1)
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))

def sixVertexCanonicalFixedOddDensityBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexZeroPhaseBetheEigenvalueValue c
    (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
    (sixVertexOddCentralIndex (s + k + 1))

def sixVertexCanonicalFixedEvenDensityPositiveRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) -> Real :=
  sixVertexEvenPositiveHalfProjection (s + k + 1)
    (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)

def sixVertexCanonicalFixedOddDensityPositiveRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) -> Real :=
  sixVertexOddPositiveHalfProjection (s + k + 1)
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)

theorem eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s]
      with k hk
  have hlift : sixVertexEvenSymmetricLift (s + k + 1)
      (sixVertexEvenPositiveHalfProjection (s + k + 1)
        (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)) =
      sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k :=
    sixVertexEvenSymmetricLift_projection (s + k + 1) hk.1.1.2.1
  have hpositive (j : Fin (s + k + 1)) :
      sixVertexEvenPositiveHalfProjection (s + k + 1)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) j ∈
        Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    rw [hlift]
    exact hk.1.1
  unfold sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue
  rw [<- sixVertexSymmetricBetheEigenvalueKernel_eq_value c _ hpositive]
  exact hk.1.2.2

theorem eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  exact hk.1.2.2

theorem eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq
    {c : Real} (hc : 2 < c) (s : Nat) :
    sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s =ᶠ[atTop]
      sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq_top hc s,
      eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top hc s]
      with k hkDensity hkCanonical
  rw [hkDensity, hkCanonical]

theorem eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq
    {c : Real} (hc : 2 < c) (s : Nat) :
    sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s =ᶠ[atTop]
      sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityBetheEigenvalueValue_eq_top hc s,
      eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top hc s]
      with k hkDensity hkCanonical
  rw [hkDensity, hkCanonical]

def sixVertexCanonicalFixedEvenDensityCandidateLogRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)))

def sixVertexCanonicalFixedOddDensityCandidateLogRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)))

theorem sixVertexCanonicalFixedEvenDensityCandidateLogRatio_eq
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s k =
      2 * ((∑ j, sixVertexBetheLogObservable c
          (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j)) -
        ∑ j, sixVertexBetheLogObservable c
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k) j)) := by
  unfold sixVertexCanonicalFixedEvenDensityCandidateLogRatio
    sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue
    sixVertexCanonicalFixedEvenDensityPositiveRoots
    sixVertexBetheLogObservable
  rw [sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  ring

theorem sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
      (sixVertexOddCentralIndex (s + k + 1)) = 0 := by
  have hs := hfixed.1.1.2.1 (sixVertexOddCentralIndex (s + k + 1))
  rw [sixVertexOddCentralIndex_rev] at hs
  linarith

theorem sum_erase_central_sixVertexBetheLogObservable_oddSymmetric
    (c : Real) (m : Nat) {p : Fin ((m + 1) + m) -> Real}
    (hp : SixVertexRootSymmetric p) :
    (∑ j ∈ Finset.univ.erase (sixVertexOddCentralIndex m),
        sixVertexBetheLogObservable c (p j)) =
      2 * ∑ j : Fin m, sixVertexBetheLogObservable c
        (sixVertexOddPositiveHalfProjection m p j) := by
  let q := sixVertexOddPositiveHalfProjection m p
  have hlift : sixVertexOddSymmetricLift m q = p :=
    sixVertexOddSymmetricLift_projection m hp
  rw [<- hlift]
  simp only [sixVertexOddPositiveHalfProjection_lift]
  let f : Fin ((m + 1) + m) -> Real := fun j =>
    sixVertexBetheLogObservable c (sixVertexOddSymmetricLift m q j)
  have hcentral : f (sixVertexOddCentralIndex m) = 0 := by
    rw [show f (sixVertexOddCentralIndex m) =
      sixVertexBetheLogObservable c 0 by
        simp [f, sixVertexOddSymmetricLift_central]]
    simp [sixVertexBetheLogObservable, sixVertexBetheM,
      sixVertexBethePhase]
  have herase : (∑ j ∈ Finset.univ.erase (sixVertexOddCentralIndex m), f j) =
      ∑ j, f j := by
    rw [<- Finset.sum_erase_add _ _
      (Finset.mem_univ (sixVertexOddCentralIndex m)), hcentral, add_zero]
  change (∑ j ∈ Finset.univ.erase (sixVertexOddCentralIndex m), f j) = _
  rw [herase]
  have hrev : (∑ j : Fin m, sixVertexBetheLogObservable c (q j.rev)) =
      ∑ j : Fin m, sixVertexBetheLogObservable c (q j) := by
    simpa using (Equiv.sum_comp Fin.revPerm
      (fun j : Fin m => sixVertexBetheLogObservable c (q j)))
  have hneg : (∑ j : Fin (m + 1), f (Fin.castAdd m j)) =
      ∑ j : Fin m, sixVertexBetheLogObservable c (q j) := by
    rw [Fin.sum_univ_castSucc]
    have hterms : (∑ j : Fin m, f (Fin.castAdd m j.castSucc)) =
        ∑ j : Fin m, sixVertexBetheLogObservable c (q j.rev) := by
      apply Finset.sum_congr rfl
      intro j _
      change sixVertexBetheLogObservable c
        (sixVertexOddSymmetricLift m q (sixVertexOddNegativeIndex m j)) = _
      rw [sixVertexOddSymmetricLift_negative,
        sixVertexBetheLogObservable_neg]
    rw [hterms, hrev]
    have hlast : f (Fin.castAdd m (Fin.last m)) = 0 := by
      change f (sixVertexOddCentralIndex m) = 0
      exact hcentral
    rw [hlast, add_zero]
  have hpos : (∑ j : Fin m, f (Fin.natAdd (m + 1) j)) =
      ∑ j : Fin m, sixVertexBetheLogObservable c (q j) := by
    apply Finset.sum_congr rfl
    intro j _
    change sixVertexBetheLogObservable c
      (sixVertexOddSymmetricLift m q (sixVertexOddPositiveIndex m j)) = _
    rw [sixVertexOddSymmetricLift_positive]
  rw [Fin.sum_univ_add, hneg, hpos]
  ring

theorem sixVertexCanonicalFixedOddDensityCandidateLogRatio_eq
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k =
      Real.log (sixVertexZeroPhaseBethePrefactor c
        (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
        (sixVertexOddCentralIndex (s + k + 1))) - Real.log 2 +
      2 * ((∑ j, sixVertexBetheLogObservable c
          (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j)) -
        ∑ j, sixVertexBetheLogObservable c
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc
            (2 * s + 1 + k) j)) := by
  have hcentral :=
    sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
      hc s k hfixed
  unfold sixVertexCanonicalFixedOddDensityCandidateLogRatio
    sixVertexCanonicalFixedOddDensityBetheEigenvalueValue
  rw [sixVertexZeroPhaseBetheEigenvalueValue_log hc
      (by unfold sixVertexFourWidth; omega)
      _ _ hcentral,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  have hsum :=
    sum_erase_central_sixVertexBetheLogObservable_oddSymmetric c
      (s + k + 1) hfixed.1.1.2.1
  unfold sixVertexBetheLogObservable at hsum
  rw [hsum]
  unfold sixVertexCanonicalFixedOddDensityPositiveRoots
    sixVertexBetheLogObservable
  ring

end

end StatMech.FrontierD
