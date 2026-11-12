/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeRoots

open Finset

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedEvenChargeBetheParticleCount_eq (s k : Nat) :
    sixVertexFixedChargeBetheParticleCount (2 * s) k =
      (s + k + 1) + (s + k + 1) := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega



def sixVertexFixedEvenChargeBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin ((s + k + 1) + (s + k + 1)) -> Real :=
  fun i => sixVertexFixedChargeBetheRoots hc (2 * s) k
    (Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i)

def sixVertexFixedEvenPositiveBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) -> Real :=
  fun j => sixVertexFixedEvenChargeBetheRoots hc s k
    (Fin.natAdd (s + k + 1) j)

theorem sixVertexFixedEvenChargeBetheRoots_symmetric
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexRootSymmetric (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  intro i
  have hsymm := (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k).2.1
    (Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i)
  have hind :
      Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i.rev =
        (Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm i).rev := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  unfold sixVertexFixedEvenChargeBetheRoots
  rw [hind, hsymm]

theorem prod_sixVertexFixedEvenChargeBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) (f : Real -> Complex) :
    (∏ i, f (sixVertexFixedChargeBetheRoots hc (2 * s) k i)) =
      (∏ j, f (sixVertexFixedEvenPositiveBetheRoots hc s k j)) *
        ∏ j, f (-sixVertexFixedEvenPositiveBetheRoots hc s k j) := by
  let m := s + k + 1
  let p := sixVertexFixedEvenChargeBetheRoots hc s k
  let q := sixVertexFixedEvenPositiveBetheRoots hc s k
  have hreindex :
      (∏ i, f (sixVertexFixedChargeBetheRoots hc (2 * s) k i)) =
        ∏ i, f (p i) := by
    let e : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) ≃
        Fin (m + m) := (Fin.castOrderIso
          (sixVertexFixedEvenChargeBetheParticleCount_eq s k)).toEquiv
    apply Fintype.prod_equiv e
    intro i
    congr 2
  have hsymm := sixVertexFixedEvenChargeBetheRoots_symmetric hc s k
  have hfirst : (∏ i : Fin m, f (p (Fin.castAdd m i))) =
      ∏ i : Fin m, f (-q i) := by
    calc
      (∏ i : Fin m, f (p (Fin.castAdd m i))) =
          ∏ i : Fin m, f (-q i.rev) := by
        apply Finset.prod_congr rfl
        intro i _
        have hi := hsymm (Fin.castAdd m i).rev
        rw [Fin.rev_rev] at hi
        change p (Fin.castAdd m i) = -p (Fin.castAdd m i).rev at hi
        rw [hi]
        congr 2
        simp [q, sixVertexFixedEvenPositiveBetheRoots, p,
          sixVertexFixedEvenChargeBetheRoots, m, Fin.rev_castAdd]
      _ = ∏ i : Fin m, f (-q i) := by
        simpa using (Equiv.prod_comp Fin.revPerm (fun i => f (-q i)))
  rw [hreindex]
  change (∏ i, f (p i)) = _
  rw [Fin.prod_univ_add, hfirst]
  change (∏ i, f (-q i)) * (∏ i, f (q i)) =
    (∏ i, f (q i)) * ∏ i, f (-q i)
  rw [mul_comm]

theorem sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexBetheEigenvalueCandidate c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) =
      sixVertexSymmetricBetheEigenvalueCandidate c
        (sixVertexFixedEvenPositiveBetheRoots hc s k) := by
  unfold sixVertexBetheEigenvalueCandidate
    sixVertexSymmetricBetheEigenvalueCandidate
  rw [prod_sixVertexFixedEvenChargeBetheRoots hc s k
      (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    prod_sixVertexFixedEvenChargeBetheRoots hc s k
      (fun r => sixVertexBetheM c (sixVertexBethePhase r)),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]

def sixVertexFixedEvenChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexSymmetricBetheEigenvalueValue c
    (sixVertexFixedEvenPositiveBetheRoots hc s k)

theorem sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexBetheEigenvalueCandidate c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) =
      (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k : Complex) := by
  rw [sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric hc s k,
    sixVertexSymmetricBetheEigenvalueCandidate_eq_value]
  rfl

theorem sixVertexFixedEvenChargeBetheEigenvalueValue_pos
    {c : Real} (hc : 2 < c) (s k : Nat) :
    0 < sixVertexFixedEvenChargeBetheEigenvalueValue hc s k := by
  exact sixVertexSymmetricBetheEigenvalueValue_pos hc _



theorem sixVertexFixedEvenChargeBetheRoots_eigenrelation_value
    {c : Real} (hc : 2 < c) (s k : Nat) :
    (sixVertexSectorTransferComplex (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k) c).mulVec
        (sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)) =
      (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k : Complex) •
        sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k) := by
  have h := sixVertexFixedChargeBetheRoots_physicalEigenrelation_of_even_charge
    hc (r := 2 * s) ⟨s, by omega⟩ k
  unfold SixVertexCoordinateBetheEigenrelation at h
  rwa [sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value hc s k] at h

theorem sixVertexFixedEvenChargeBetheEigenvalueValue_log
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Real.log (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k) =
      Real.log 2 + 2 * ∑ j,
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRoots hc s k j))‖ := by
  exact sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc _


def sixVertexEvenChargeBetheCandidateLogRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc (2 * s + k)))

theorem sixVertexEvenChargeBetheCandidateLogRatio_eq
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexEvenChargeBetheCandidateLogRatio hc s k =
      2 * ((∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRoots hc s k j))‖) -
        ∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexPositiveHalfBetheRoots hc (2 * s + k) j))‖) := by
  rw [sixVertexEvenChargeBetheCandidateLogRatio,
    sixVertexFixedEvenChargeBetheEigenvalueValue_log hc,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  ring

end

end StatMech.FrontierD
