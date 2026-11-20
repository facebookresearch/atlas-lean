/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedOddChargeBetheParticleCount_eq (s k : Nat) :
    sixVertexFixedChargeBetheParticleCount (2 * s + 1) k =
      ((s + k + 1) + 1) + (s + k + 1) := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega

def sixVertexFixedOddChargeBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (((s + k + 1) + 1) + (s + k + 1)) → Real :=
  fun i => sixVertexFixedChargeBetheRoots hc (2 * s + 1) k
    (Fin.cast (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm i)

def sixVertexFixedOddPositiveBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) → Real :=
  fun j => sixVertexFixedOddChargeBetheRoots hc s k
    (sixVertexOddPositiveIndex (s + k + 1) j)

theorem sixVertexFixedOddChargeBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexOpenRootSimplex (sixVertexFixedOddChargeBetheRoots hc s k) := by
  let e : Fin (((s + k + 1) + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) :=
    (Fin.castOrderIso
      (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm).toEquiv
  have h := sixVertexFixedChargeBetheRoots_mem_open hc (2 * s + 1) k
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact h.1 (by simpa [e] using hij)
  · intro i
    have hs := h.2.1 (e i)
    have hrev : e i.rev = (e i).rev := by
      apply Fin.ext
      simp [e, Fin.rev]
      omega
    unfold sixVertexFixedOddChargeBetheRoots
    change sixVertexFixedChargeBetheRoots hc (2 * s + 1) k (e i.rev) = _
    rw [hrev]
    exact hs
  · intro i
    exact h.2.2 (e i)

theorem sixVertexFixedOddChargeBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1))
      (sixVertexFixedOddChargeBetheRoots hc s k) := by
  let e : Fin (((s + k + 1) + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) :=
    (Fin.castOrderIso
      (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm).toEquiv
  intro j
  have hj := sixVertexFixedChargeBetheRoots_is_solution hc (2 * s + 1) k (e j)
  have hquantum : sixVertexCentralQuantumNumber (e j) =
      sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [e]
    ring
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
    fun l => sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)
  have hsum : (∑ l, f l) = ∑ l, f (e l) := by
    simpa using (Equiv.sum_comp e f).symm
  rw [hquantum] at hj
  rw [show (∑ l, sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)) =
        ∑ l, f l by rfl, hsum] at hj
  simpa [sixVertexFixedOddChargeBetheRoots, e, f] using hj

def sixVertexFixedOddChargeBetheContinuationPoint
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (s k : Nat) : SixVertexBetheContinuationSpace a b
      (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1)) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  let p := sixVertexFixedOddChargeBetheRoots hc2 s k
  refine ⟨(c, p), hc, ?_, ?_⟩
  · exact (sixVertexFixedOddChargeBetheRoots_mem_open hc2 s k).toClosed
  · exact (sixVertexBetheUpdate_eq_self_iff
      (sixVertexFourWidth_pos (2 * s + 1) k) p).mpr
      (sixVertexFixedOddChargeBetheRoots_is_solution hc2 s k)

@[simp] theorem sixVertexFixedOddChargeBetheContinuationPoint_projection
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexFixedOddChargeBetheContinuationPoint ha hc s k) = ⟨c, hc⟩ := rfl

theorem sixVertexFiniteRootDensity_fixedOddCharge_eq
    {c : Real} (hc : 2 < c) (s k : Nat) (x : Real) :
    sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexFixedOddChargeBetheRoots hc s k) x =
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x := by
  let e : Fin (((s + k + 1) + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) :=
    (Fin.castOrderIso
      (sixVertexFixedOddChargeBetheParticleCount_eq s k).symm).toEquiv
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) → Real :=
    fun j => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) /
      sixVertexThetaDerivativeDenominator c x
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)
  have hsum : (∑ j, f j) = ∑ j, f (e j) := by
    simpa using (Equiv.sum_comp e f).symm
  have heqsum : (∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
      (sixVertexFixedOddChargeBetheRoots hc s k j) /
        sixVertexThetaDerivativeDenominator c x
          (sixVertexFixedOddChargeBetheRoots hc s k j)) =
      ∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) /
          sixVertexThetaDerivativeDenominator c x
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j) := by
    simpa [sixVertexFixedOddChargeBetheRoots, e, f] using hsum.symm
  unfold sixVertexFiniteRootDensity
  rw [heqsum]

theorem sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq
    {c : Real} (hc : 2 < c) (s k : Nat) (rho : C(Real, Real)) :
    sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexFixedOddChargeBetheRoots hc s k) rho =
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) rho := by
  unfold sixVertexWeightedFiniteDensityGauge
  congr 1
  apply ContinuousMap.ext
  intro x
  simp only [sixVertexWeightedFiniteDensityDifference, ContinuousMap.coe_mk]
  rw [sixVertexFiniteRootDensity_fixedOddCharge_eq hc s k x]

theorem tendsto_sixVertexFixedOddChargeContinuationGauge_tail
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (s : Nat) :
    Tendsto (fun k : Nat =>
      sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexFixedOddChargeBetheContinuationPoint ha hc s k))
      atTop (nhds 0) := by
  have h := tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail
    (ha.trans_le hc.1) htail (2 * s + 1)
  apply h.congr'
  filter_upwards with k
  symm
  change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc.1)
      (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1))
      (sixVertexFixedOddChargeBetheRoots (ha.trans_le hc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hc⟩) = _
  rw [sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq]
  congr 2

end

end StatMech.FrontierD
