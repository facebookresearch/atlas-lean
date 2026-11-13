/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheSelectedPerron

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexFixedChargeBetheParticleCount (r k : Nat) : Nat :=
  sixVertexFourWidth r k / 2 - r

@[simp] theorem sixVertexFixedChargeBetheParticleCount_eq (r k : Nat) :
    sixVertexFixedChargeBetheParticleCount r k = r + 2 * (k + 1) := by
  unfold sixVertexFixedChargeBetheParticleCount sixVertexFourWidth
  omega

theorem sixVertexFixedChargeBetheParticleCount_pos (r k : Nat) :
    0 < sixVertexFixedChargeBetheParticleCount r k := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  omega

theorem sixVertexFixedChargeBetheParticleCount_twice_le (r k : Nat) :
    2 * sixVertexFixedChargeBetheParticleCount r k <=
      sixVertexFourWidth r k := by
  rw [sixVertexFixedChargeBetheParticleCount_eq]
  unfold sixVertexFourWidth
  omega


def sixVertexFixedChargeBetheRoots
    {c : Real} (hc : 2 < c) (r k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  sixVertexChosenBetheSolution hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)

theorem sixVertexFixedChargeBetheRoots_mem_open
    {c : Real} (hc : 2 < c) (r k : Nat) :
    SixVertexOpenRootSimplex (sixVertexFixedChargeBetheRoots hc r k) := by
  exact sixVertexChosenBetheSolution_mem_open hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)

theorem sixVertexFixedChargeBetheRoots_is_solution
    {c : Real} (hc : 2 < c) (r k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)
      (sixVertexFixedChargeBetheRoots hc r k) := by
  exact sixVertexChosenBetheSolution_is_solution hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)

theorem sixVertexFixedChargeBetheRoots_is_multiplicativeSolution
    {c : Real} (hc : 2 < c) (r k : Nat) :
    SixVertexSatisfiesMultiplicativeBetheEquations c (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)
      (sixVertexFixedChargeBetheRoots hc r k) :=
  (sixVertexFixedChargeBetheRoots_is_solution hc r k).multiplicative

theorem sixVertexFixedChargeBetheRoots_sum_eq_zero
    {c : Real} (hc : 2 < c) (r k : Nat) :
    ∑ j, sixVertexFixedChargeBetheRoots hc r k j = 0 := by
  exact (sixVertexFixedChargeBetheRoots_is_solution hc r k).sum_eq_zero
    (sixVertexFourWidth_pos r k)




theorem sixVertexFixedChargeBetheRoot_add_empiricalTheta_eq_quantum
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeBetheRoots hc r k j +
        (∑ l, sixVertexTheta c (sixVertexFixedChargeBetheRoots hc r k j)
          (sixVertexFixedChargeBetheRoots hc r k l)) /
          (sixVertexFourWidth r k : Real) =
      2 * Real.pi * sixVertexCentralQuantumNumber j /
        (sixVertexFourWidth r k : Real) := by
  have hroot := sixVertexFixedChargeBetheRoots_is_solution hc r k j
  have hN : (sixVertexFourWidth r k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos r k).ne'
  field_simp [hN]
  linarith

theorem sixVertexFixedChargeBetheRoots_quantumSpacing
    {c : Real} (hc : 2 < c) (r k : Nat)
    {i j : Fin (sixVertexFixedChargeBetheParticleCount r k)} (hij : i < j) :
    2 * Real.pi *
        (sixVertexCentralQuantumNumber j - sixVertexCentralQuantumNumber i) <
      (sixVertexFourWidth r k : Real) *
        (sixVertexFixedChargeBetheRoots hc r k j -
          sixVertexFixedChargeBetheRoots hc r k i) := by
  exact sixVertexBetheSolution_quantumSpacing hc
    (sixVertexFixedChargeBetheRoots_mem_open hc r k)
    (sixVertexFixedChargeBetheRoots_is_solution hc r k) hij



theorem sixVertexFixedChargeBetheParticleDensity_tendsto_half (r : Nat) :
    Tendsto (fun k : Nat =>
      (sixVertexFixedChargeBetheParticleCount r k : Real) /
        (sixVertexFourWidth r k : Real)) atTop (nhds (1 / 2 : Real)) := by
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop := by
    exact (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hoffset : Tendsto (fun k : Nat =>
      (r : Real) / (sixVertexFourWidth r k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hidentity : (fun k : Nat =>
      (sixVertexFixedChargeBetheParticleCount r k : Real) /
        (sixVertexFourWidth r k : Real)) =
      fun k => (1 / 2 : Real) -
        (r : Real) / (sixVertexFourWidth r k : Real) := by
    funext k
    rw [sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    have hden : (4 : Real) * ((r : Real) + (k : Real) + 1) ≠ 0 := by
      positivity
    field_simp [hden]
    ring
  rw [hidentity]
  simpa using (tendsto_const_nhds.sub hoffset)



theorem sixVertexFixedChargeBetheRoots_phase_ne_one_of_even_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Even r) (k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j) ≠ 1 := by
  have hopen := sixVertexFixedChargeBetheRoots_mem_open hc r k
  intro hphase
  have hphase0 :
      sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j) =
        sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using hphase
  have hjzero := sixVertexBethePhase_injective_on_Ioo (hopen.2.2 j)
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0
  have hrevzero : sixVertexFixedChargeBetheRoots hc r k j.rev = 0 := by
    rw [hopen.2.1, hjzero, neg_zero]
  have hjrev : j.rev = j := hopen.1.injective (hrevzero.trans hjzero.symm)
  have hval := congrArg Fin.val hjrev
  simp only [Fin.rev, Fin.val_mk] at hval
  rcases hr with ⟨s, hs⟩
  have hcount : sixVertexFixedChargeBetheParticleCount r k =
      2 * (s + k + 1) := by
    rw [sixVertexFixedChargeBetheParticleCount_eq, hs]
    omega
  omega



theorem sixVertexFixedChargeBetheRoots_physicalEigenrelation_of_even_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Even r) (k : Nat) :
    SixVertexCoordinateBetheEigenrelation (N := sixVertexFourWidth r k) c
      (sixVertexFixedChargeBetheRoots hc r k) := by
  exact SixVertexSatisfiesMultiplicativeBetheEquations.physicalCoordinateBetheEigenrelation_of_pos
    hc (sixVertexFixedChargeBetheParticleCount_pos r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheRoots_is_multiplicativeSolution hc r k)
    (sixVertexFixedChargeBetheRoots_phase_ne_one_of_even_charge hc hr k)



def sixVertexFixedChargeBetheCentralIndex (r k : Nat) :
    Fin (sixVertexFixedChargeBetheParticleCount r k) :=
  ⟨sixVertexFixedChargeBetheParticleCount r k / 2,
    Nat.div_lt_self (sixVertexFixedChargeBetheParticleCount_pos r k)
      (by omega)⟩




theorem sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexFixedChargeBetheRoots hc r k
      (sixVertexFixedChargeBetheCentralIndex r k) = 0 := by
  let i := sixVertexFixedChargeBetheCentralIndex r k
  have hi : i.rev = i := by
    apply Fin.ext
    simp only [Fin.rev, Fin.val_mk]
    dsimp [i, sixVertexFixedChargeBetheCentralIndex]
    rcases hr with ⟨s, rfl⟩
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega
  have hsymm := (sixVertexFixedChargeBetheRoots_mem_open hc r k).2.1 i
  rw [hi] at hsymm
  linarith

theorem sixVertexFixedChargeBetheRoots_central_phase_eq_one_of_odd_charge
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k
      (sixVertexFixedChargeBetheCentralIndex r k)) = 1 := by
  rw [sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k]
  simp [sixVertexBethePhase]

end

end StatMech.FrontierD
