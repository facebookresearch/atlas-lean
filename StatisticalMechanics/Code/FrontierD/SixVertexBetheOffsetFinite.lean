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



def sixVertexEvenChargeHalfIndex (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    Fin (((2 * s + k + 1) + (2 * s + k + 1))) :=
  ⟨j.val + s, by
    have hj := j.isLt
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s) k
    omega⟩



def sixVertexOddChargeLowerHalfIndex (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    Fin (((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))) :=
  ⟨j.val + s, by
    have hj := j.isLt
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
    omega⟩



def sixVertexOddChargeUpperHalfIndex (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    Fin (((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))) :=
  ⟨j.val + s + 1, by
    have hj := j.isLt
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
    omega⟩

theorem sixVertexEvenChargeHalfIndex_quantum (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexCentralQuantumNumber (sixVertexEvenChargeHalfIndex s k j) =
      sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexEvenChargeHalfIndex, Fin.val_mk]
  have hcount : (sixVertexFixedChargeBetheParticleCount (2 * s) k : Real) =
      (2 * s + 2 * (k + 1) : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheParticleCount_eq (2 * s) k
  rw [hcount]
  push_cast
  ring

theorem sixVertexOddChargeHalfIndex_quantum_average (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    (sixVertexCentralQuantumNumber (sixVertexOddChargeLowerHalfIndex s k j) +
        sixVertexCentralQuantumNumber
          (sixVertexOddChargeUpperHalfIndex s k j)) / 2 =
      sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq,
    sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexOddChargeLowerHalfIndex,
    sixVertexOddChargeUpperHalfIndex, Fin.val_mk]
  have hcount :
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k : Real) =
        (2 * s + 1 + 2 * (k + 1) : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
  rw [hcount]
  push_cast
  ring



def sixVertexEvenChargeBetheOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) : Real :=
  (sixVertexFourWidth (2 * s) k : Real) *
    (sixVertexFixedChargeBetheRoots hc (2 * s) k j -
      sixVertexHalfFilledBetheRoots hc (2 * s + k)
        (sixVertexEvenChargeHalfIndex s k j))



def sixVertexOddChargeBetheOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) : Real :=
  (sixVertexFourWidth (2 * s + 1) k : Real) *
    (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j -
      (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeLowerHalfIndex s k j) +
        sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
          (sixVertexOddChargeUpperHalfIndex s k j)) / 2)



theorem sixVertexEvenChargeBetheOffset_eq_thetaDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexEvenChargeBetheOffset hc s k j =
      (∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRoots hc (2 * s + k)
            (sixVertexEvenChargeHalfIndex s k j))
          (sixVertexHalfFilledBetheRoots hc (2 * s + k) l)) -
        ∑ l, sixVertexTheta c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k j)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k l) := by
  have hfixed := sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k j
  have hhalf : SixVertexSatisfiesBetheEquations c
      (sixVertexFourWidth (2 * s) k)
      ((2 * s + k + 1) + (2 * s + k + 1))
      (sixVertexHalfFilledBetheRoots hc (2 * s + k)) := by
    simpa [sixVertexFourWidth] using
      sixVertexHalfFilledBetheRoots_is_solution hc (2 * s + k)
  have hhalf := hhalf (sixVertexEvenChargeHalfIndex s k j)
  rw [sixVertexEvenChargeHalfIndex_quantum] at hhalf
  unfold sixVertexEvenChargeBetheOffset
  linarith



theorem sixVertexOddChargeBetheOffset_eq_thetaDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    sixVertexOddChargeBetheOffset hc s k j =
      ((∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
            (sixVertexOddChargeLowerHalfIndex s k j))
          (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) l)) +
        (∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)
            (sixVertexOddChargeUpperHalfIndex s k j))
          (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) l))) / 2 -
        ∑ l, sixVertexTheta c
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) := by
  have hfixed := sixVertexFixedChargeBetheRoots_is_solution hc
    (2 * s + 1) k j
  have hhalf : SixVertexSatisfiesBetheEquations c
      (sixVertexFourWidth (2 * s + 1) k)
      ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
      (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) := by
    simpa [sixVertexFourWidth] using
      sixVertexHalfFilledBetheRoots_is_solution hc (2 * s + 1 + k)
  have hlower := hhalf (sixVertexOddChargeLowerHalfIndex s k j)
  have hupper := hhalf (sixVertexOddChargeUpperHalfIndex s k j)
  have hquantum := sixVertexOddChargeHalfIndex_quantum_average s k j
  have hquantum' :
      2 * Real.pi * sixVertexCentralQuantumNumber j =
        (2 * Real.pi * sixVertexCentralQuantumNumber
            (sixVertexOddChargeLowerHalfIndex s k j) +
          2 * Real.pi * sixVertexCentralQuantumNumber
            (sixVertexOddChargeUpperHalfIndex s k j)) / 2 := by
    rw [← hquantum]
    ring
  unfold sixVertexOddChargeBetheOffset
  linarith



theorem sixVertexOddChargeBetheOffset_central_eq_zero
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexOddChargeBetheOffset hc s k
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) = 0 := by
  let j := sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k
  let il := sixVertexOddChargeLowerHalfIndex s k j
  let iu := sixVertexOddChargeUpperHalfIndex s k j
  have hjval : j.val = s + k + 1 := by
    dsimp [j, sixVertexFixedChargeBetheCentralIndex]
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega
  have hrev : il.rev = iu := by
    apply Fin.ext
    dsimp only [il, iu, sixVertexOddChargeLowerHalfIndex,
      sixVertexOddChargeUpperHalfIndex]
    simp only [Fin.rev, Fin.val_mk]
    rw [hjval]
    omega
  have hhalf := (sixVertexHalfFilledBetheRoots_mem_open hc
    (2 * s + 1 + k)).2.1 il
  rw [hrev] at hhalf
  have hfixed := sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge
    (r := 2 * s + 1) hc ⟨s, rfl⟩ k
  unfold sixVertexOddChargeBetheOffset
  change (sixVertexFourWidth (2 * s + 1) k : Real) *
    (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k j -
      (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) il +
        sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) iu) / 2) = 0
  rw [hfixed, hhalf]
  ring

end

end StatMech.FrontierD
