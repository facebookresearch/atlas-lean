/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron
import Code.FrontierD.SixVertexBetheRootOffsetAbstract








namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalEvenHalfIndex (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    Fin ((2 * s + k + 1) + (2 * s + k + 1)) :=
  ⟨s + j, by omega⟩

def sixVertexCanonicalEvenAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
    (sixVertexCanonicalEvenHalfIndex s k j)

def sixVertexCanonicalEvenChargeOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  (sixVertexFourWidth (2 * s) k : Real) *
    (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j -
      sixVertexCanonicalEvenAlignedHalfRoots hc s k j)

def sixVertexCanonicalEvenOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  (∑ l, sixVertexTheta c
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
      (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) l)) -
    ∑ l, sixVertexTheta c
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k l)

def sixVertexCanonicalEvenOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) : Real :=
  let N := sixVertexFourWidth (2 * s) k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  eps j - sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
    (1 / (N : Real)) * ∑ l,
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

theorem sixVertexCanonicalEvenHalfIndex_quantum
    (s k : Nat) (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCentralQuantumNumber (sixVertexCanonicalEvenHalfIndex s k j) =
      sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexCanonicalEvenHalfIndex, Fin.val_mk]
  push_cast
  ring

theorem sixVertexCanonicalEvenChargeOffset_eq_thetaDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenChargeOffset hc s k j =
      (∑ l, sixVertexTheta c
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k) l)) -
        ∑ l, sixVertexTheta c
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) := by
  let N := sixVertexFourWidth (2 * s) k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)
  have hfixedEq := hfixed.2.1 j
  have hhalfEq :=
    sixVertexCanonicalDensityPerronBetheRoots_is_solution hc (2 * s + k)
      (sixVertexCanonicalEvenHalfIndex s k j)
  have hwidth : sixVertexFourWidth 0 (2 * s + k) = N := by
    dsimp [N]
    unfold sixVertexFourWidth
    omega
  rw [hwidth, sixVertexCanonicalEvenHalfIndex_quantum] at hhalfEq
  change (N : Real) * q j =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ l, sixVertexTheta c (q j) (q l) at hfixedEq
  change (N : Real) * p (sixVertexCanonicalEvenHalfIndex s k j) =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ l, sixVertexTheta c
        (p (sixVertexCanonicalEvenHalfIndex s k j)) (p l) at hhalfEq
  unfold sixVertexCanonicalEvenChargeOffset
    sixVertexCanonicalEvenAlignedHalfRoots
  linarith

theorem sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenChargeOffset hc s k j =
      sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
        ∑ l, (sixVertexTheta c
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k j)
          (sixVertexCanonicalEvenAlignedHalfRoots hc s k l) -
        sixVertexTheta c
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l)) := by
  rw [sixVertexCanonicalEvenChargeOffset_eq_thetaDifference hc s k hfixed j]
  unfold sixVertexCanonicalEvenOffsetBoundarySource
  rw [sum_sub_distrib]
  ring

theorem abs_sixVertexCanonicalEvenOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    {B : Real} (hB : 0 <= B)
    (hoffset : forall j, |sixVertexCanonicalEvenChargeOffset hc s k j| <= B)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    |sixVertexCanonicalEvenOffsetNodalResidual hc s k j| <=
      4 * sixVertexThetaTaylorBound c * B ^ 2 /
        sixVertexFourWidth (2 * s) k := by
  let N := sixVertexFourWidth (2 * s) k
  let p := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s) k
  have hn : (s + k + 1) + (s + k + 1) <= N := by
    dsimp [N]
    unfold sixVertexFourWidth
    omega
  apply abs_genericOffsetNodalResidual_le hc hN hn hB
    (p := p) (q := q) (eps := eps)
    (boundary := sixVertexCanonicalEvenOffsetBoundarySource hc s k)
  · intro l
    rfl
  · exact hoffset
  · intro l
    have h := sixVertexCanonicalEvenChargeOffset_eq_boundary_add_commonDifference
      hc s k hfixed l
    change eps l - sixVertexCanonicalEvenOffsetBoundarySource hc s k l = _
    linarith

def sixVertexCanonicalOddLowerHalfIndex (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    Fin ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) :=
  ⟨s + j, by omega⟩

def sixVertexCanonicalOddUpperHalfIndex (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    Fin ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) :=
  ⟨s + 1 + j, by omega⟩

def sixVertexCanonicalOddAlignedHalfRoots
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      (sixVertexCanonicalOddLowerHalfIndex s k j) +
    sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
      (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2

def sixVertexCanonicalOddChargeOffset
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  (sixVertexFourWidth (2 * s + 1) k : Real) *
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j -
      sixVertexCanonicalOddAlignedHalfRoots hc s k j)

def sixVertexCanonicalOddOffsetBoundarySource
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let xL := p (sixVertexCanonicalOddLowerHalfIndex s k j)
  let xU := p (sixVertexCanonicalOddUpperHalfIndex s k j)
  ((∑ l, sixVertexTheta c xL (p l)) +
    (∑ l, sixVertexTheta c xU (p l))) / 2 -
      ∑ l, sixVertexTheta c
        (sixVertexCanonicalOddAlignedHalfRoots hc s k j)
        (sixVertexCanonicalOddAlignedHalfRoots hc s k l)

def sixVertexCanonicalOddOffsetNodalResidual
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) : Real :=
  let N := sixVertexFourWidth (2 * s + 1) k
  let p := sixVertexCanonicalOddAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalOddChargeOffset hc s k
  eps j - sixVertexCanonicalOddOffsetBoundarySource hc s k j +
    (1 / (N : Real)) * ∑ l,
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l)

theorem sixVertexCanonicalOddHalfIndex_quantum_average
    (s k : Nat) (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    (sixVertexCentralQuantumNumber (sixVertexCanonicalOddLowerHalfIndex s k j) +
      sixVertexCentralQuantumNumber (sixVertexCanonicalOddUpperHalfIndex s k j)) /
        2 = sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq,
    sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexCanonicalOddLowerHalfIndex,
    sixVertexCanonicalOddUpperHalfIndex, Fin.val_mk]
  push_cast
  ring

theorem sixVertexCanonicalOddChargeOffset_eq_thetaDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddChargeOffset hc s k j =
      ((∑ l, sixVertexTheta c
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
            (sixVertexCanonicalOddLowerHalfIndex s k j))
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) l)) +
        (∑ l, sixVertexTheta c
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
            (sixVertexCanonicalOddUpperHalfIndex s k j))
          (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) l))) / 2 -
        ∑ l, sixVertexTheta c
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  have hfixedEq := hfixed.2.1 j
  have hhalf := sixVertexCanonicalDensityPerronBetheRoots_is_solution hc
    (2 * s + 1 + k)
  have hL := hhalf (sixVertexCanonicalOddLowerHalfIndex s k j)
  have hU := hhalf (sixVertexCanonicalOddUpperHalfIndex s k j)
  have hwidth : sixVertexFourWidth 0 (2 * s + 1 + k) = N := by
    dsimp [N]
    unfold sixVertexFourWidth
    omega
  rw [hwidth] at hL hU
  have hquantum := sixVertexCanonicalOddHalfIndex_quantum_average s k j
  have hquantumScaled :
      2 * Real.pi * sixVertexCentralQuantumNumber j =
        (2 * Real.pi *
            sixVertexCentralQuantumNumber (sixVertexCanonicalOddLowerHalfIndex s k j) +
          2 * Real.pi *
            sixVertexCentralQuantumNumber (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2 := by
    rw [<- hquantum]
    ring
  unfold sixVertexCanonicalOddChargeOffset
    sixVertexCanonicalOddAlignedHalfRoots
  change (N : Real) * q j =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ l, sixVertexTheta c (q j) (q l) at hfixedEq
  change (N : Real) * p (sixVertexCanonicalOddLowerHalfIndex s k j) =
    2 * Real.pi *
      sixVertexCentralQuantumNumber (sixVertexCanonicalOddLowerHalfIndex s k j) -
      ∑ l, sixVertexTheta c
        (p (sixVertexCanonicalOddLowerHalfIndex s k j)) (p l) at hL
  change (N : Real) * p (sixVertexCanonicalOddUpperHalfIndex s k j) =
    2 * Real.pi *
      sixVertexCentralQuantumNumber (sixVertexCanonicalOddUpperHalfIndex s k j) -
      ∑ l, sixVertexTheta c
        (p (sixVertexCanonicalOddUpperHalfIndex s k j)) (p l) at hU
  change (N : Real) *
      (q j - (p (sixVertexCanonicalOddLowerHalfIndex s k j) +
        p (sixVertexCanonicalOddUpperHalfIndex s k j)) / 2) =
    ((∑ l, sixVertexTheta c
        (p (sixVertexCanonicalOddLowerHalfIndex s k j)) (p l)) +
      (∑ l, sixVertexTheta c
        (p (sixVertexCanonicalOddUpperHalfIndex s k j)) (p l))) / 2 -
      ∑ l, sixVertexTheta c (q j) (q l)
  linarith

theorem sixVertexCanonicalOddChargeOffset_eq_boundary_add_commonDifference
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddChargeOffset hc s k j =
      sixVertexCanonicalOddOffsetBoundarySource hc s k j +
        ∑ l, (sixVertexTheta c
          (sixVertexCanonicalOddAlignedHalfRoots hc s k j)
          (sixVertexCanonicalOddAlignedHalfRoots hc s k l) -
        sixVertexTheta c
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l)) := by
  rw [sixVertexCanonicalOddChargeOffset_eq_thetaDifference hc s k hfixed j]
  unfold sixVertexCanonicalOddOffsetBoundarySource
  dsimp only
  rw [sum_sub_distrib]
  ring

theorem abs_sixVertexCanonicalOddOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    {B : Real} (hB : 0 <= B)
    (hoffset : forall j, |sixVertexCanonicalOddChargeOffset hc s k j| <= B)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    |sixVertexCanonicalOddOffsetNodalResidual hc s k j| <=
      4 * sixVertexThetaTaylorBound c * B ^ 2 /
        sixVertexFourWidth (2 * s + 1) k := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let p := sixVertexCanonicalOddAlignedHalfRoots hc s k
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalOddChargeOffset hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hn : ((s + k + 1) + 1) + (s + k + 1) <= N := by
    dsimp [N]
    unfold sixVertexFourWidth
    omega
  apply abs_genericOffsetNodalResidual_le hc hN hn hB
    (p := p) (q := q) (eps := eps)
    (boundary := sixVertexCanonicalOddOffsetBoundarySource hc s k)
  · intro l
    rfl
  · exact hoffset
  · intro l
    have h := sixVertexCanonicalOddChargeOffset_eq_boundary_add_commonDifference
      hc s k hfixed l
    change eps l - sixVertexCanonicalOddOffsetBoundarySource hc s k l = _
    linarith

end

end StatMech.FrontierD
