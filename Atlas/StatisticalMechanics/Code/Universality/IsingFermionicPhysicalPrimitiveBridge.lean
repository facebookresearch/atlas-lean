/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredBoundaryRay
import Code.Universality.IsingFermionicPrimitiveIntegration










namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquareWiredPrimitiveIncrement
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Real :=
  isingPrimitiveIncrement
    ((fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z)

theorem fkIsingSquareWiredDirectedPhase_normSq
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    Complex.normSq (fkIsingSquareWiredDirectedPhase n hn z) = 1 := by
  unfold fkIsingSquareWiredDirectedPhase
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp [fkIsingSquareWiredDirectedPhase]



theorem fkIsingSquareWired_tangent_mul_observable_sq_eq_increment
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredDirectedTangent n hn z *
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z ^ 2 =
      (fkIsingSquareWiredPrimitiveIncrement n hn z : Complex) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let phase := fkIsingSquareWiredDirectedPhase n hn z
  have hphase : ∀ omega, z ∈ D.exploration omega →
      D.windingPhase omega z ^ 2 = phase ^ 2 := by
    intro omega hz
    apply fkIsingSquareWired_windingPhase_sq n hn omega z
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [D, fkIsingSquareWiredDobrushinDomain] using hz
  have hobs := D.fermionicObservable_eq_signedExplorationMass_mul_phase
    z phase hphase
  have hnorm : Complex.normSq phase = 1 := by
    simpa only [phase] using
      fkIsingSquareWiredDirectedPhase_normSq n hn z
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [hobs]
  let mass := D.signedExplorationMass z phase
  change fkIsingSquareWiredDirectedTangent n hn z *
      ((mass : Complex) * phase) ^ 2 =
    (Complex.normSq ((mass : Complex) * phase) : Complex)
  calc
    fkIsingSquareWiredDirectedTangent n hn z *
        ((mass : Complex) * phase) ^ 2 =
      (mass : Complex) ^ 2 *
        (fkIsingSquareWiredDirectedTangent n hn z * phase ^ 2) := by ring
    _ = (mass : Complex) ^ 2 := by
      rw [fkIsingSquareWiredDirectedTangent_mul_phase_sq]
      ring
    _ = (Complex.normSq ((mass : Complex) * phase) : Complex) := by
      rw [Complex.normSq_mul, hnorm, mul_one]
      simp [Complex.normSq_apply]
      ring

theorem fkIsingSquareWiredPrimitiveIncrement_nonneg
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    0 ≤ fkIsingSquareWiredPrimitiveIncrement n hn z := by
  exact Complex.normSq_nonneg _



theorem fkIsingSquareWiredPrimitiveIncrement_le_one
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredPrimitiveIncrement n hn z ≤ 1 := by
  have hnorm :=
    (fkIsingSquareWiredDobrushinDomain n hn).norm_fermionicObservable_le_one z
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg
    ((fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z)]



theorem fkIsingSquareWiredPrimitiveIncrement_mem_Icc
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredPrimitiveIncrement n hn z ∈ Set.Icc 0 1 :=
  ⟨fkIsingSquareWiredPrimitiveIncrement_nonneg n hn z,
    fkIsingSquareWiredPrimitiveIncrement_le_one n hn z⟩

end

end StatMech.Universality
