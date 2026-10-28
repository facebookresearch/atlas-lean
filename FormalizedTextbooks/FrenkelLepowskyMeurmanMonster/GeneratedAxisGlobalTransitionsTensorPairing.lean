/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorUnits
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidualLocalCoordinates

/-! Coordinate evaluation and pairing transport for genuine local tensor operators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem coordinatePairing_unit {I : Type*} [Fintype I] [DecidableEq I]
    (t : I) (i : Fin 24) (T : I → Fin 24 → ℝ) :
    tensorColumnPairing (fun u j => if u = t then if j = i then 1 else 0 else 0) T =
      T t i := by
  simp [tensorColumnPairing, ite_mul]

private theorem coordinatePairing_smul {I : Type*} [Fintype I]
    (c : ℝ) (T U : I → Fin 24 → ℝ) :
    tensorColumnPairing (c • T) U = c * tensorColumnPairing T U := by
  simp only [tensorColumnPairing, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum]

private theorem coordinatePairing_add {I : Type*} [Fintype I]
    (T U V : I → Fin 24 → ℝ) :
    tensorColumnPairing (T + U) V =
      tensorColumnPairing T V + tensorColumnPairing U V := by
  simp only [tensorColumnPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Pairing with a physical coordinate unit reads precisely that coordinate. -/
theorem generatedAxisGlobalTensorUnit_pairing (t : SpinIndex) (i : Fin 24)
    (T : SpinIndex → Fin 24 → ℝ) :
    tensorColumnPairing (generatedAxisGlobalTensorUnit t i) T = T t i :=
  coordinatePairing_unit t i T

/-- The actual local tensor action preserves the physical coordinate pairing. -/
theorem generatedAxisGlobalTensor_pairing_local (f : localFiberSubgroup)
    (T U : SpinIndex → Fin 24 → ℝ) :
    tensorColumnPairing (localTensorRepresentation f T) (localTensorRepresentation f U) =
      tensorColumnPairing T U := by
  rw [← generatedLocal_tensor_action, ← generatedLocal_tensor_action]
  exact generatedCentralizerTensorAction_pairing _ T U

/-- A signed dictionary image gives the corresponding exact pairing transport. -/
theorem generatedAxisGlobalTensor_pairing_signed (f : localFiberSubgroup)
    (T U V : SpinIndex → Fin 24 → ℝ) (c : ZMod 2)
    (h : localTensorRepresentation f U = qSign c • V) :
    tensorColumnPairing V (localTensorRepresentation f T) =
      qSign c * tensorColumnPairing U T := by
  have hp := generatedAxisGlobalTensor_pairing_local f U T
  rw [h, coordinatePairing_smul] at hp
  calc
    tensorColumnPairing V (localTensorRepresentation f T) =
        qSign c * (qSign c * tensorColumnPairing V (localTensorRepresentation f T)) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = qSign c * tensorColumnPairing U T := by rw [hp]

/-- The two-term original dictionary reads every physical tensor coordinate. -/
theorem generatedAxisGlobalTensor_dictionary_pairing (d : Fin 2048) (b : ZMod 2)
    (i : Fin 24) (T : SpinIndex → Fin 24 → ℝ) :
    Real.sqrt 2 * T (generatedFifthSpinLow d + b • (Pi.single 11 1 : SpinIndex)) i =
      (qSign b * (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
        tensorColumnPairing (trialityYTensor d i) T +
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        tensorColumnPairing (trialityZTensor d i) T := by
  have h := congrArg (fun U => tensorColumnPairing U T)
    (generatedAxisGlobalTensorUnit_dictionary d b i)
  rw [coordinatePairing_smul, generatedAxisGlobalTensorUnit_pairing,
    coordinatePairing_add, coordinatePairing_smul, coordinatePairing_smul] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
