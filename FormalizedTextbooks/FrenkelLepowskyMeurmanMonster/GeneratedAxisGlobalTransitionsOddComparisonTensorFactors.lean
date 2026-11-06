/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddQTensorFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSignTensorPackets

/-! Genuine tensor transports of the three complete local comparison words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The comparison words use the original low-code dictionary signs. -/
def generatedAxisGlobalOddComparisonLowSign : Fin 3 → Fin 2048 := ![52, 6, 4]

/-- The original low-code labels agree with the literal full source sign labels. -/
theorem generatedAxisGlobalOddComparisonLowSign_actual (k : Fin 3) :
    generatedAxisGlobalSignLowCode (generatedAxisGlobalOddComparisonLowSign k) =
      generatedAxisGlobalOddComparisonSign k := by
  fin_cases k <;> rfl

/-- The complete spin factor retains both the actual source sign and the central Q correction. -/
def generatedAxisGlobalOddComparisonSpinInteger (k : Fin 3) (u : Fin 4096 → ℤ) :
    Fin 4096 → ℤ :=
  generatedAxisGlobalOddQSpinInteger (generatedAxisGlobalOddComparisonQ k)
    (generatedAxisGlobalOddSignSpinInteger (generatedAxisGlobalOddComparisonLowSign k) u)

/-- The complete spatial factor keeps the original physical coordinate signs. -/
def generatedAxisGlobalOddComparisonSpatialInteger (k : Fin 3) (v : Fin 24 → ℤ) :
    Fin 24 → ℤ :=
  generatedAxisGlobalOddSignSpatialInteger (generatedAxisGlobalOddComparisonLowSign k) v

/-- A proved complete source root packet transports through the genuine entire comparison word. -/
theorem generatedAxisGlobalOddComparisonTensor_of_root_packet
    (k : Fin 3) (u : Fin 4096 → ℤ) (v : Fin 24 → ℤ) (D : ℕ)
    (ht : localTensorRepresentation
        (generatedAxisGlobalOddSourceRootFiber (generatedAxisGlobalOddComparisonRoot k))
        ((griessConwayEncode generatedOddAxis).2.2) =
      generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor u v) D) :
    localTensorRepresentation (generatedAxisGlobalOddComparisonFiber k)
        ((griessConwayEncode generatedOddAxis).2.2) =
      generatedAxisGlobalTensorIntegerPacket
        (generatedAxisGlobalOddTensorFactor (generatedAxisGlobalOddComparisonSpinInteger k u)
          (generatedAxisGlobalOddComparisonSpatialInteger k v)) (2 * D) := by
  rw [generatedAxisGlobalOddComparisonFiber, map_mul, map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [ht, ← generatedAxisGlobalOddComparisonLowSign_actual,
    generatedAxisGlobalOddSignTensorFactor_actual, generatedAxisGlobalOddQTensorFactor_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
