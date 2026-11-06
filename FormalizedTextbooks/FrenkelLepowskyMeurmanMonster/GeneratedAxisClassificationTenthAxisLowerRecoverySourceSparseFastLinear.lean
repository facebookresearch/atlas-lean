/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceSparseFastQCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Ungated exact twelve-column XOR evaluator for the original source inverse spin coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Twelve original binary columns suffice; there is no144-entry matrix evaluation per input. -/
def generatedTenthSourceSparseFastLinearMask (cols : Fin 12 → ℕ) (n : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun j : Fin 12 =>
    if n.testBit j.val then cols j else 0))

/-- Arbitrary original columns give the identical complete genuine spin coordinate matrix. -/
theorem generatedTenth_source_sparse_fast_linear_actual
    (cols : Fin 12 → ℕ) (n : Fin 4096) :
    monsterCo1GeometryBinaryMaskDecode (n := 12)
        (generatedTenthSourceSparseFastLinearMask cols n.val) =
      generatedTwelfthSpinCompactMatrix cols *ᵥ golayLabelCoefficients n := by
  unfold generatedTenthSourceSparseFastLinearMask
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  ext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases h : n.val.testBit j.val <;>
    simp [generatedTwelfthSpinCompactMatrix, golayLabelCoefficients,
      monsterCo1GeometryBinaryMaskDecode, golayBooleanCast, h]

/-- The actual source inverse coordinate map uses its held original inverse columns. -/
def generatedTenthSourceSparseFastLeftInverse (t : SpinIndex) : SpinIndex :=
  monsterCo1GeometryBinaryMaskDecode (n := 12)
    (generatedTenthSourceSparseFastLinearMask
      (generatedTenthAxisLowerRecoverySourceCompactLeftInverseColumns 0)
      (generatedAxisGlobalSpinLabel t).val)

/-- The XOR evaluator is exactly the original source's genuine inverse coordinate equivalence. -/
theorem generatedTenth_source_sparse_fast_left_inverse (t : SpinIndex) :
    generatedTenthSourceSparseFastLeftInverse t =
      (generatedTenthAxisLowerRecoverySourceCompactLeft 0).symm t := by
  unfold generatedTenthSourceSparseFastLeftInverse
  rw [generatedTenth_source_sparse_fast_linear_actual, generatedAxisGlobalSpinLabel_decode]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

