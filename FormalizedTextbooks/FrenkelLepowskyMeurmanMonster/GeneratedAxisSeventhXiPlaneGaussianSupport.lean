/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneGaussianPackedAction

/-! Every genuine Gaussian shift preserves the actual tensor's binary support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 10000 in
-- All original full-phase Pauli shifts are retained in this support check.
/-- Every original Gaussian shift lies in the two actual support kernels. -/
theorem generatedSeventhXiGaussianPackedShift_supported : ∀ a : Fin 64,
    generatedSeventhXiTensorSupported (generatedSeventhXiGaussianPackedShift a).val := by
  decide +kernel

private theorem parity_xor (d u r : Fin 4096) :
    monsterNortonBitParity ((d.val ^^^ u.val) &&& r.val) =
      Bool.xor (monsterNortonBitParity (d.val &&& r.val))
        (monsterNortonBitParity (u.val &&& r.val)) := by
  have h := spinDot_add_left (golayLabelCoefficients d) (golayLabelCoefficients u)
    (golayLabelCoefficients r)
  rw [← monsterNortonBitXor_coeff, generatedSeventhXi_bit_dot,
    generatedSeventhXi_bit_dot, generatedSeventhXi_bit_dot] at h
  change golayBooleanCast (monsterNortonBitParity ((d.val ^^^ u.val) &&& r.val)) =
    golayBooleanCast (monsterNortonBitParity (d.val &&& r.val)) +
      golayBooleanCast (monsterNortonBitParity (u.val &&& r.val)) at h
  cases h0 : monsterNortonBitParity ((d.val ^^^ u.val) &&& r.val) <;>
    cases h1 : monsterNortonBitParity (d.val &&& r.val) <;>
      cases h2 : monsterNortonBitParity (u.val &&& r.val) <;>
        simp_all [golayBooleanCast]

/-- Adding any original Gaussian shift preserves both actual support syndromes. -/
theorem generatedSeventhXiGaussianPackedShift_support_iff (d : Fin 4096) (a : Fin 64) :
    generatedSeventhXiTensorSupported
        (monsterNortonBitXor d (generatedSeventhXiGaussianPackedShift a)).val ↔
      generatedSeventhXiTensorSupported d.val := by
  have hu := generatedSeventhXiGaussianPackedShift_supported a
  change monsterNortonBitParity ((d.val ^^^ _) &&& 1504) = false ∧
      monsterNortonBitParity ((d.val ^^^ _) &&& 1648) = false ↔ _
  rw [parity_xor d _ ⟨1504, by decide⟩, parity_xor d _ ⟨1648, by decide⟩,
    hu.1, hu.2]
  simp only [Bool.xor_false]
  rfl

/-- The full original Gaussian image is zero at every label outside the genuine tensor support. -/
theorem generatedSeventhXiPlaneGaussianPacked_tensor_zero (d : Fin 4096) (j : Fin 24)
    (hd : ¬ generatedSeventhXiTensorSupported d.val) :
    generatedSeventhXiPlaneGaussianPacked
      (fun x => generatedSeventhXiPlaneTensorPacked x j) d = 0 := by
  unfold generatedSeventhXiPlaneGaussianPacked
  apply Finset.sum_eq_zero
  intro a _
  have hx : ¬ generatedSeventhXiTensorSupported
      (monsterNortonBitXor d (generatedSeventhXiGaussianPackedShift a)).val :=
    fun h => hd ((generatedSeventhXiGaussianPackedShift_support_iff d a).mp h)
  dsimp only
  rw [generatedSeventhXiPlaneTensorPacked_zero _ j hx, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
