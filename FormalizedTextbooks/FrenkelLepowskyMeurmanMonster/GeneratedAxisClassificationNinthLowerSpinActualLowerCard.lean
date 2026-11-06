/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinActualLowerAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineLowerAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

/-! The actual source-generated Conway subgroup has at least512×181440 elements. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original-coordinate binary action conjugates the actual source group by genuine T. -/
def generatedNinthLowerSpinActualBinaryAction : generatedNinthLowerSpinActualGroup →*
    ((Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) where
  toFun g := leechBinaryAction generatedNinthAffineTransport * co1BinaryAction g.val *
    (leechBinaryAction generatedNinthAffineTransport)⁻¹
  map_one' := by simp
  map_mul' g h := by
    simp only [Subgroup.coe_mul, map_mul]
    simp only [mul_assoc, inv_mul_cancel_left]

/-- Pull back the genuine binary linear action, retaining the original section coordinates. -/
instance generatedNinthLowerSpinActualBinaryMulAction :
    MulAction generatedNinthLowerSpinActualGroup (Fin 24 → ZMod 2) :=
  MulAction.compHom (Fin 24 → ZMod 2) generatedNinthLowerSpinActualBinaryAction

/-- Conjugation by the genuine source transport recovers each exact original whole source word. -/
theorem generatedNinth_lower_spin_actual_generator_binary (i : Fin 11) :
    generatedNinthLowerSpinActualBinaryAction (generatedNinthLowerSpinActualGroupGenerator i) =
      leechBinaryAction (generatedNinthAffineLowerSourceIsometry i) := by
  change leechBinaryAction generatedNinthAffineTransport *
    leechBinaryAction (generatedNinthAffineLowerTransportedIsometry i) *
      (leechBinaryAction generatedNinthAffineTransport)⁻¹ = _
  rw [generatedNinthAffineLowerTransportedIsometry, map_mul, map_mul, map_inv]
  simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

/-- The first nine actual source generators supply the entire original binary kernel orbit. -/
def generatedNinthLowerSpinActualKernelGenerator (j : Fin 9) :
    generatedNinthLowerSpinActualGroup :=
  generatedNinthLowerSpinActualGroupGenerator ⟨j.val, by omega⟩

/-- The last two actual source generators supply the entire alternating permutation image. -/
def generatedNinthLowerSpinActualImageGenerator (j : Fin 2) :
    generatedNinthLowerSpinActualGroup :=
  generatedNinthLowerSpinActualGroupGenerator ⟨j.val + 9, by omega⟩

/-- Every actual kernel source fixes all nine complete actual direction submodules. -/
theorem generatedNinth_lower_spin_actual_kernel_permutation (j : Fin 9) :
    generatedNinthLowerSpinActualPermutationHom (generatedNinthLowerSpinActualKernelGenerator j) =
      1 := by
  rw [generatedNinthLowerSpinActualKernelGenerator,
    generatedNinth_lower_spin_actual_generator_permutation]
  simp only [generatedNinthAffineLowerFiberPermutation, j.isLt, ↓reduceDIte]

/-- All original twenty-four coordinates of every genuine kernel source action are preserved. -/
theorem generatedNinth_lower_spin_actual_kernel_binary (j : Fin 9) (v : ℕ) :
    generatedNinthLowerSpinActualKernelGenerator j •
        monsterCo1GeometryBinaryMaskDecode (n := 24) v =
      monsterCo1GeometryBinaryMaskDecode
        (sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns j) v) := by
  change generatedNinthLowerSpinActualBinaryAction
    (generatedNinthLowerSpinActualGroupGenerator ⟨j.val, by omega⟩)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) v) = _
  rw [generatedNinth_lower_spin_actual_generator_binary]
  exact generatedNinth_affine_lower_kernel_packed j v

/-- The entire two-generator finite image is the original proved alternating image. -/
theorem generatedNinth_lower_spin_actual_image_permutation (j : Fin 2) :
    generatedNinthLowerSpinActualPermutationHom (generatedNinthLowerSpinActualImageGenerator j) =
      generatedNinthAffineAlternatingPermutation j := by
  rw [generatedNinthLowerSpinActualImageGenerator,
    generatedNinth_lower_spin_actual_generator_permutation]
  simp only [generatedNinthAffineLowerFiberPermutation,
    show ¬(j.val + 9 < 9) by omega, ↓reduceDIte, Nat.add_sub_cancel]

/-- The actual source-generated Conway subgroup has at least512×181440 elements. -/
theorem generatedNinth_lower_spin_actual_group_card_lower :
    92897280 ≤ Nat.card generatedNinthLowerSpinActualGroup := by
  let : Finite Co1 := co1_finite
  exact generatedNinth_affine_full_group_card_lower
    generatedNinthLowerSpinActualPermutationHom generatedNinthLowerSpinActualKernelGenerator
    generatedNinthLowerSpinActualImageGenerator
    generatedNinth_lower_spin_actual_kernel_permutation
    generatedNinth_lower_spin_actual_kernel_binary
    generatedNinth_lower_spin_actual_image_permutation

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
