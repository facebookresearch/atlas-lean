/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizer

/-! An original-code certificate for the correcting Golay permutation in the
Tenth E7 root-line move. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000

/-- Complete original coordinate data for the correcting permutation. -/
def generatedTenthE7XiForward : Fin 24 → Fin 24 :=
  ![1, 3, 7, 0, 2, 6, 4, 5, 13, 16, 8, 21, 11, 22, 14, 19, 17, 12, 20, 9, 23, 10, 18, 15]

/-- Complete original coordinate data for the correcting permutation. -/
def generatedTenthE7XiInverse : Fin 24 → Fin 24 :=
  ![3, 0, 4, 1, 6, 7, 5, 2, 10, 19, 21, 12, 17, 8, 14, 23, 9, 16, 22, 15, 18, 11, 13, 20]

/-- Complete original coordinate data for the correcting permutation. -/
def generatedTenthE7XiForwardLabels : Fin 12 → Fin 4096 :=
  ![1733, 1776, 1754, 1760, 25, 54, 125, 202, 3306, 2872, 3568, 2048]

/-- Complete original coordinate data for the correcting permutation. -/
def generatedTenthE7XiInverseLabels : Fin 12 → Fin 4096 :=
  ![1581, 1550, 1563, 1591, 10, 63, 1652, 1741, 1331, 2353, 2495, 2048]

/-- Both compositions of the complete coordinate arrays are identity. -/
theorem generatedTenth_e7_xi_inverse_certificate : ∀ i : Fin 24,
    generatedTenthE7XiForward (generatedTenthE7XiInverse i) = i ∧
      generatedTenthE7XiInverse (generatedTenthE7XiForward i) = i := by
  decide +kernel

/-- The literal inverse certificate constructs an actual coordinate permutation. -/
def generatedTenthE7XiPermutation : Equiv.Perm (Fin 24) where
  toFun := generatedTenthE7XiForward
  invFun := generatedTenthE7XiInverse
  left_inv i := (generatedTenth_e7_xi_inverse_certificate i).2
  right_inv i := (generatedTenth_e7_xi_inverse_certificate i).1

private theorem code_certificate : ∀ j : Fin 12, ∀ i : Fin 24,
    (golayGeneratorMasks j).testBit (generatedTenthE7XiInverse i).val =
      (golayEncodedMask (generatedTenthE7XiForwardLabels j).val).testBit i.val ∧
    (golayGeneratorMasks j).testBit (generatedTenthE7XiForward i).val =
      (golayEncodedMask (generatedTenthE7XiInverseLabels j).val).testBit i.val := by
  decide +kernel

private theorem label_boolean (d : Fin 4096) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients d) i =
      golayBooleanCast ((golayEncodedMask d.val).testBit i.val) := by
  apply ZMod.val_injective 2
  rw [golayLabelEncoder_match]
  have h0 : (0 : ZMod 2).val = 0 := by decide
  have h1 : (1 : ZMod 2).val = 1 := by decide
  cases h : (golayEncodedMask d.val).testBit i.val <;>
    simp only [golayBooleanCast, Bool.false_eq_true, ite_false, ite_true, h0, h1]

private theorem generator_boolean (j : Fin 12) (i : Fin 24) :
    (golayGeneratorBit j i : ZMod 2) =
      golayBooleanCast ((golayGeneratorMasks j).testBit i.val) := by
  cases h : (golayGeneratorMasks j).testBit i.val <;>
    simp only [golayGeneratorBit, golayBooleanCast, h, Bool.false_eq_true,
      ite_false, ite_true, Int.cast_zero, Int.cast_one]

private def permutationLinear (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem mem_of_generator_images (p : Equiv.Perm (Fin 24))
    (hp : ∀ j, golayPermute p (fun i => (golayGeneratorBit j i : ZMod 2)) ∈ golayCode)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) : golayPermute p c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change (permutationLinear p).comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  apply golayCode.smul_mem
  have hrow : golayEncoder (Pi.single j 1) = fun i => (golayGeneratorBit j i : ZMod 2) := by
    ext i
    simp [golayEncoder, Pi.single_apply, ite_mul]
  change golayPermute p (golayEncoder (Pi.single j 1)) ∈ golayCode
  rw [hrow]
  exact hp j

/-- Forward and inverse generator images prove preservation of the full actual Golay code. -/
def generatedTenthE7XiAutomorphism : golayAutomorphismSubgroup :=
  ⟨generatedTenthE7XiPermutation, by
    have hf (j : Fin 12) :
        golayPermute generatedTenthE7XiPermutation
          (fun i => (golayGeneratorBit j i : ZMod 2)) =
          golayEncoder (golayLabelCoefficients (generatedTenthE7XiForwardLabels j)) := by
      ext i
      change (golayGeneratorBit j (generatedTenthE7XiInverse i) : ZMod 2) = _
      rw [generator_boolean, label_boolean, (code_certificate j i).1]
    have hi (j : Fin 12) :
        golayPermute generatedTenthE7XiPermutation⁻¹
          (fun i => (golayGeneratorBit j i : ZMod 2)) =
          golayEncoder (golayLabelCoefficients (generatedTenthE7XiInverseLabels j)) := by
      ext i
      change (golayGeneratorBit j (generatedTenthE7XiForward i) : ZMod 2) = _
      rw [generator_boolean, label_boolean, (code_certificate j i).2]
    intro c
    constructor
    · intro hc
      exact mem_of_generator_images _ (fun j => by rw [hf]; exact ⟨_, rfl⟩) c hc
    · intro hc
      have h := mem_of_generator_images generatedTenthE7XiPermutation⁻¹
        (fun j => by rw [hi]; exact ⟨_, rfl⟩) _ hc
      rw [golayPermute_inv] at h
      exact h⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
