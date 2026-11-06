/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Exact original spin label Fourier covariance follows symbolically from genuine XOR semantics. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original twelve-coordinate Golay reader is the genuine finite binary mask decoder. -/
theorem generatedTwelfth_spin_label_decode (d : Fin 4096) :
    golayLabelCoefficients d = monsterCo1GeometryBinaryMaskDecode (n := 12) d.val := by
  funext j
  simp only [golayLabelCoefficients, monsterCo1GeometryBinaryMaskDecode]

/-- A single original source coordinate is exactly the corresponding twelve-bit unit mask. -/
theorem generatedTwelfth_spin_label_unit (k : Fin 12) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (2 ^ k.val) = Pi.single k 1 := by
  funext j
  by_cases h : k = j
  · subst j
    simp [monsterCo1GeometryBinaryMaskDecode]
  · have hv : k.val ≠ j.val := by exact fun he => h (Fin.ext he)
    simp [monsterCo1GeometryBinaryMaskDecode, hv, Ne.symm h]

/-- Every original Fourier coordinate flip is exactly its genuine twelve-bit XOR source label. -/
theorem generatedTwelfth_spin_label_xor (k : Fin 12) (n : Fin 4096) :
    nortonUIntegerLabel (golayLabelCoefficients n + Pi.single k 1) =
      ⟨(Nat.xor n.val (2 ^ k.val)) % 4096, Nat.mod_lt _ (by decide)⟩ := by
  have hp : 2 ^ k.val < 4096 := by
    change 2 ^ k.val < 2 ^ 12
    exact Nat.pow_lt_pow_right (by decide) k.isLt
  have hx : Nat.xor n.val (2 ^ k.val) < 4096 := Nat.xor_lt_two_pow (n := 12) n.isLt hp
  apply golayLabelCoefficients_injective
  rw [nortonUIntegerLabel_inverse]
  simp_rw [generatedTwelfth_spin_label_decode]
  simp only [Nat.mod_eq_of_lt hx, monsterCo1GeometryBinaryMaskDecode_xor,
    generatedTwelfth_spin_label_unit]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
