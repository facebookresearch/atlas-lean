/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinCircuit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Exact finite mask coordinates for the original six-dimensional Gaussian sum. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Six binary bits give the actual grey-space coordinate vector. -/
def generatedSixthGrayCoefficients (n : Fin 64) : XiGrayIndex :=
  monsterCo1GeometryBinaryMaskDecode n.val

set_option maxHeartbeats 2000000 in
-- Reassemble each of the 64 actual six-bit labels.
/-- Grey labels are recovered from their genuine binary coefficients. -/
theorem generatedSixth_gray_reassemble : ∀ n : Fin 64,
    (∑ i, (generatedSixthGrayCoefficients n i).val * 2 ^ i.val) = n.val := by
  decide +kernel

/-- The six-bit labels biject with the actual grey module. -/
theorem generatedSixth_gray_bijective : Function.Bijective generatedSixthGrayCoefficients := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    apply Fin.ext
    rw [← generatedSixth_gray_reassemble a, ← generatedSixth_gray_reassemble b, h]
  · simp [XiGrayIndex]

/-- The actual grey module is indexed by the 64 literal binary addresses. -/
noncomputable def generatedSixthGrayEquiv : Fin 64 ≃ XiGrayIndex :=
  Equiv.ofBijective generatedSixthGrayCoefficients generatedSixth_gray_bijective

/-- The actual grey code translation labels in the original twelve-bit coordinates. -/
def generatedSixthGrayCodeLabel : Fin 64 → Fin 4096 :=
![
  0, 1024, 3087, 2063, 3073, 2049, 14, 1038,
  3074, 2050, 13, 1037, 3, 1027, 3084, 2060,
  3076, 2052, 11, 1035, 5, 1029, 3082, 2058,
  6, 1030, 3081, 2057, 3079, 2055, 8, 1032,
  3080, 2056, 7, 1031, 9, 1033, 3078, 2054,
  10, 1034, 3077, 2053, 3083, 2059, 4, 1028,
  12, 1036, 3075, 2051, 3085, 2061, 2, 1026,
  3086, 2062, 1, 1025, 15, 1039, 3072, 2048]

/-- Integral quadratic signs of the actual six-dimensional Gaussian. -/
def generatedSixthGraySign : Fin 64 → ℤ :=
![
  1, 1, 1, -1, 1, -1, -1, -1,
  1, -1, -1, -1, -1, -1, -1, 1,
  1, -1, -1, -1, -1, -1, -1, 1,
  -1, -1, -1, 1, -1, 1, 1, 1,
  1, -1, -1, -1, -1, -1, -1, 1,
  -1, -1, -1, 1, -1, 1, 1, 1,
  -1, -1, -1, 1, -1, 1, 1, 1,
  -1, 1, 1, 1, 1, 1, 1, -1]

set_option maxHeartbeats 2000000 in
-- Check the 64 translations on all 12 original spin coordinates.
/-- Literal grey translation labels decode to the genuine grey code map. -/
theorem generatedSixth_gray_code : ∀ n : Fin 64, ∀ i : Fin 12,
    golayLabelCoefficients (generatedSixthGrayCodeLabel n) i =
      xiGrayCode (generatedSixthGrayCoefficients n) i := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check all 64 original quadratic signs.
/-- Literal Gaussian signs are the actual source signs. -/
theorem generatedSixth_gray_sign : ∀ n : Fin 64,
    generatedSixthGraySign n = xiGraySign (generatedSixthGrayCoefficients n) := by
  decide +kernel

/-- Actual twelve-bit spin labels add by literal XOR. -/
def generatedSixthSpinLabelXor (a b : Fin 4096) : Fin 4096 :=
  ⟨Nat.xor a.val b.val, Nat.xor_lt_two_pow (n := 12) a.isLt b.isLt⟩

/-- Literal XOR is genuine addition of the original spin-coordinate vectors. -/
theorem generatedSixth_spin_label_xor (a b : Fin 4096) :
    golayLabelCoefficients (generatedSixthSpinLabelXor a b) =
      golayLabelCoefficients a + golayLabelCoefficients b := by
  exact monsterCo1GeometryBinaryMaskDecode_xor a.val b.val

/-- The fast 64-term sum retains the genuine diagonal Gaussian sign at each input. -/
def generatedSixthIntegerXiFast (v : NortonUIntegerVector) (n : Fin 4096) : ℤ :=
  ∑ a : Fin 64, generatedSixthGraySign a *
    nortonUIntegerGammaSign
      (golayLabelCoefficients (generatedSixthSpinLabelXor n (generatedSixthGrayCodeLabel a))) *
    v (generatedSixthSpinLabelXor n (generatedSixthGrayCodeLabel a))

private theorem sum_gray (f : XiGrayIndex → ℤ) :
    (∑ a : XiGrayIndex, f a) = ∑ n : Fin 64, f (generatedSixthGrayCoefficients n) :=
  (Equiv.sum_comp generatedSixthGrayEquiv f).symm

/-- The fast binary-address Gaussian is the genuine original integer Gaussian. -/
theorem generatedSixth_integer_xi_fast (v : NortonUIntegerVector) :
    nortonUIntegerXi v = generatedSixthIntegerXiFast v := by
  funext n
  dsimp only [nortonUIntegerXi, nortonUIntegerG, nortonUIntegerGamma,
    generatedSixthIntegerXiFast]
  rw [sum_gray]
  apply Finset.sum_congr rfl
  intro a _
  have hc : xiGrayCode (generatedSixthGrayCoefficients a) =
      golayLabelCoefficients (generatedSixthGrayCodeLabel a) :=
    (funext (generatedSixth_gray_code a)).symm
  change xiGraySign (generatedSixthGrayCoefficients a) * _ = _
  rw [hc, ← generatedSixth_spin_label_xor, nortonUIntegerLabel_coeff,
    ← generatedSixth_gray_sign]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
