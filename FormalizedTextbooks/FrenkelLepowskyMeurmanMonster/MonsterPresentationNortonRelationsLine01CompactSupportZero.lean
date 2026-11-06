/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse-numerator vanishing from the proved finite support geometry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactSupportBitwise
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem bit_permutation_xor (k : Fin 2) (a b : Fin 4096) :
    monsterNortonUCompactBitPermutation k (monsterNortonBitXor a b) =
      monsterNortonBitXor (monsterNortonUCompactBitPermutation k a)
        (monsterNortonUCompactBitPermutation k b) := by
  have hf (n : Fin 4096) : golayLabelCoefficients (monsterNortonUCompactBitPermutation k n) =
      monsterNortonUCompactPermutation k (golayLabelCoefficients n) := by
    rw [← monsterNortonUCompactBitPermutation_actual, nortonUIntegerLabel_inverse]
  apply golayLabelCoefficients_injective
  rw [hf, monsterNortonBitXor_coeff, monsterNortonBitXor_coeff, hf, hf, map_add]

private theorem gaussian_mask (a : Fin 64) :
    monsterNortonUCompactBitPermutation 0 (monsterNortonBitGrayLabel a) =
      monsterNortonLine01CompactInputGaussianMask a := by
  revert a
  decide +kernel

private theorem preimage_eq (n : Fin 4096) :
    monsterNortonLine01CompactBitPreimage n = monsterNortonBitXor
      (monsterNortonUCompactBitPermutation 0 (monsterNortonUCompactBitPermutation 1 n)) 1024 := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 12)
    (monsterNortonUCompactBitPermutation 0 (monsterNortonUCompactBitPermutation 1 n)).isLt
      (by norm_num))

private theorem inner_input (n : Fin 4096) (a : Fin 64) :
    monsterNortonBitXor (monsterNortonUCompactBitInner n a) 1024 =
      monsterNortonBitXor (monsterNortonLine01CompactBitPreimage n)
        (monsterNortonLine01CompactInputGaussianMask a) := by
  rw [monsterNortonUCompactBitInner, bit_permutation_xor, gaussian_mask, preimage_eq]
  apply Fin.ext
  simp only [monsterNortonBitXor]
  rw [Nat.xor_assoc, Nat.xor_assoc]
  exact congrArg (fun x : ℕ =>
    (monsterNortonUCompactBitPermutation 0 (monsterNortonUCompactBitPermutation 1 n)).val ^^^ x)
      (Nat.xor_comm (monsterNortonLine01CompactInputGaussianMask a).val
        (1024 : Fin 4096).val)

private theorem support_xor (n : Fin 4096) (hn : monsterNortonLine01CompactInputSupport n)
    (a : Fin 64) : monsterNortonLine01CompactInputSupport
      (monsterNortonBitXor n (monsterNortonLine01CompactInputGaussianMask a)) := by
  let p := monsterNortonLine01CompactInputLookup n
  have he : monsterNortonLine01CompactInputLabel p = n := hn
  have h := monsterNortonLine01CompactSupport_gaussian p a
  have hx : (⟨((monsterNortonLine01CompactInputLabel p).val ^^^
      (monsterNortonLine01CompactInputGaussianMask a).val) % 4096,
        Nat.mod_lt _ (by norm_num)⟩ : Fin 4096) =
      monsterNortonBitXor (monsterNortonLine01CompactInputLabel p)
        (monsterNortonLine01CompactInputGaussianMask a) := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 12)
      (monsterNortonLine01CompactInputLabel p).isLt
        (monsterNortonLine01CompactInputGaussianMask a).isLt)
  rwa [hx, he] at h

private theorem input_outside (n : Fin 4096) (hn : ¬ monsterNortonLine01CompactOutputSupport n)
    (a : Fin 64) : ¬ monsterNortonLine01CompactInputSupport
      (monsterNortonBitXor (monsterNortonUCompactBitInner n a) 1024) := by
  intro hi
  have hs := support_xor _ hi a
  rw [inner_input] at hs
  have hx (v w : Fin 4096) : monsterNortonBitXor (monsterNortonBitXor v w) w = v := by
    apply Fin.ext
    simp [monsterNortonBitXor, Nat.xor_assoc]
  rw [hx] at hs
  exact hn ((monsterNortonLine01CompactSupport_preimage n).mpr hs)

/-- Every coordinate outside the output catalogue vanishes under the actual inverse numerator. -/
theorem monsterNortonLine01CompactInverse_bit_zero (k : Fin 16) (n : Fin 4096)
    (hn : ¬ monsterNortonLine01CompactOutputSupport n) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector k) n = 0 := by
  rw [monsterNortonUCompactBitInverseNumerator_actual]
  unfold monsterNortonUCompactBitInverseNumerator
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro a _
  have hi : monsterNortonLine01CompactInputVector k
      (monsterNortonBitXor (monsterNortonUCompactBitInner n a) 1024) = 0 := by
    exact ite_eq_right (input_outside n hn a)
  simp only [hi, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
