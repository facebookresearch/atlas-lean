/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiCombinedMaskPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Ordinary folded XOR evaluates the exact parity of thirty-two coefficient bits. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A selected bit is read as its literal characteristic-two scalar. -/
def generatedSixthXiBitScalar (n j : ℕ) : ZMod 2 := if n.testBit j then 1 else 0

/-- XOR is scalar addition at any selected original bit. -/
theorem generatedSixth_xi_bit_scalar_xor (n m j : ℕ) :
    generatedSixthXiBitScalar (Nat.xor n m) j =
      generatedSixthXiBitScalar n j + generatedSixthXiBitScalar m j := by
  exact congrFun (monsterCo1GeometryBinaryMaskDecode_xor (n := j + 1) n m)
    ⟨j, Nat.lt_succ_self j⟩

/-- Right shift reads the same original coefficient at the translated bit position. -/
theorem generatedSixth_xi_bit_scalar_shift (n d j : ℕ) :
    generatedSixthXiBitScalar (n >>> d) j = generatedSixthXiBitScalar n (d + j) := by
  simp only [generatedSixthXiBitScalar, Nat.testBit_shiftRight]

/-- Five folded shifts compute the parity of the original low thirty-two bits. -/
def generatedSixthXiFoldedParity (n : ℕ) : ZMod 2 :=
  let a := Nat.xor n (n >>> 16)
  let b := Nat.xor a (a >>> 8)
  let c := Nat.xor b (b >>> 4)
  let d := Nat.xor c (c >>> 2)
  generatedSixthXiBitScalar (Nat.xor d (d >>> 1)) 0

/-- The folded arithmetic is exactly the original thirty-two-bit scalar sum. -/
theorem generatedSixth_xi_folded_parity (n : ℕ) :
    generatedSixthXiFoldedParity n =
      ∑ j : Fin 32, generatedSixthXiBitScalar n j.val := by
  simp only [generatedSixthXiFoldedParity, generatedSixth_xi_bit_scalar_xor,
    generatedSixth_xi_bit_scalar_shift]
  norm_num [Fin.sum_univ_succ]
  abel

/-- Intersection parity is the literal dot product of all thirty-two original bits. -/
theorem generatedSixth_xi_folded_dot (n m : ℕ) :
    generatedSixthXiFoldedParity (n &&& m) =
      ∑ j : Fin 32, generatedSixthXiBitScalar n j.val *
        generatedSixthXiBitScalar m j.val := by
  rw [generatedSixth_xi_folded_parity]
  apply Finset.sum_congr rfl
  intro j _
  simp only [generatedSixthXiBitScalar, Nat.testBit_and]
  cases n.testBit j.val <;> cases m.testBit j.val <;> decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
