/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Exact packed-column arithmetic for the genuine sixth frame orbit certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A packed column catalogue denotes a genuine binary matrix, with the stated orientation. -/
def sixthFrameOrbitColumnMatrix {n : ℕ} (c : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  (monsterCo1GeometryBinaryMaskMatrix c).transpose

/-- Select original columns by the input bits, using exact ordinary XOR. -/
def sixthFrameOrbitMaskApply {n : ℕ} (c : Fin n → ℕ) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum
    (List.ofFn (fun j : Fin n => if v.testBit j.val then c j else 0))

/-- Packed column selection decodes to literal matrix multiplication on the actual binary space. -/
theorem sixthFrameOrbitMaskApply_decode {n : ℕ} (c : Fin n → ℕ) (v : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := n) (sixthFrameOrbitMaskApply c v) =
      sixthFrameOrbitColumnMatrix c *ᵥ monsterCo1GeometryBinaryMaskDecode v := by
  ext i
  change monsterCo1GeometryBinaryMaskDecode
    (monsterCo1GeometryBinaryMaskSum
      (List.ofFn (fun j : Fin n => if v.testBit j.val then c j else 0))) i =
    ∑ j : Fin n, monsterCo1GeometryBinaryMaskDecode (c j) i *
      monsterCo1GeometryBinaryMaskDecode v j
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  cases hv : v.testBit j.val <;> simp [monsterCo1GeometryBinaryMaskDecode, hv]

/-- The chosen number of bits recovers every packed value strictly below its range. -/
theorem sixthFrameOrbitMaskDecode_injective {n : ℕ} (a b : ℕ)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : monsterCo1GeometryBinaryMaskDecode (n := n) a =
      monsterCo1GeometryBinaryMaskDecode b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have he := congrFun h (⟨k, hk⟩ : Fin n)
    cases hka : a.testBit k <;> cases hkb : b.testBit k <;>
      simp_all [monsterCo1GeometryBinaryMaskDecode]
  · have hp : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le hp),
      Nat.testBit_eq_false_of_lt (hb.trans_le hp)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
