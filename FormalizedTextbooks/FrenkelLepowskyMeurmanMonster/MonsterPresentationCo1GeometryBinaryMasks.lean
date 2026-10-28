/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Binary row masks decode into actual characteristic-two vectors, with checked XOR semantics. -/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Read the chosen coordinate bits of an integer mask as a genuine binary vector. -/
def monsterCo1GeometryBinaryMaskDecode {n : ℕ} (a : ℕ) : Fin n → ZMod 2 :=
  fun j => if a.testBit j.val then 1 else 0

/-- A finite mask sum uses ordinary bitwise XOR, with no numerical or field approximation. -/
def monsterCo1GeometryBinaryMaskSum : List ℕ → ℕ
  | [] => 0
  | a :: row => Nat.xor a (monsterCo1GeometryBinaryMaskSum row)

/-- Bitwise XOR decodes to exact addition in the actual characteristic-two coordinate module. -/
theorem monsterCo1GeometryBinaryMaskDecode_xor {n : ℕ} (a b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := n) (Nat.xor a b) =
      monsterCo1GeometryBinaryMaskDecode a + monsterCo1GeometryBinaryMaskDecode b := by
  ext j
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  cases ha : a.testBit j.val <;> cases hb : b.testBit j.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode, Nat.testBit_xor, ha, hb, h11]

/-- The zero mask is exactly the zero coordinate vector. -/
theorem monsterCo1GeometryBinaryMaskDecode_zero {n : ℕ} :
    monsterCo1GeometryBinaryMaskDecode (n := n) 0 = 0 := by
  ext j
  simp [monsterCo1GeometryBinaryMaskDecode]

/-- A complete finite XOR row sum decodes to its literal vector sum. -/
theorem monsterCo1GeometryBinaryMaskDecode_sum {n : ℕ} (row : List ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := n) (monsterCo1GeometryBinaryMaskSum row) =
      (row.map (monsterCo1GeometryBinaryMaskDecode (n := n))).sum := by
  induction row with
  | nil => exact monsterCo1GeometryBinaryMaskDecode_zero
  | cons a row ih =>
      simp only [monsterCo1GeometryBinaryMaskSum, monsterCo1GeometryBinaryMaskDecode_xor,
        ih, List.map_cons, List.sum_cons]

/-- At any chosen bit, a finite XOR sum is the exact characteristic-two bit parity. -/
theorem monsterCo1GeometryBinaryMaskSum_parity (row : List ℕ) (i : ℕ) :
    (if (monsterCo1GeometryBinaryMaskSum row).testBit i then (1 : ZMod 2) else 0) =
      (row.map (fun a => if a.testBit i then (1 : ZMod 2) else 0)).sum := by
  induction row with
  | nil => simp [monsterCo1GeometryBinaryMaskSum]
  | cons a row ih =>
      simp only [monsterCo1GeometryBinaryMaskSum, List.map_cons, List.sum_cons, ← ih]
      have h := congrFun
        (monsterCo1GeometryBinaryMaskDecode_xor (n := i + 1) a
          (monsterCo1GeometryBinaryMaskSum row)) (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))
      exact h


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
