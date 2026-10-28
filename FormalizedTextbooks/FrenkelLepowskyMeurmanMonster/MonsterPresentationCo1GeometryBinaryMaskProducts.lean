/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A compact XOR checker certifies complete actual binary matrix multiplication. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Integer row masks denote complete genuine binary square matrices of the chosen dimension. -/
def monsterCo1GeometryBinaryMaskMatrix {n : ℕ} (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) (ZMod 2) := fun i => monsterCo1GeometryBinaryMaskDecode (a i)

/-- Mask product rows select the right matrix rows according to left matrix coordinate bits. -/
def monsterCo1GeometryBinaryMaskProduct {n : ℕ} (a b : Fin n → ℕ) : Fin n → ℕ :=
  fun i => monsterCo1GeometryBinaryMaskSum
    (List.ofFn (fun k : Fin n => if (a i).testBit k.val then b k else 0))

/-- The compact mask product decodes to exact ordinary matrix multiplication, in the same order. -/
theorem monsterCo1GeometryBinaryMaskMatrix_product {n : ℕ} (a b : Fin n → ℕ) :
    monsterCo1GeometryBinaryMaskMatrix (monsterCo1GeometryBinaryMaskProduct a b) =
      monsterCo1GeometryBinaryMaskMatrix a * monsterCo1GeometryBinaryMaskMatrix b := by
  ext i j
  change monsterCo1GeometryBinaryMaskDecode
      (monsterCo1GeometryBinaryMaskSum
        (List.ofFn (fun k : Fin n => if (a i).testBit k.val then b k else 0))) j =
    ∑ k, monsterCo1GeometryBinaryMaskDecode (a i) k *
      monsterCo1GeometryBinaryMaskDecode (b k) j
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases h : (a i).testBit k.val <;> simp [monsterCo1GeometryBinaryMaskDecode, h]

/-- Complete matrix decoding checks and an exact mask product certificate prove the original
actual matrix equality; the checker adds no assumption about any group action. -/
theorem monsterCo1GeometryBinaryMaskProduct_certificate {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (ZMod 2)) (a b c : Fin n → ℕ)
    (hA : A = monsterCo1GeometryBinaryMaskMatrix a)
    (hB : B = monsterCo1GeometryBinaryMaskMatrix b)
    (hC : C = monsterCo1GeometryBinaryMaskMatrix c)
    (check : monsterCo1GeometryBinaryMaskProduct a b = c) : A * B = C := by
  rw [hA, hB, hC, ← monsterCo1GeometryBinaryMaskMatrix_product, check]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
