/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Exact column-XOR evaluation of genuine binary matrices. This compact
encoding avoids expanding a field sum for every finite orbit-certificate edge. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Decode integer column masks into an ordinary binary matrix. -/
def generatedAxisGlobalMaskColumnMatrix {n : ℕ} (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => monsterCo1GeometryBinaryMaskDecode (a j) i

/-- Evaluate a binary matrix by XOR of exactly the selected column masks. -/
def generatedAxisGlobalMaskColumnAction {n : ℕ} (a : Fin n → ℕ) (b : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum
    (List.ofFn (fun j : Fin n => if b.testBit j.val then a j else 0))

/-- Compact XOR evaluation is the genuine matrix-vector action, at every dimension. -/
theorem generatedAxisGlobalMaskColumnAction_decode {n : ℕ} (a : Fin n → ℕ) (b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := n) (generatedAxisGlobalMaskColumnAction a b) =
      generatedAxisGlobalMaskColumnMatrix a *ᵥ monsterCo1GeometryBinaryMaskDecode b := by
  unfold generatedAxisGlobalMaskColumnAction
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  ext i
  simp only [Finset.sum_apply, Function.comp_apply, generatedAxisGlobalMaskColumnMatrix,
    Matrix.mulVec, dotProduct]
  change (∑ j : Fin n,
    monsterCo1GeometryBinaryMaskDecode (if b.testBit j.val then a j else 0) i) =
      ∑ j : Fin n, monsterCo1GeometryBinaryMaskDecode (a j) i *
        monsterCo1GeometryBinaryMaskDecode b j
  apply Finset.sum_congr rfl
  intro j _
  cases h : b.testBit j.val
  · simp only [h, Bool.false_eq_true, ↓reduceIte,
      monsterCo1GeometryBinaryMaskDecode, Nat.zero_testBit, mul_zero]
  · simp only [h, ↓reduceIte, monsterCo1GeometryBinaryMaskDecode, mul_one]

/-- A checked integer-mask edge proves the actual binary matrix edge. -/
theorem generatedAxisGlobalMaskColumn_edge {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (a : Fin n → ℕ) (b c : ℕ)
    (hM : M = generatedAxisGlobalMaskColumnMatrix a)
    (hc : generatedAxisGlobalMaskColumnAction a b = c) :
    M *ᵥ monsterCo1GeometryBinaryMaskDecode b = monsterCo1GeometryBinaryMaskDecode c := by
  rw [hM, ← generatedAxisGlobalMaskColumnAction_decode, hc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
