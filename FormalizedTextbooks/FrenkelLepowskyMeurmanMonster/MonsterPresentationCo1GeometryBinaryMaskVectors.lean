/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Compact bit parity proves exact binary dot products and matrix-vector action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- Select coordinate bits of the right vector using the left vector, and sum by XOR. -/
def monsterCo1GeometryBinaryMaskDot (n : ℕ) (a b : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun k : Fin n =>
    if a.testBit k.val then if b.testBit k.val then 1 else 0 else 0))

/-- A compact bit dot product is the literal dot product of the genuine binary vectors. -/
theorem monsterCo1GeometryBinaryMaskDot_decode (n : ℕ) (a b : ℕ) :
    (if (monsterCo1GeometryBinaryMaskDot n a b).testBit 0 then (1 : ZMod 2) else 0) =
      ∑ k : Fin n, monsterCo1GeometryBinaryMaskDecode a k *
        monsterCo1GeometryBinaryMaskDecode b k := by
  unfold monsterCo1GeometryBinaryMaskDot
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  cases ha : a.testBit k.val <;> cases hb : b.testBit k.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode, ha, hb]

/-- The row parities give the complete exact action of a decoded binary matrix. -/
theorem monsterCo1GeometryBinaryMaskMatrix_mulVec {n : ℕ} (a : Fin n → ℕ) (b : ℕ) :
    monsterCo1GeometryBinaryMaskMatrix a *ᵥ monsterCo1GeometryBinaryMaskDecode b =
      fun i => if (monsterCo1GeometryBinaryMaskDot n (a i) b).testBit 0 then 1 else 0 := by
  ext i
  exact (monsterCo1GeometryBinaryMaskDot_decode n (a i) b).symm

/-- Exact bit-parity tests prove the original matrix action on complete actual vectors. -/
theorem monsterCo1GeometryBinaryMaskVector_certificate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (u v : Fin n → ZMod 2)
    (a : Fin n → ℕ) (b c : ℕ)
    (hA : A = monsterCo1GeometryBinaryMaskMatrix a)
    (hu : u = monsterCo1GeometryBinaryMaskDecode b)
    (hv : v = monsterCo1GeometryBinaryMaskDecode c)
    (check : ∀ i : Fin n, (monsterCo1GeometryBinaryMaskDot n (a i) b).testBit 0 =
      c.testBit i.val) : A *ᵥ u = v := by
  rw [hA, hu, hv, monsterCo1GeometryBinaryMaskMatrix_mulVec]
  ext i
  simp only [monsterCo1GeometryBinaryMaskDecode, check i]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
