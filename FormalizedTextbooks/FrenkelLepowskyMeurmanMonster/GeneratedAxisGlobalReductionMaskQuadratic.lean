/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Boolean mask parity is the genuine extraspecial quadratic form in the
proved hyperbolic coordinates, rather than an independent singularity test. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem boolXor_value (a b : Bool) :
    (if Bool.xor a b then (1 : ZMod 2) else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide +kernel

private theorem boolFold_value (bits : List Bool) (a : Bool) :
    (if bits.foldl Bool.xor a then (1 : ZMod 2) else 0) =
      (if a then 1 else 0) + (bits.map (fun b => if b then (1 : ZMod 2) else 0)).sum := by
  induction bits generalizing a with
  | nil => simp
  | cons b bits ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, boolXor_value, add_assoc]

/-- Compute singularity by the parity of the twelve genuine hyperbolic coordinate pairs. -/
def generatedAxisGlobalMaskSingular (b : ℕ) : Bool :=
  !((List.ofFn (fun i : Fin 12 => b.testBit i.val && b.testBit (i.val + 12))).foldl
    Bool.xor false)

/-- The compact Boolean test is exactly zero of the actual extraspecial quadratic form. -/
theorem generatedAxisGlobalMaskSingular_iff (b : ℕ) :
    generatedAxisGlobalMaskSingular b = true ↔
      squareQuad (monsterCo1GeometryBinaryMaskDecode (n := 24) b) = 0 := by
  let bits := List.ofFn (fun i : Fin 12 => b.testBit i.val && b.testBit (i.val + 12))
  have hv := boolFold_value bits false
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add, bits, List.map_ofFn,
    List.sum_ofFn] at hv
  have hq : squareQuad (monsterCo1GeometryBinaryMaskDecode (n := 24) b) =
      if bits.foldl Bool.xor false then (1 : ZMod 2) else 0 := by
    rw [hv]
    change (∑ i : Fin 12,
      monsterCo1GeometryBinaryMaskDecode b (Fin.castAdd 12 i) *
        monsterCo1GeometryBinaryMaskDecode b (Fin.natAdd 12 i)) = _
    apply Finset.sum_congr rfl
    intro i _
    cases h : b.testBit i.val <;> cases h' : b.testBit (i.val + 12) <;>
      simp [monsterCo1GeometryBinaryMaskDecode, h, h']
  rw [hq]
  change (!(bits.foldl Bool.xor false)) = true ↔ _
  cases bits.foldl Bool.xor false <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
