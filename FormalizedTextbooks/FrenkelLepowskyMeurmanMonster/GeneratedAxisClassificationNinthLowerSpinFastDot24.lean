/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFastParity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import Mathlib.Data.List.OfFn

/-! Exact byte and nibble lookups replace the twenty-four individual bit products.
Both operands may be arbitrary natural numbers; only the original low twenty-four bits count. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem bool_fold_xor (bits : List Bool) (a : Bool) :
    bits.foldl Bool.xor a = Bool.xor a (bits.foldl Bool.xor false) := by
  induction bits generalizing a with
  | nil => cases a <;> rfl
  | cons b bits ih =>
    simp only [List.foldl_cons]
    rw [ih (Bool.xor a b), ih (Bool.xor false b)]
    cases a <;> cases b <;> cases bits.foldl Bool.xor false <;> rfl

private theorem mask_sum_bool (bits : List Bool) :
    monsterCo1GeometryBinaryMaskSum (bits.map (fun b => if b then 1 else 0)) =
      if bits.foldl Bool.xor false then 1 else 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.map_cons, monsterCo1GeometryBinaryMaskSum, List.foldl_cons, ih]
    have hf : bits.foldl Bool.xor (Bool.xor false b) =
        Bool.xor b (bits.foldl Bool.xor false) := by
      rw [bool_fold_xor bits (Bool.xor false b)]
      cases b <;> rfl
    simp only [hf]
    generalize bits.foldl Bool.xor false = c
    cases b <;> cases c <;> decide +kernel

private theorem mask_sum_append (a b : List ℕ) :
    monsterCo1GeometryBinaryMaskSum (a ++ b) =
      Nat.xor (monsterCo1GeometryBinaryMaskSum a) (monsterCo1GeometryBinaryMaskSum b) := by
  induction a with
  | nil => simp only [List.nil_append, monsterCo1GeometryBinaryMaskSum, Nat.xor_eq,
      Nat.zero_xor]
  | cons c a ih =>
    simp only [List.cons_append, monsterCo1GeometryBinaryMaskSum, ih, Nat.xor_eq,
      Nat.xor_assoc]

/-- The exact twelve-bit dot product, using the certified byte and nibble parity tables. -/
def generatedNinthLowerSpinFastDotTwelve (a b : ℕ) : ℕ :=
  if !(generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096)) then 1 else 0

/-- Two twelve-bit intersection parities give the complete original twenty-four-bit dot. -/
def generatedNinthLowerSpinFastDot24 (a b : ℕ) : ℕ :=
  if Bool.xor (generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096))
      (generatedAxisGlobalFastParityTwelve (((a >>> 12) &&& (b >>> 12)) % 4096))
    then 1 else 0

/-- The fast twelve-bit result equals the original natural-number XOR dot, without bounds. -/
theorem generatedNinth_lower_spin_fast_dot_twelve (a b : ℕ) :
    generatedNinthLowerSpinFastDotTwelve a b =
      monsterCo1GeometryBinaryMaskDot 12 a b := by
  have hbits : (List.ofFn (fun k : Fin 12 =>
      if a.testBit k.val then if b.testBit k.val then 1 else 0 else 0)) =
      (List.ofFn (fun k : Fin 12 => (a &&& b).testBit k.val)).map
        (fun bit => if bit then 1 else 0) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    dsimp only [Function.comp_apply]
    rw [Nat.testBit_and]
    cases a.testBit k.val <;> cases b.testBit k.val <;> rfl
  unfold monsterCo1GeometryBinaryMaskDot
  rw [hbits, mask_sum_bool]
  have hp := generatedAxisGlobalFastParity_certificate
    (⟨(a &&& b) % 4096, Nat.mod_lt _ (by decide)⟩ : Fin 4096)
  have hm := generatedAxisGlobalParityTwelve_mod (a &&& b)
  have he : generatedAxisGlobalParityTwelve (a &&& b) =
      generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096) := hm.trans hp
  unfold generatedAxisGlobalParityTwelve at he
  unfold generatedNinthLowerSpinFastDotTwelve
  rw [← he]
  cases (List.ofFn (fun k : Fin 12 => (a &&& b).testBit k.val)).foldl Bool.xor false <;>
    rfl

/-- The original finite dot splits at coordinate twelve, retaining all its original bits. -/
theorem generatedNinth_lower_spin_dot24_split (a b : ℕ) :
    monsterCo1GeometryBinaryMaskDot 24 a b =
      Nat.xor (monsterCo1GeometryBinaryMaskDot 12 a b)
        (monsterCo1GeometryBinaryMaskDot 12 (a >>> 12) (b >>> 12)) := by
  unfold monsterCo1GeometryBinaryMaskDot
  change monsterCo1GeometryBinaryMaskSum (List.ofFn (fun k : Fin (12 + 12) =>
    if a.testBit k.val then if b.testBit k.val then 1 else 0 else 0)) = _
  rw [List.ofFn_add, mask_sum_append]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.testBit_shiftRight, Nat.add_comm]

/-- The fast result is the entire original natural-number dot, including its exact parity bit.
No boundedness assumption is made on either input mask. -/
theorem generatedNinth_lower_spin_fast_dot24 (a b : ℕ) :
    generatedNinthLowerSpinFastDot24 a b =
      monsterCo1GeometryBinaryMaskDot 24 a b := by
  rw [generatedNinth_lower_spin_dot24_split,
    ← generatedNinth_lower_spin_fast_dot_twelve,
    ← generatedNinth_lower_spin_fast_dot_twelve]
  unfold generatedNinthLowerSpinFastDot24 generatedNinthLowerSpinFastDotTwelve
  cases generatedAxisGlobalFastParityTwelve ((a &&& b) % 4096) <;>
    cases generatedAxisGlobalFastParityTwelve (((a >>> 12) &&& (b >>> 12)) % 4096) <;>
      decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
