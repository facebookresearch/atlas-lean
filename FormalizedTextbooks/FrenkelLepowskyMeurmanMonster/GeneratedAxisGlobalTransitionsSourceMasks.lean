/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskEncode
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SourceCocode
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary

/-! Exact packed masks for the original code and cocode coordinate dictionaries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Two original twelve-coordinate words, packed without losing either coordinate block. -/
def generatedAxisGlobalSourceMaskJoin (a b : ℕ) : ℕ :=
  Nat.xor (a % 4096) (b <<< 12)

/-- Packing the two finite source words is exactly the original twenty-four-coordinate vector. -/
theorem generatedAxisGlobalSourceMaskJoin_decode (a b : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalSourceMaskJoin a b) =
      Fin.append (monsterCo1GeometryBinaryMaskDecode (n := 12) a)
        (monsterCo1GeometryBinaryMaskDecode (n := 12) b) := by
  unfold generatedAxisGlobalSourceMaskJoin
  rw [monsterCo1GeometryBinaryMaskDecode_xor]
  funext i
  refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i
  · simp only [Pi.add_apply, Fin.append_left]
    change (if (a % 2 ^ 12).testBit j.val then (1 : ZMod 2) else 0) +
      (if (b <<< 12).testBit j.val then (1 : ZMod 2) else 0) =
        (if a.testBit j.val then (1 : ZMod 2) else 0)
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    simp [j.isLt, show ¬j.val ≥ 12 by omega]
  · have ha : (a % 4096).testBit (12 + j.val) = false := by
      apply Nat.testBit_eq_false_of_lt
      have hm : a % 4096 < 2 ^ 12 := Nat.mod_lt _ (by decide)
      exact hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [Pi.add_apply, Fin.append_right]
    change (if (a % 4096).testBit (12 + j.val) then (1 : ZMod 2) else 0) +
      (if (b <<< 12).testBit (12 + j.val) then (1 : ZMod 2) else 0) =
        (if b.testBit j.val then (1 : ZMod 2) else 0)
    rw [ha, Nat.testBit_shiftLeft]
    simp

/-- The original code section mask, with its original Parker theta modulation. -/
def generatedAxisGlobalSourceCodeMask (d : Fin 4096) : ℕ :=
  generatedAxisGlobalSourceMaskJoin d.val (parkerThetaMask d.val)

/-- The packed code section has exactly its actual original code and theta coordinates. -/
theorem generatedAxisGlobalSourceCodeMask_decode (d : Fin 4096) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalSourceCodeMask d) =
      Fin.append (golayLabelCoefficients d) (sourceWordTheta d) := by
  rw [generatedAxisGlobalSourceCodeMask, generatedAxisGlobalSourceMaskJoin_decode]
  rfl

/-- The actual twenty-four cocode generator columns in their original twelve-bit coordinates. -/
def generatedAxisGlobalCocodeColumnMask : Fin 24 → ℕ :=
  ![2048, 3584, 3328, 3840, 3087, 2191, 2127, 2255,
    3086, 2094, 2078, 2110, 3085, 2733, 2397, 3069,
    3083, 2539, 2971, 2683, 3079, 2919, 2775, 2487]

/-- Every cocode-column bit is the original Golay generator bit, with its actual scalar cast. -/
theorem generatedAxisGlobalCocodeColumnMask_decode (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedAxisGlobalCocodeColumnMask i) =
      (fun k : Fin 12 => (golayGeneratorBit k i : ZMod 2)) := by
  funext k
  have h : ∀ i : Fin 24, ∀ k : Fin 12,
      monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedAxisGlobalCocodeColumnMask i) k =
        (golayGeneratorBit k i : ZMod 2) := by
    decide +kernel
  exact h i k

/-- A complete physical binary cocode word, evaluated in the original source frame. -/
def generatedAxisGlobalCocodeMask (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then generatedAxisGlobalCocodeColumnMask i else 0))

/-- Every physical mask is sent to the precise actual original Golay syndrome. -/
theorem generatedAxisGlobalCocodeMask_decode (v : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedAxisGlobalCocodeMask v) =
      golaySyndrome (monsterCo1GeometryBinaryMaskDecode (n := 24) v) := by
  unfold generatedAxisGlobalCocodeMask
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  funext k
  simp only [Finset.sum_apply]
  change (∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode (n := 12)
    (if v.testBit i.val then generatedAxisGlobalCocodeColumnMask i else 0) k) =
      ∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode (n := 24) v i *
        (golayGeneratorBit k i : ZMod 2)
  apply Finset.sum_congr rfl
  intro i _
  cases h : v.testBit i.val
  · simp [h, monsterCo1GeometryBinaryMaskDecode]
  · simpa [h, monsterCo1GeometryBinaryMaskDecode] using
      congrFun (generatedAxisGlobalCocodeColumnMask_decode i) k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
