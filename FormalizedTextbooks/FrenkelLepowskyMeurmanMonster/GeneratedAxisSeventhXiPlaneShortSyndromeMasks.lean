/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortQMaskCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary

/-! Compact cocode masks evaluate the actual source Golay syndrome on physical positions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every physical coordinate's complete twelve-bit cocode column in the original Golay basis. -/
def generatedSeventhXiShortCocodeColumn : Fin 24 → Fin 4096 :=
  ![2048, 3584, 3328, 3840, 3087, 2191, 2127, 2255, 3086, 2094, 2078, 2110,
    3085, 2733, 2397, 3069, 3083, 2539, 2971, 2683, 3079, 2919, 2775, 2487]

/-- All source generator bits agree with the complete physical column masks. -/
theorem generatedSeventhXiShortCocodeColumn_actual : ∀ i : Fin 24,
    golayLabelCoefficients (generatedSeventhXiShortCocodeColumn i) =
      fun k => (golayGeneratorBit k i : ZMod 2) := by
  decide +kernel

/-- Reduction modulo4096 preserves every original twelve-coordinate source bit. -/
theorem generatedSeventhXiShortMask_mod_decode (n : ℕ) :
    golayLabelCoefficients ⟨n % 4096, Nat.mod_lt _ (by decide)⟩ =
      monsterCo1GeometryBinaryMaskDecode (n := 12) n := by
  funext k
  have h : (n % 4096).testBit k.val = n.testBit k.val := by
    change (n % 2 ^ 12).testBit k.val = _
    rw [Nat.testBit_mod_two_pow]
    simp only [k.isLt, decide_true, Bool.true_and]
  simp only [golayLabelCoefficients, monsterCo1GeometryBinaryMaskDecode, h]

/-- The exact syndrome mask adds each selected physical column in characteristic two. -/
def generatedSeventhXiShortSyndromeMask (v : ℕ) : Fin 4096 :=
  ⟨monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
      if v.testBit i.val then (generatedSeventhXiShortCocodeColumn i).val else 0)) % 4096,
    Nat.mod_lt _ (by decide)⟩

/-- Every cocode mask is the literal Golay syndrome, with all selected physical positions. -/
theorem generatedSeventhXiShortSyndromeMask_actual (v : ℕ) :
    golayLabelCoefficients (generatedSeventhXiShortSyndromeMask v) =
      golaySyndrome (fun i => golayBooleanCast (v.testBit i.val)) := by
  rw [generatedSeventhXiShortSyndromeMask, generatedSeventhXiShortMask_mod_decode,
    monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  funext k
  simp only [Finset.sum_apply, Function.comp_def]
  change (∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode
      (n := 12) (if v.testBit i.val then (generatedSeventhXiShortCocodeColumn i).val else 0) k) =
    ∑ i : Fin 24, golayBooleanCast (v.testBit i.val) * (golayGeneratorBit k i : ZMod 2)
  apply Finset.sum_congr rfl
  intro i _
  cases hv : v.testBit i.val
  · simp [monsterCo1GeometryBinaryMaskDecode, golayBooleanCast]
  · simp only [ite_true, golayBooleanCast, one_mul]
    exact congrFun (generatedSeventhXiShortCocodeColumn_actual i) k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
