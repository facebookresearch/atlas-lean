/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiMaskCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Exact original syndrome masks evaluate preferred-Q modulation without lattice inversion. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Literal original Golay-column syndromes in the twelve cocode positions. -/
def generatedSixthXiSyndromeColumns : Fin 24 → ℕ :=
  ![2048, 3584, 3328, 3840, 3087, 2191, 2127, 2255, 3086, 2094, 2078, 2110,
    3085, 2733, 2397, 3069, 3083, 2539, 2971, 2683, 3079, 2919, 2775, 2487]

/-- Every displayed column is the original generator-coordinate character. -/
theorem generatedSixth_xi_syndrome_columns : ∀ i : Fin 24, ∀ j : Fin 12,
    monsterCo1GeometryBinaryMaskDecode (generatedSixthXiSyndromeColumns i) j =
      (golayGeneratorBit j i : ZMod 2) := by
  decide +kernel

/-- Selected original syndrome columns sum by genuine characteristic-two XOR. -/
def generatedSixthXiSyndromeMask (n : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if n.testBit i.val then generatedSixthXiSyndromeColumns i else 0))

/-- The mask is exactly the original syndrome of the full negative-coordinate vector. -/
theorem generatedSixth_xi_syndrome_mask (n : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedSixthXiSyndromeMask n) =
      golaySyndrome (monsterCo1GeometryBinaryMaskDecode n) := by
  rw [generatedSixthXiSyndromeMask, monsterCo1GeometryBinaryMaskDecode_sum,
    List.map_ofFn, List.sum_ofFn]
  funext j
  simp only [Finset.sum_apply]
  change (∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode
    (if n.testBit i.val then generatedSixthXiSyndromeColumns i else 0) j) =
      ∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode n i *
        (golayGeneratorBit j i : ZMod 2)
  apply Finset.sum_congr rfl
  intro i _
  cases h : n.testBit i.val
  · simp [monsterCo1GeometryBinaryMaskDecode, h]
  · simp only [ite_true]
    rw [generatedSixth_xi_syndrome_columns]
    simp [monsterCo1GeometryBinaryMaskDecode, h]

/-- Zero-one integer mask coordinates have the exact original parity vector. -/
theorem generatedSixth_xi_integer_mask_parity (n : ℕ) :
    integerParity (fun i : Fin 24 => if n.testBit i.val then (1 : ℤ) else 0) =
      monsterCo1GeometryBinaryMaskDecode n := by
  funext i
  cases h : n.testBit i.val <;> simp [integerParity, monsterCo1GeometryBinaryMaskDecode, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
