/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSourceMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMaskEncode

/-! Compact masks for all three original preferred short-Q dictionaries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual Ω correction in the original twelve-coordinate translation block. -/
def generatedAxisGlobalOmegaMask (c : ZMod 2) : ℕ := if c = 0 then 0 else 2048

/-- The packed Ω correction is exactly its original translation vector. -/
theorem generatedAxisGlobalOmegaMask_decode (c : ZMod 2) :
    monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedAxisGlobalOmegaMask c) =
      c • (Pi.single 11 1 : Fin 12 → ZMod 2) := by
  have h : ∀ c : ZMod 2, ∀ i : Fin 12,
      monsterCo1GeometryBinaryMaskDecode (n := 12) (generatedAxisGlobalOmegaMask c) i =
        (c • (Pi.single 11 1 : Fin 12 → ZMod 2)) i := by
    decide +kernel
  funext i
  exact h c i

/-- The physical mask of the actual negative coordinates of an octad label. -/
def generatedAxisGlobalOctadNegativeMask (j : Fin 759) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun (k : Fin 8) (m : ℕ) =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedAxisGlobalOctadCoordinatesData j k).val else 0) ||| m) 0

/-- Decoding the negative mask is the parity of the actual integer dictionary vector. -/
theorem generatedAxisGlobalOctadNegativeMask_decode (j : Fin 759) (e : Fin 64) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalOctadNegativeMask j e) =
      integerParity (generatedAxisGlobalOctadNegativeInteger j e) := by
  funext i
  unfold monsterCo1GeometryBinaryMaskDecode generatedAxisGlobalOctadNegativeMask
    integerParity generatedAxisGlobalOctadNegativeInteger
  split <;> simp_all

/-- The compact original mask of each pair, octad, or odd preferred short lift. -/
def generatedAxisGlobalShortMask : GriessShortIndex → ℕ
  | Sum.inl (s, p) => generatedAxisGlobalSourceMaskJoin (if s = 0 then 0 else 2048)
      (Nat.xor
        (generatedAxisGlobalCocodeColumnMask (generatedAxisGlobalPairCoordinates p).1)
        (generatedAxisGlobalCocodeColumnMask (generatedAxisGlobalPairCoordinates p).2))
  | Sum.inr (Sum.inl (j, e)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedAxisGlobalOctadCodeData j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (parkerThetaMask (generatedAxisGlobalOctadCodeData j).val)
        (generatedAxisGlobalCocodeMask (generatedAxisGlobalOctadNegativeMask j e)))
  | Sum.inr (Sum.inr (d, j)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor d.val (generatedAxisGlobalOmegaMask (griessOddOmegaCoefficient d j)))
      (Nat.xor (parkerThetaMask d.val) (generatedAxisGlobalCocodeColumnMask j))

/-- Every compact short mask decodes to the entire original preferred-Q binary vector. -/
theorem generatedAxisGlobalShortMask_decode (r : GriessShortIndex) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalShortMask r) =
      toAdd (generatedAxisGlobalShortQFinite r).base := by
  rcases r with ⟨s, p⟩ | (⟨j, e⟩ | ⟨d, j⟩)
  · simp only [generatedAxisGlobalShortMask, generatedAxisGlobalSourceMaskJoin_decode,
      monsterCo1GeometryBinaryMaskDecode_xor, generatedAxisGlobalCocodeColumnMask_decode]
    have hlow : monsterCo1GeometryBinaryMaskDecode (n := 12)
        (if s = 0 then 0 else 2048) = (if s = 0 then 0 else Pi.single 11 1) := by
      by_cases h : s = 0
      · simp [h, monsterCo1GeometryBinaryMaskDecode_zero]
      · simpa [h, generatedAxisGlobalOmegaMask] using generatedAxisGlobalOmegaMask_decode 1
    rw [hlow]
    rfl
  · simp only [generatedAxisGlobalShortMask, generatedAxisGlobalSourceMaskJoin_decode,
      monsterCo1GeometryBinaryMaskDecode_xor, generatedAxisGlobalOmegaMask_decode,
      generatedAxisGlobalCocodeMask_decode, generatedAxisGlobalOctadNegativeMask_decode]
    rfl
  · simp only [generatedAxisGlobalShortMask, generatedAxisGlobalSourceMaskJoin_decode,
      monsterCo1GeometryBinaryMaskDecode_xor, generatedAxisGlobalOmegaMask_decode,
      generatedAxisGlobalCocodeColumnMask_decode]
    rfl

/-- The compact mask is the full actual preferred lift, including its positive central section. -/
theorem generatedAxisGlobalShortMask_Q_actual (r : GriessShortIndex) :
    generatedAxisGlobalShortQFinite r =
      generatedAxisGlobalQMask (generatedAxisGlobalShortMask r) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact (generatedAxisGlobalShortMask_decode r).symm
  · exact generatedAxisGlobalShortQFinite_positive r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
