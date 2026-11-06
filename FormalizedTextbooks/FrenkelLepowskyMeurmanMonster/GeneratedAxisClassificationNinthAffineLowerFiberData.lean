/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSignedWordActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineSpreadTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineAlternatingImage

/-! Whole transported fiber coordinates for the eleven original genuine source words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The full fiber permutation of each original kernel or alternating source word. -/
def generatedNinthAffineLowerFiberPermutation (k : Fin 11) : Equiv.Perm (Fin 9) :=
  if h : k.val < 9 then 1 else generatedNinthAffineAlternatingPermutation ⟨k.val - 9, by omega⟩

/-- Exact four-coordinate images of every whole source word on every transported fiber basis. -/
def generatedNinthAffineLowerFiberCoefficientLabels : Fin 11 → Fin 9 → Fin 4 → Fin 16 :=
  ![![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8]],
    ![![14, 1, 5, 3], ![8, 2, 6, 7], ![1, 5, 2, 8], ![9, 8, 11, 15], ![1, 12, 10, 5], ![6, 1, 14,
    13], ![15, 6, 10, 2], ![7, 11, 3, 5], ![14, 12, 7, 10]],
    ![![15, 6, 3, 2], ![1, 5, 2, 12], ![15, 4, 7, 5], ![7, 15, 9, 4], ![9, 14, 12, 13], ![14, 1,
    10, 6], ![6, 7, 14, 10], ![8, 11, 1, 14], ![6, 10, 4, 7]]]

/-- The entire four-coordinate map of a genuine original source word between transported fibers. -/
def generatedNinthAffineLowerFiberCoefficientMap (k : Fin 11) (i : Fin 9) :
    (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  Matrix.mulVecLin (fun j l =>
    if (generatedNinthAffineLowerFiberCoefficientLabels k i l).val.testBit j.val then 1 else 0)

/-- Exact packed combination of the four whole original fiber directions. -/
def generatedNinthAffineLowerFiberDirectionMask (i : Fin 9) (a : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum
    (List.ofFn (fun j : Fin 4 => if a.testBit j.val then
      generatedNinthAffineDirectionMasks i j else 0))

/-- Packed four-direction selection decodes to the entire actual fiber map. -/
theorem generatedNinth_affine_lower_fiber_direction_decode (i : Fin 9) (a : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
        (generatedNinthAffineLowerFiberDirectionMask i a) =
      generatedNinthAffineDirectionMap i (monsterCo1GeometryBinaryMaskDecode (n := 4) a) := by
  ext k
  change monsterCo1GeometryBinaryMaskDecode
    (monsterCo1GeometryBinaryMaskSum
      (List.ofFn (fun j : Fin 4 => if a.testBit j.val then
        generatedNinthAffineDirectionMasks i j else 0))) k =
    ∑ j : Fin 4, monsterCo1GeometryBinaryMaskDecode (generatedNinthAffineDirectionMasks i j) k *
      monsterCo1GeometryBinaryMaskDecode a j
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  cases ha : a.testBit j.val <;> simp [monsterCo1GeometryBinaryMaskDecode, ha]

set_option maxHeartbeats 8000000 in
-- Evaluate each whole original source matrix on all thirty-six packed fiber directions.
/-- All complete source matrices retain the exact packed transported-fiber coordinates. -/
theorem generatedNinth_affine_lower_fiber_packed_certificate :
    ∀ (k : Fin 11) (i : Fin 9) (j : Fin 4),
    sixthFrameOrbitMaskApply (generatedNinthAffineLowerSourceColumns k)
      (sixthFrameOrbitMaskApply generatedNinthAffineTransportBinaryColumns
        (generatedNinthAffineDirectionMasks i j)) =
      sixthFrameOrbitMaskApply generatedNinthAffineTransportBinaryColumns
        (generatedNinthAffineLowerFiberDirectionMask (generatedNinthAffineLowerFiberPermutation k i)
          (generatedNinthAffineLowerFiberCoefficientLabels k i j).val) := by
  decide +kernel

/-- Every original source basis vector has the stated whole transported-fiber coordinates. -/
theorem generatedNinth_affine_lower_fiber_coordinate_certificate
    (k : Fin 11) (i : Fin 9) (j : Fin 4) :
    sixthFrameOrbitColumnMatrix (generatedNinthAffineLowerSourceColumns k) *ᵥ
      (sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
        generatedNinthAffineDirectionMap i (Pi.single j 1)) =
      sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns *ᵥ
        generatedNinthAffineDirectionMap (generatedNinthAffineLowerFiberPermutation k i)
          (generatedNinthAffineLowerFiberCoefficientMap k i (Pi.single j 1)) := by
  have h := congrArg (monsterCo1GeometryBinaryMaskDecode (n := 24))
    (generatedNinth_affine_lower_fiber_packed_certificate k i j)
  rw [sixthFrameOrbitMaskApply_decode, sixthFrameOrbitMaskApply_decode,
    sixthFrameOrbitMaskApply_decode, generatedNinth_affine_lower_fiber_direction_decode] at h
  have hd : generatedNinthAffineDirectionMap i (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedNinthAffineDirectionMasks i j) := by
    rw [generatedNinthAffineDirectionMap, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    rfl
  have hc : generatedNinthAffineLowerFiberCoefficientMap k i (Pi.single j 1) =
      monsterCo1GeometryBinaryMaskDecode (n := 4)
        (generatedNinthAffineLowerFiberCoefficientLabels k i j).val := by
    rw [generatedNinthAffineLowerFiberCoefficientMap, Matrix.mulVecLin_apply,
      Matrix.mulVec_single_one]
    rfl
  rw [hd, hc]
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
