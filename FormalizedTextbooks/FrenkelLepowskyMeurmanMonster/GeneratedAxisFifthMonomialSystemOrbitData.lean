/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSectionRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameSystemIntrinsic

/-! Finite certificates for the actual selected-octad orbit of the fifth frame system. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The fifteen displayed intrinsic indices in the monomial system orbit. -/
def generatedFifthMonomialSystemIndex : Fin 15 → Fin 270 :=
  ![14, 74, 66, 38, 134, 126, 102, 30, 122, 90, 62, 42, 2, 6, 98]

/-- Generator transitions among the displayed actual systems. -/
def generatedFifthMonomialSystemTransition : Fin 5 → Fin 15 → Fin 15 :=
  ![![1, 0, 7, 3, 11, 12, 10, 2, 14, 9, 6, 4, 5, 13, 8], ![0, 4, 2, 10, 1, 6, 5, 9, 11, 7, 3, 8,
    13, 12, 14], ![0, 5, 8, 9, 10, 1, 7, 6, 2, 3, 4, 14, 12, 13, 11], ![2, 1, 0, 10, 4, 13, 12,
    8, 7, 11, 3, 9, 6, 5, 14], ![3, 6, 9, 8, 10, 2, 7, 11, 1, 4, 14, 0, 12, 5, 13]]

/-- Forward basis-change columns, encoded as four-bit labels. -/
def generatedFifthMonomialSystemForward : Fin 5 → Fin 15 → Fin 4 → Fin 16 :=
  ![![![3, 4, 2, 8], ![5, 4, 2, 8], ![5, 1, 3, 8], ![2, 1, 7, 8], ![6, 1, 4, 8], ![6, 7, 3, 8],
    ![2, 5, 3, 8], ![2, 6, 3, 8], ![6, 1, 3, 8], ![2, 1, 4, 8], ![5, 1, 7, 8], ![2, 5, 4, 8],
    ![3, 7, 6, 8], ![2, 1, 4, 8], ![2, 6, 7, 8]], ![![1, 2, 6, 8], ![2, 1, 4, 8], ![2, 1, 4, 8],
    ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8],
    ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![1, 2, 6, 8], ![1, 2, 6, 8], ![2, 1, 4, 8]],
    ![![1, 3, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 3, 5, 8], ![1, 2, 5, 8], ![1, 2, 4, 8]], ![![4, 3, 2, 8], ![6, 5, 4, 8], ![6, 4, 1, 8],
    ![2, 5, 4, 8], ![6, 5, 4, 8], ![6, 4, 1, 8], ![6, 4, 1, 8], ![2, 5, 4, 8], ![6, 1, 4, 8],
    ![6, 1, 4, 8], ![6, 1, 4, 8], ![2, 5, 4, 8], ![4, 3, 2, 8], ![4, 3, 2, 8], ![6, 5, 4, 8]],
    ![![5, 3, 4, 8], ![1, 5, 2, 8], ![1, 2, 7, 8], ![3, 2, 5, 8], ![1, 2, 5, 8], ![1, 5, 7, 8],
    ![6, 5, 7, 8], ![3, 5, 2, 8], ![1, 7, 2, 8], ![6, 7, 5, 8], ![1, 7, 5, 8], ![3, 5, 4, 8],
    ![5, 3, 2, 8], ![5, 4, 3, 8], ![6, 5, 4, 8]]]

/-- Backward basis-change columns, encoded as four-bit labels. -/
def generatedFifthMonomialSystemBackward : Fin 5 → Fin 15 → Fin 4 → Fin 16 :=
  ![![![5, 4, 2, 8], ![3, 4, 2, 8], ![2, 6, 3, 8], ![2, 1, 7, 8], ![2, 5, 4, 8], ![3, 7, 6, 8],
    ![5, 1, 7, 8], ![5, 1, 3, 8], ![2, 6, 7, 8], ![2, 1, 4, 8], ![2, 5, 3, 8], ![6, 1, 4, 8],
    ![6, 7, 3, 8], ![2, 1, 4, 8], ![6, 1, 3, 8]], ![![1, 2, 6, 8], ![2, 1, 4, 8], ![2, 1, 4, 8],
    ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8],
    ![2, 1, 4, 8], ![2, 1, 4, 8], ![2, 1, 4, 8], ![1, 2, 6, 8], ![1, 2, 6, 8], ![2, 1, 4, 8]],
    ![![1, 3, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8],
    ![1, 3, 5, 8], ![1, 2, 5, 8], ![1, 2, 4, 8]], ![![6, 4, 1, 8], ![6, 5, 4, 8], ![4, 3, 2, 8],
    ![6, 1, 4, 8], ![6, 5, 4, 8], ![4, 3, 2, 8], ![4, 3, 2, 8], ![6, 1, 4, 8], ![2, 5, 4, 8],
    ![2, 5, 4, 8], ![2, 5, 4, 8], ![6, 1, 4, 8], ![6, 4, 1, 8], ![6, 4, 1, 8], ![6, 5, 4, 8]],
    ![![5, 7, 4, 8], ![1, 4, 3, 8], ![1, 2, 7, 8], ![3, 2, 7, 8], ![1, 2, 5, 8], ![1, 6, 3, 8],
    ![5, 6, 7, 8], ![5, 4, 7, 8], ![1, 4, 7, 8], ![3, 6, 7, 8], ![1, 6, 5, 8], ![6, 7, 4, 8],
    ![6, 4, 7, 8], ![3, 7, 2, 8], ![6, 5, 4, 8]]]

/-- Binary coefficient matrix decoded from four four-bit columns. -/
def generatedFifthMonomialSystemChange (a : Fin 4 → Fin 16) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if (a j).val.testBit i.val then 1 else 0

/-- Actual candidate basis matrices, with columns in root coordinates. -/
def generatedFifthMonomialSystemBasisMatrix (j : Fin 15) :
    Matrix (Fin 8) (Fin 4) (ZMod 2) :=
  fun i k => generatedAxisE8FrameSystemCandidateBasis (generatedFifthMonomialSystemIndex j) k i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Verify all75 eight-coordinate basis-change matrices using ordinary kernel reduction.
/-- Each forward basis change gives the actual selected-generator matrix action. -/
theorem generatedFifthMonomialSystem_forward_certificate : ∀ k : Fin 5, ∀ i : Fin 15,
    generatedFifthSectionGeneratorBinary ⟨12 + k.val, by omega⟩ *
        generatedFifthMonomialSystemBasisMatrix i =
      generatedFifthMonomialSystemBasisMatrix (generatedFifthMonomialSystemTransition k i) *
          generatedFifthMonomialSystemChange (generatedFifthMonomialSystemForward k i) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Verify all75 eight-coordinate basis-change matrices using ordinary kernel reduction.
/-- The backward change proves equality of spans, as well as forward containment. -/
theorem generatedFifthMonomialSystem_backward_certificate : ∀ k : Fin 5, ∀ i : Fin 15,
    generatedFifthSectionGeneratorBinary ⟨12 + k.val, by omega⟩ *
        generatedFifthMonomialSystemBasisMatrix i *
          generatedFifthMonomialSystemChange (generatedFifthMonomialSystemBackward k i) =
      generatedFifthMonomialSystemBasisMatrix (generatedFifthMonomialSystemTransition k i) := by
  decide +kernel

/-- The displayed intrinsic indices are distinct. -/
theorem generatedFifthMonomialSystemIndex_injective :
    Function.Injective generatedFifthMonomialSystemIndex := by
  decide +kernel

/-- Every generator transition is a permutation of the displayed indices. -/
theorem generatedFifthMonomialSystemTransition_bijective : ∀ k : Fin 5,
    Function.Bijective (generatedFifthMonomialSystemTransition k) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
