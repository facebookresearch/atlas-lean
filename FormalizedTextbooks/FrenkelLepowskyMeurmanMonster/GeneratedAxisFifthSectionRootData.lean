/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthSelectedOctad
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsIncidence
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiMatrix

/-! Exact root-coordinate certificates for actual selected-section signs, permutations and Xi. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Exact physical matrix numerators of twelve signs, five selected permutations and Xi. -/
def generatedFifthSectionGeneratorNumerator (g : Fin 18) : Matrix (Fin 24) (Fin 24) ℤ :=
  if h : g.val < 12 then fun i j =>
    if i = j then 2 * (if golayGeneratorBit ⟨g.val, h⟩ i = 0 then 1 else -1) else 0
  else if h' : g.val < 17 then fun i j =>
    if i = generatedFifthSelectedOctadForward ⟨g.val - 12, by omega⟩ j
      then 2 else 0
  else co1XiNumerator

/-- Actual integral root actions of the selected-section generators. -/
def generatedFifthSectionGeneratorInteger : Fin 18 → Matrix (Fin 8) (Fin 8) ℤ :=
  ![![![1, 0, 0, 1, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 1, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![1, 0, 0, 1, 1, 1, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 0, 1, 0, 2],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, -1],
    ![0, 0, 0, 0, 1, 0, 0, -1],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 3],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 1, 0, 0, 2],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, -1],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, -1],
    ![0, 0, 0, 0, 1, 0, 1, 3],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 1, 0, 0, 2],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, -1],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, -1],
    ![0, 0, 0, 0, 1, 0, 1, 3],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 0, 0, 0, 1, 1, 0, -1],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, 0, -1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![1, 1, 1, 0, 1, 1, 0, -2],
    ![0, -1, 0, 0, 0, 0, 0, 1],
    ![0, 0, -1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 1],
    ![0, 0, 0, 0, 0, -1, 0, 1],
    ![0, 1, 1, 0, 1, 1, 1, -2],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 1, 0, 0, 1, 1, 2],
    ![0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, -1],
    ![0, 0, 0, 0, 1, 0, 0, -1],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![1, 0, 1, 0, 0, 1, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![0, 1, 1, 1, 0, 0, 1, -1],
    ![0, -1, 0, 0, 0, 0, 0, 1],
    ![0, 0, -1, 0, 0, 0, 0, 1],
    ![0, 0, 0, -1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![-1, 0, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1]],
    ![![1, 3, 0, 0, 0, 0, 0, 0],
    ![0, -1, 0, 0, 0, 0, 0, 0],
    ![0, -1, 1, 0, 0, 0, 0, 0],
    ![0, -1, 0, 1, 0, 0, 0, 0],
    ![0, -1, 0, 0, 1, 0, 0, 0],
    ![-1, -2, -1, -1, -1, -1, -1, 0],
    ![0, 4, 0, 0, 0, 0, 1, 0],
    ![0, -2, 0, 0, 0, 0, 0, 1]],
    ![![0, 1, 0, 0, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 1, 0, 0, 0, 1, 0],
    ![-1, -1, -1, -1, -1, -1, -1, 0],
    ![1, 0, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![2, -1, -1, -1, -1, -1, -3, 0],
    ![-1, 1, 0, 0, 0, 0, 1, 0],
    ![-1, 0, 0, 0, 0, 1, 1, 0],
    ![-1, 0, 0, 0, 0, 0, 1, 0],
    ![-1, 0, 1, 0, 0, 0, 1, 0],
    ![-1, 0, 0, 1, 0, 0, 1, 0],
    ![4, 0, 0, 0, 0, 0, -3, 0],
    ![-2, 0, 0, 0, 0, 0, 2, 1]],
    ![![0, -1, -1, -1, -2, -2, -1, 1],
    ![0, 1, 0, 1, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1, 0, -1],
    ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![-1, -1, -1, -2, -3, -3, -1, 1],
    ![0, 0, 0, 1, 1, 1, 0, -1]]]

/-- Reduction of the checked integral root-coordinate matrices. -/
def generatedFifthSectionGeneratorBinary (g : Fin 18) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  (generatedFifthSectionGeneratorInteger g).map (Int.castRingHom (ZMod 2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check all 144 genuine root images in all 24 physical coordinates.
/-- Every displayed root-coordinate image matches the actual physical generator numerator. -/
theorem generatedFifthSectionGenerator_root_certificate :
    ∀ g : Fin 18, ∀ j : Fin 8, ∀ i : Fin 24,
      (generatedFifthSectionGeneratorNumerator g *ᵥ
        generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j)) i =
      2 * generatedFifthFrameInsert
        (generatedOctadIntegerRootMatrix *ᵥ (generatedFifthSectionGeneratorInteger g).col j) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check the genuine twelve encoder sign actions on all eight roots.
/-- The original Golay generator signs have precisely the displayed integer root images. -/
theorem generatedFifthSectionGenerator_sign_certificate :
    ∀ k : Fin 12, ∀ j : Fin 8, ∀ i : Fin 24,
      golayIntegerSign (golayEncoder (Pi.single k 1))
          (generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j)) i =
        generatedFifthFrameInsert (generatedOctadIntegerRootMatrix *ᵥ
          (generatedFifthSectionGeneratorInteger ⟨k.val, by omega⟩).col j) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check the five genuine physical selected permutation actions on all eight roots.
/-- The displayed integral root image has the actual selected permutation coordinates. -/
theorem generatedFifthSectionGenerator_permutation_certificate :
    ∀ k : Fin 5, ∀ j : Fin 8, ∀ i : Fin 24,
      generatedFifthFrameInsert (generatedOctadIntegerRootMatrix *ᵥ
          (generatedFifthSectionGeneratorInteger ⟨12 + k.val, by omega⟩).col j)
          (generatedFifthSelectedOctadForward k i) =
        generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j) i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check actual Xi integral-basis coordinates rather than rounded physical coordinates.
/-- The actual previously proved Xi lattice matrix has the displayed root-coordinate action. -/
theorem generatedFifthSectionGenerator_xi_certificate : ∀ j : Fin 8,
    co1XiBasisMatrix *ᵥ generatedFifthFrameIntegerMatrix.col j =
      generatedFifthFrameIntegerMatrix *ᵥ (generatedFifthSectionGeneratorInteger 17).col j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
