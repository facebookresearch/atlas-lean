/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryMatrix

/-! The displayed eight-root data are actual lattice vectors in the selected coordinate section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Eight genuine lattice vectors recovered from their exact integer basis coordinates. -/
def generatedFifthFrameRoot (j : Fin 8) : leechIntegral :=
  leechExplicitCoordinates.symm (generatedFifthFrameIntegerMatrix.col j)

/-- The roots have their actual physical octad coordinates. -/
theorem generatedFifthFrameRoot_physical (j : Fin 8) :
    (generatedFifthFrameRoot j).val =
      generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j) := by
  have h := leechExplicitCoordinates_vector (generatedFifthFrameRoot j)
  rw [generatedFifthFrameRoot, LinearEquiv.apply_symm_apply] at h
  exact h.symm.trans (generatedFifthFrame_integer_matrix_certificate j)

/-- All eight genuine lattice roots have squared physical norm four. -/
theorem generatedFifthFrameRoot_square (j : Fin 8) :
    leechSquareSum (generatedFifthFrameRoot j).val = 32 := by
  rw [generatedFifthFrameRoot_physical]
  have h : ∀ k : Fin 8,
      leechSquareSum (generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col k)) = 32 := by
    decide +kernel
  exact h j

/-- The binary matrix columns are the genuine quotient classes of the eight lattice roots. -/
theorem generatedFifthFrameRoot_binary (j : Fin 8) :
    leechHyperbolicCoordinates (leechReduction (generatedFifthFrameRoot j)) =
      generatedFifthFrameBinaryMatrix.col j := by
  rw [leechHyperbolicCoordinates_explicit, generatedFifthFrameRoot,
    LinearEquiv.apply_symm_apply]
  change leechHyperbolicInverse *ᵥ integerParity (generatedFifthFrameIntegerMatrix.col j) =
    (leechHyperbolicInverse *
      generatedFifthFrameIntegerMatrix.map (Int.castRingHom (ZMod 2))).col j
  rw [Matrix.col_mul_eq_mulVec_col]
  congr 1

/-- Actual binary classes obtained by reducing the integer span of these roots. -/
def generatedFifthFrameBinarySpan : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  generatedFifthFrameBinaryMatrix.mulVecLin.range

/-- Each actual root class lies in the displayed binary span. -/
theorem generatedFifthFrameRoot_mem_binarySpan (j : Fin 8) :
    leechHyperbolicCoordinates (leechReduction (generatedFifthFrameRoot j)) ∈
      generatedFifthFrameBinarySpan := by
  rw [generatedFifthFrameRoot_binary]
  exact ⟨Pi.single j 1, Matrix.mulVec_single_one generatedFifthFrameBinaryMatrix j⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
