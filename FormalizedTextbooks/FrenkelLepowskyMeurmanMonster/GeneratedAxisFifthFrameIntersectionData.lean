/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthFrameIntersectionArithmetic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative

/-! Actual eight-root lattice and binary coordinates of the fifth candidate's selected section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Increasing physical coordinates of the actual octad with encoder label 2052. -/
def generatedFifthFramePositions : Fin 8 → Fin 24 := ![0, 1, 2, 3, 16, 17, 18, 19]

/-- Insertion of local coordinates into the actual selected octad. -/
def generatedFifthFrameInsert : (Fin 8 → ℤ) →ₗ[ℤ] (Fin 24 → ℤ) where
  toFun v i := if h : i.val < 4 then v ⟨i.val, by omega⟩ else
    if h : 16 ≤ i.val ∧ i.val < 20 then v ⟨i.val - 12, by omega⟩ else 0
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- Integer coordinates of the actual six differences, sum root, and positive octad root. -/
def generatedFifthFrameIntegerMatrix : Matrix (Fin 24) (Fin 8) ℤ :=
  ![
  ![1, 1, 1, 1, -3, -2, 0, 4],
  ![-1, 0, 0, 0, 1, 0, 1, 0],
  ![0, -1, 0, 0, 0, 0, 0, 0],
  ![0, 0, -1, 0, 1, 1, 0, -1],
  ![0, 0, 0, 0, 0, 1, 0, -1],
  ![0, 0, 0, 0, 1, 1, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 0, -1],
  ![0, 0, 0, 0, 1, 0, 0, -1],
  ![0, 0, 0, 0, 0, 1, 0, -1],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, -1, 1, 1, 0, -1],
  ![0, 0, 0, 0, -2, 0, 0, 1],
  ![0, 0, 0, 0, 0, -2, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0]]

/-- Binary coordinates of the same actual eight lattice roots. -/
def generatedFifthFrameBinaryMatrix : Matrix (Fin 24) (Fin 8) (ZMod 2) :=
  leechHyperbolicInverse * generatedFifthFrameIntegerMatrix.map (Int.castRingHom (ZMod 2))

/-- The displayed integer columns map to the genuine physical local root columns. -/
theorem generatedFifthFrame_integer_matrix_certificate : ∀ j : Fin 8,
    leechBasisMatrix *ᵥ generatedFifthFrameIntegerMatrix.col j =
      generatedFifthFrameInsert (generatedOctadIntegerRootMatrix.col j) := by
  decide +kernel

/-- Each local coordinate inserts into its actual selected physical coordinate. -/
theorem generatedFifthFrame_insert_coordinates : ∀ (v : Fin 8 → ℤ) (j : Fin 8),
    generatedFifthFrameInsert v (generatedFifthFramePositions j) = v j := by
  intro v j
  fin_cases j <;> simp [generatedFifthFrameInsert, generatedFifthFramePositions]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
