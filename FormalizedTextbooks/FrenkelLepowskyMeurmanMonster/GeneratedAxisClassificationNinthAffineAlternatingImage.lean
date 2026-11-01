/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Two finite nine-fiber images and literal words realizing every three-cycle.
Actual spatial and full-axis lift certificates remain separate prerequisites. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Nine-fiber images of two original spatial Schreier words. -/
def generatedNinthAffineAlternatingForward : Fin 2 → Fin 9 → Fin 9 :=
  ![![4, 3, 8, 1, 0, 5, 2, 7, 6],
    ![3, 5, 6, 8, 7, 1, 0, 4, 2]]

/-- Literal inverse coordinate arrays of the two displayed finite images. -/
def generatedNinthAffineAlternatingInverse : Fin 2 → Fin 9 → Fin 9 :=
  ![![4, 3, 6, 1, 0, 5, 8, 7, 2],
    ![6, 5, 8, 0, 7, 1, 2, 4, 3]]

/-- Both nine-coordinate arrays certify genuine inverse permutations. -/
theorem generatedNinth_affine_alternating_inverse : ∀ (g : Fin 2) (i : Fin 9),
    generatedNinthAffineAlternatingInverse g (generatedNinthAffineAlternatingForward g i) = i ∧
      generatedNinthAffineAlternatingForward g (generatedNinthAffineAlternatingInverse g i) =
        i := by
  decide +kernel

/-- The original two finite images as actual permutations of the nine fiber positions. -/
def generatedNinthAffineAlternatingPermutation (g : Fin 2) : Equiv.Perm (Fin 9) where
  toFun := generatedNinthAffineAlternatingForward g
  invFun := generatedNinthAffineAlternatingInverse g
  left_inv := fun i => (generatedNinth_affine_alternating_inverse g i).1
  right_inv := fun i => (generatedNinth_affine_alternating_inverse g i).2

/-- Literal original-image words for all168 distinct oriented three-cycles. -/
def generatedNinthAffineThreeCycleWord : Fin 168 → List (Fin 2) :=
  ![[0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1],
    [1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0],
    [1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0],
    [1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1],
    [1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1],
    [1, 0, 0, 1, 0, 0, 1, 1, 0, 0],
    [1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1],
    [1, 0, 0, 1, 0, 0, 1, 1],
    [1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0],
    [1, 1, 1, 1, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    [1, 1, 0, 0, 0, 0, 1, 1, 0, 0],
    [1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1],
    [1, 1, 1, 1, 1, 1, 0, 0, 0, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1],
    [1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1],
    [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1],
    [1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1],
    [1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1],
    [0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0],
    [1, 1, 1, 0, 0, 1],
    [1, 1, 1, 1, 0, 0],
    [1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1],
    [1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1],
    [1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0],
    [1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0],
    [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1],
    [0, 0, 1, 1, 1, 0, 0, 1],
    [0, 0, 1, 1, 1, 1],
    [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    [0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [1, 1, 1, 1, 0, 0, 1, 0, 0, 1],
    [0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    [0, 1, 1, 0, 0, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 0, 1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1],
    [1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 1, 0],
    [1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0],
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
    [0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
    [1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0],
    [0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    [1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0],
    [1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0],
    [0, 1, 1, 1, 1, 1, 1, 0, 0, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1],
    [0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0],
    [0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0],
    [0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0],
    [1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0],
    [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1],
    [0, 1, 0, 0, 1, 1, 1, 0],
    [0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1],
    [0, 1, 1, 1, 1, 1, 0, 0, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0],
    [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1],
    [0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1],
    [1, 1, 0, 0, 1, 0, 0, 1],
    [1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1],
    [1, 0, 0, 1, 1, 0, 0, 0, 0, 1],
    [0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0],
    [0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0],
    [0, 1, 0, 0, 1, 0, 0, 1, 1, 0],
    [1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0],
    [0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 0, 1, 1, 1, 0, 0],
    [0, 1, 1, 1, 0, 0, 1, 0],
    [1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0],
    [0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0],
    [0, 0],
    [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0],
    [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1],
    [0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1],
    [1, 0, 0, 1, 1, 1],
    [0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    [1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [0, 0, 0, 0],
    [1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    [1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0],
    [0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0],
    [1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1],
    [0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1],
    [1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0],
    [1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1],
    [0, 0, 1, 0, 0, 1, 1, 1],
    [1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0],
    [0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1],
    [0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    [1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1],
    [1, 0, 0, 1, 0, 0, 1, 1, 1, 1],
    [1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1],
    [1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0],
    [0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1],
    [0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0],
    [0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0],
    [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0],
    [0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0],
    [1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1],
    [1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0],
    [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1]]

/-- A source-word address for every ordered triple of distinct original fiber positions. -/
def generatedNinthAffineThreeCycleAddress : Fin 9 → Fin 9 → Fin 9 → Fin 168 :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 1, 2, 3, 4, 5, 6],
      ![0, 7, 0, 8, 9, 10, 11, 12, 13],
      ![0, 14, 15, 0, 16, 17, 18, 19, 20],
      ![0, 21, 22, 23, 0, 24, 25, 26, 27],
      ![0, 28, 29, 30, 31, 0, 32, 33, 34],
      ![0, 35, 36, 37, 38, 39, 0, 40, 41],
      ![0, 42, 43, 44, 45, 46, 47, 0, 48],
      ![0, 49, 50, 51, 52, 53, 54, 55, 0]],
    ![![0, 0, 7, 14, 21, 28, 35, 42, 49],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 56, 57, 58, 59, 60, 61],
      ![1, 0, 62, 0, 63, 64, 65, 66, 67],
      ![2, 0, 68, 69, 0, 70, 71, 72, 73],
      ![3, 0, 74, 75, 76, 0, 77, 78, 79],
      ![4, 0, 80, 81, 82, 83, 0, 84, 85],
      ![5, 0, 86, 87, 88, 89, 90, 0, 91],
      ![6, 0, 92, 93, 94, 95, 96, 97, 0]],
    ![![0, 0, 0, 15, 22, 29, 36, 43, 50],
      ![7, 0, 0, 62, 68, 74, 80, 86, 92],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![8, 56, 0, 0, 98, 99, 100, 101, 102],
      ![9, 57, 0, 103, 0, 104, 105, 106, 107],
      ![10, 58, 0, 108, 109, 0, 110, 111, 112],
      ![11, 59, 0, 113, 114, 115, 0, 116, 117],
      ![12, 60, 0, 118, 119, 120, 121, 0, 122],
      ![13, 61, 0, 123, 124, 125, 126, 127, 0]],
    ![![0, 1, 8, 0, 23, 30, 37, 44, 51],
      ![14, 0, 56, 0, 69, 75, 81, 87, 93],
      ![15, 62, 0, 0, 103, 108, 113, 118, 123],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![16, 63, 98, 0, 0, 128, 129, 130, 131],
      ![17, 64, 99, 0, 132, 0, 133, 134, 135],
      ![18, 65, 100, 0, 136, 137, 0, 138, 139],
      ![19, 66, 101, 0, 140, 141, 142, 0, 143],
      ![20, 67, 102, 0, 144, 145, 146, 147, 0]],
    ![![0, 2, 9, 16, 0, 31, 38, 45, 52],
      ![21, 0, 57, 63, 0, 76, 82, 88, 94],
      ![22, 68, 0, 98, 0, 109, 114, 119, 124],
      ![23, 69, 103, 0, 0, 132, 136, 140, 144],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![24, 70, 104, 128, 0, 0, 148, 149, 150],
      ![25, 71, 105, 129, 0, 151, 0, 152, 153],
      ![26, 72, 106, 130, 0, 154, 155, 0, 156],
      ![27, 73, 107, 131, 0, 157, 158, 159, 0]],
    ![![0, 3, 10, 17, 24, 0, 39, 46, 53],
      ![28, 0, 58, 64, 70, 0, 83, 89, 95],
      ![29, 74, 0, 99, 104, 0, 115, 120, 125],
      ![30, 75, 108, 0, 128, 0, 137, 141, 145],
      ![31, 76, 109, 132, 0, 0, 151, 154, 157],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![32, 77, 110, 133, 148, 0, 0, 160, 161],
      ![33, 78, 111, 134, 149, 0, 162, 0, 163],
      ![34, 79, 112, 135, 150, 0, 164, 165, 0]],
    ![![0, 4, 11, 18, 25, 32, 0, 47, 54],
      ![35, 0, 59, 65, 71, 77, 0, 90, 96],
      ![36, 80, 0, 100, 105, 110, 0, 121, 126],
      ![37, 81, 113, 0, 129, 133, 0, 142, 146],
      ![38, 82, 114, 136, 0, 148, 0, 155, 158],
      ![39, 83, 115, 137, 151, 0, 0, 162, 164],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![40, 84, 116, 138, 152, 160, 0, 0, 166],
      ![41, 85, 117, 139, 153, 161, 0, 167, 0]],
    ![![0, 5, 12, 19, 26, 33, 40, 0, 55],
      ![42, 0, 60, 66, 72, 78, 84, 0, 97],
      ![43, 86, 0, 101, 106, 111, 116, 0, 127],
      ![44, 87, 118, 0, 130, 134, 138, 0, 147],
      ![45, 88, 119, 140, 0, 149, 152, 0, 159],
      ![46, 89, 120, 141, 154, 0, 160, 0, 165],
      ![47, 90, 121, 142, 155, 162, 0, 0, 167],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0],
      ![48, 91, 122, 143, 156, 163, 166, 0, 0]],
    ![![0, 6, 13, 20, 27, 34, 41, 48, 0],
      ![49, 0, 61, 67, 73, 79, 85, 91, 0],
      ![50, 92, 0, 102, 107, 112, 117, 122, 0],
      ![51, 93, 123, 0, 131, 135, 139, 143, 0],
      ![52, 94, 124, 144, 0, 150, 153, 156, 0],
      ![53, 95, 125, 145, 157, 0, 161, 163, 0],
      ![54, 96, 126, 146, 158, 164, 0, 166, 0],
      ![55, 97, 127, 147, 159, 165, 167, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The finite original-image product named by a source word. -/
def generatedNinthAffineAlternatingWordPermutation (w : List (Fin 2)) : Equiv.Perm (Fin 9) :=
  (w.map generatedNinthAffineAlternatingPermutation).prod

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Bind every three-cycle on all nine original positions.
/-- Every ordered distinct triple has its entire literal three-cycle source-word action. -/
theorem generatedNinth_affine_three_cycle_word_coordinate : ∀ (a b c i : Fin 9),
    a ≠ b → b ≠ c → a ≠ c →
      generatedNinthAffineAlternatingWordPermutation
        (generatedNinthAffineThreeCycleWord (generatedNinthAffineThreeCycleAddress a b c)) i =
          (Equiv.swap a b * Equiv.swap b c) i := by
  decide +kernel

/-- The two displayed original images are even permutations. -/
theorem generatedNinth_affine_alternating_permutation_even : ∀ g : Fin 2,
    generatedNinthAffineAlternatingPermutation g ∈ alternatingGroup (Fin 9) := by
  simp_rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

/-- Every original-image source word belongs to the subgroup generated by the two images. -/
theorem generatedNinth_affine_alternating_word_mem (w : List (Fin 2)) :
    generatedNinthAffineAlternatingWordPermutation w ∈
      Subgroup.closure (Set.range generatedNinthAffineAlternatingPermutation) := by
  unfold generatedNinthAffineAlternatingWordPermutation
  apply Subgroup.list_prod_mem
  intro p hp
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hp
  exact Subgroup.subset_closure ⟨g, rfl⟩

/-- The two actual finite images generate the entire alternating group on the nine fibers. -/
theorem generatedNinth_affine_alternating_image_eq :
    Subgroup.closure (Set.range generatedNinthAffineAlternatingPermutation) =
      alternatingGroup (Fin 9) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨g, rfl⟩
    exact generatedNinth_affine_alternating_permutation_even g
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hp.card_support]; decide)
    have hn := hp.nodup_iff_mem_support.mpr ha
    have hab : a ≠ p a := by grind
    have hbc : p a ≠ p (p a) := by grind
    have hac : a ≠ p (p a) := by grind
    have he : generatedNinthAffineAlternatingWordPermutation
        (generatedNinthAffineThreeCycleWord
          (generatedNinthAffineThreeCycleAddress a (p a) (p (p a)))) =
        Equiv.swap a (p a) * Equiv.swap (p a) (p (p a)) := by
      apply Equiv.ext
      intro i
      exact generatedNinth_affine_three_cycle_word_coordinate a (p a) (p (p a)) i hab hbc hac
    have hm := generatedNinth_affine_alternating_word_mem
      (generatedNinthAffineThreeCycleWord
        (generatedNinthAffineThreeCycleAddress a (p a) (p (p a))))
    rw [he, ← hp.eq_swap_mul_swap_iff_mem_support.mpr ha] at hm
    exact hm

/-- The proved original-image subgroup has exactly181440 elements. -/
theorem generatedNinth_affine_alternating_image_card :
    Nat.card (Subgroup.closure (Set.range generatedNinthAffineAlternatingPermutation)) =
      181440 := by
  rw [generatedNinth_affine_alternating_image_eq, nat_card_alternatingGroup,
    Nat.card_fin]
  decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
