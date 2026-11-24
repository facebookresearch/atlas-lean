/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralizedHorn
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet

-- The complete Arrow isomorphism retains both original ambient maps.
example {n : ℕ} (D : (Δ[n + 1] : SSet.{u}).Subcomplex) (t : Fin (n + 2)) :
    (stdSimplex.facePreimageArrowIso D t).hom.left ≫
        (stdSimplex.face {t}ᶜ ⊓ D).ι =
      (D.preimage (stdSimplex.δ t)).ι ≫ stdSimplex.δ t :=
  stdSimplex.facePreimageArrowIso_hom_left_ι D t

example {n : ℕ} (D : (Δ[n + 1] : SSet.{u}).Subcomplex) (t : Fin (n + 2)) :
    (stdSimplex.facePreimageArrowIso D t).hom.right ≫ (stdSimplex.face {t}ᶜ).ι =
      stdSimplex.δ t := by
  rw [stdSimplex.facePreimageArrowIso_hom_right,
    stdSimplex.faceSingletonComplIso_hom_ι]

-- Omitting one face specializes to the original horn.
example (n : ℕ) (i : Fin (n + 1)) : generalizedHorn.{u} n {i} = horn n i :=
  generalizedHorn_singleton n i

-- The original one-face enlargement is a native pushout with its literal point.
example {n : ℕ} (S : Finset (Fin (n + 1))) (t : Fin (n + 1)) (ht : t ∉ S) :
    let sq := generalizedHorn_insert_bicart_sq.{u} S t ht
    IsPushout (Subcomplex.homOfLE sq.le₁₂) (Subcomplex.homOfLE sq.le₁₃)
      (Subcomplex.homOfLE sq.le₂₄) (Subcomplex.homOfLE sq.le₃₄) :=
  (generalizedHorn_insert_bicart_sq S t ht).isPushout

-- No omitted faces gives the boundary; omitting every face gives the empty union.
example (n : ℕ) : generalizedHorn.{u} n ∅ = boundary n := by
  rw [boundary_eq_iSup]
  ext d x
  simp [generalizedHorn]

example (n : ℕ) : generalizedHorn.{u} n Finset.univ = ⊥ := by
  ext d x
  simp [generalizedHorn]

-- Zero-dimensional face unions are empty, including the empty omitted set.
example : generalizedHorn.{u} 0 ∅ = ⊥ := by
  ext d x
  simp [generalizedHorn]
  have h : ({0}ᶜ : Finset (Fin 1)) = ∅ := by decide
  simp [h]

-- A nonendpoint pivot uses the literal inverse-image omitted set.
example : lowerHornIndex (2 : Fin 4) ({0, 2} : Finset (Fin 4)) = {0} := by
  decide

example : (generalizedHorn.{u} 3 ({0, 2} : Finset (Fin 4))).preimage
      (stdSimplex.δ (2 : Fin 4)) = generalizedHorn 2 {0} := by
  rw [generalizedHorn_preimage_δ _ _ (by decide)]
  congr 1

-- If the pivot is included, its preimage is the whole face, so the membership
-- premise of generalizedHorn_preimage_δ cannot be dropped.
example : (generalizedHorn.{u} 2 ({0} : Finset (Fin 3))).preimage
      (stdSimplex.δ (1 : Fin 3)) = ⊤ := by
  rw [Subcomplex.preimage_eq_top_iff, stdSimplex.range_δ]
  exact face_le_generalizedHorn _ _ (by decide)

end SSet
