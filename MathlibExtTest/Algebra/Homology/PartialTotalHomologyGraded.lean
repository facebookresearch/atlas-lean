/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

import MathlibExt.Algebra.Homology.PartialTotalHomologyGraded

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example : partialTotalHomologyPreviousIndex 0 = ((-1 : ℤ) : EInt) := by
  simp

example (p : ℕ) :
    partialTotalHomologyPreviousIndex (p + 1) = ((p : ℤ) : EInt) := by
  simp

example (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj
        (partialTotalHomologyPreviousIndex p) ⟶
      (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) :=
  B.partialTotalHomologyFiltrationAdjacentHom n p

example (n p : ℕ) :
    B.partialTotalHomologyFiltrationAdjacentHom n p ≫
        (B.partialTotalHomologyFiltration n).ι.app ((p : ℤ) : EInt) =
      (B.partialTotalHomologyFiltration n).ι.app
        (partialTotalHomologyPreviousIndex p) :=
  B.partialTotalHomologyFiltrationAdjacentHom_comp_ι n p

example (n p : ℕ) :
    Mono (B.partialTotalHomologyFiltrationAdjacentHom n p) :=
  inferInstance

example (n p : ℕ) : C :=
  B.partialTotalHomologyGradedPiece n p

example (n p : ℕ) :
    (B.partialTotalHomologyGradedShortComplex n p).ShortExact :=
  B.partialTotalHomologyGradedShortComplex_shortExact n p

example (n : ℕ) : IsIso (B.partialTotalHomologyGradedπ n 0) :=
  B.isIso_partialTotalHomologyGradedπ_zero n

example (n : ℕ) :
    IsZero ((B.partialTotalHomologyFiltration n).obj
      ((-1 : ℤ) : EInt)) :=
  B.isZero_partialTotalHomologyFiltration_obj_of_neg n (-1) (by omega)

example (n : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((0 : ℤ) : EInt) ≅
      B.partialTotalHomologyGradedPiece n 0 :=
  B.partialTotalHomologyGradedZeroIso n

example (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app
      ((n : ℤ) : EInt)) :=
  B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le n _ le_rfl

example (n p : ℕ) (h : n ≤ p) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app
      ((p : ℤ) : EInt)) :=
  B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le n _ (by
    simp only [WithBotTop.coe_le_coe]
    exact_mod_cast h)

example (n : ℕ) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app ⊤) :=
  B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le n _ (by simp)

example (n : ℕ) :
    IsZero (B.partialTotalHomologyGradedPiece n (n + 1)) :=
  B.isZero_partialTotalHomologyGradedPiece_of_degree_lt n (n + 1) (by omega)

example (n : ℕ) :
    IsIso (B.partialTotalHomologyFiltrationAdjacentHom n (n + 1)) :=
  B.isIso_partialTotalHomologyFiltrationAdjacentHom_of_degree_lt
    n (n + 1) (by omega)

example (n : ℕ) :
    IsZero (B.partialTotalHomologyGradedPiece n (n + 2)) :=
  B.isZero_partialTotalHomologyGradedPiece_of_degree_lt n (n + 2) (by omega)

example : IsZero (B.partialTotalHomologyGradedPiece 0 1) :=
  B.isZero_partialTotalHomologyGradedPiece_of_degree_lt 0 1 (by omega)

example (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    image (HomologicalComplex.homologyMap (B.partialTotalι p) n) ⟶
      image (HomologicalComplex.homologyMap (B.partialTotalι p') n) :=
  B.partialTotalHomologyFiltrationImageMap n h

example (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalHomologyFiltrationImageMap n h ≫
        image.ι (HomologicalComplex.homologyMap
          (B.partialTotalι p') n) =
      image.ι (HomologicalComplex.homologyMap
        (B.partialTotalι p) n) :=
  B.partialTotalHomologyFiltrationImageMap_comp_ι n h

example (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    (B.partialTotalHomologyFiltration n).diagram.map
          (homOfLE (show ((p : ℤ) : EInt) ≤
            ((p' : ℤ) : EInt) by simpa using h)) ≫
        (B.partialTotalHomologyFiltrationObjIsoImage n p').hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n p).hom ≫
        B.partialTotalHomologyFiltrationImageMap n h :=
  B.partialTotalHomologyFiltrationObjIsoImage_naturality n h

example (n m : ℕ) :
    B.partialTotalHomologyGradedPiece n (m + 1) ≅
      cokernel (B.partialTotalHomologyFiltrationImageMap n
        (Nat.le_succ m)) :=
  B.partialTotalHomologyGradedPieceSuccIsoImageCokernel n m

example (n m : ℕ) :
    B.partialTotalHomologyGradedπ n (m + 1) ≫
        (B.partialTotalHomologyGradedPieceSuccIsoImageCokernel n m).hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n (m + 1)).hom ≫
        cokernel.π (B.partialTotalHomologyFiltrationImageMap n
          (Nat.le_succ m)) :=
  B.partialTotalHomologyGradedπ_comp_succIsoImageCokernel_hom n m

example (n : ℕ) :
    B.partialTotalHomologyGradedPiece n 0 ≅
      image (HomologicalComplex.homologyMap (B.partialTotalι 0) n) :=
  B.partialTotalHomologyGradedPieceZeroIsoImage n

example (n : ℕ) :
    B.partialTotalHomologyGradedπ n 0 ≫
        (B.partialTotalHomologyGradedPieceZeroIsoImage n).hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n 0).hom :=
  B.partialTotalHomologyGradedπ_zero_comp_zeroIsoImage_hom n

end HomologicalComplex₂

end
