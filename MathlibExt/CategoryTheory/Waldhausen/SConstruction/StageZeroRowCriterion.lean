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

public import MathlibExt.CategoryTheory.Waldhausen.CofiberCompositeQuotient
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage

/-!
# General finite stages from their original zero-row quotients

For `A : Ar n ⥤ C`, assume independently that every diagonal value
`A(i,i)` is zero and that `A(0,i) ⟶ A(0,j) ⟶ A(i,j)` is a cofiber row
for every `i ≤ j`, including equality. These hypotheses imply every
cofiber triple `A(i,j) ⟶ A(i,k) ⟶ A(j,k)` with `i ≤ j ≤ k`.
The quotient row of a composite cofibration supplies the arbitrary triple.
This uses a Waldhausen structure without gluing, not an
admissible-monomorphism flag or exact-category reconstruction.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let `C` have a zero object and a Waldhausen structure without gluing,
and let `A : Ar n ⥤ C`. Assume independently that `A.obj (diag i)` is
zero for every `i : Fin (n + 1)`. Also assume, for every `i ≤ j`, including
`i = j`, that the maps `A(0,i) ⟶ A(0,j) ⟶ A(i,j)` form a cofiber sequence:
its legs are `A.map (horiz (Fin.zero_le i) hij)` and
`A.map (vert (Fin.zero_le i) hij)`. Then `IsStage n A` holds, giving a
cofiber sequence `A(i,j) ⟶ A(i,k) ⟶ A(j,k)` for every `i ≤ j ≤ k`.
The diagonal-zero assumption is separate from the zero-row cofiber data. -/
theorem isStage_of_zeroRowCofiber {n : ℕ} (A : Ar n ⥤ C)
    (hDiag : ∀ i, IsZero (A.obj (diag i)))
    (hRow : ∀ {i j : Fin (n + 1)} (hij : i ≤ j),
      IsCofiberSequence (A.map (horiz (Fin.zero_le i) hij))
        (A.map (vert (Fin.zero_le i) hij))) : IsStage n A where
  diag_isZero := hDiag
  cofiber_triple {i j k} hij hjk := by
    have hcomp : A.map (horiz (Fin.zero_le i) hij) ≫
        A.map (horiz (Fin.zero_le j) hjk) =
          A.map (horiz (Fin.zero_le i) (hij.trans hjk)) := by
      rw [← A.map_comp]
      exact A.congr_map
        (Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    have hIJ := hRow (hij.trans hjk)
    rw [← hcomp] at hIJ
    have hα : A.map (vert (Fin.zero_le i) hij) ≫ A.map (horiz hij hjk) =
        A.map (horiz (Fin.zero_le j) hjk) ≫
          A.map (vert (Fin.zero_le i) (hij.trans hjk)) := by
      calc
        A.map (vert (Fin.zero_le i) hij) ≫ A.map (horiz hij hjk) =
            A.map (vert (Fin.zero_le i) hij ≫ horiz hij hjk) :=
          (A.map_comp _ _).symm
        _ = A.map (horiz (Fin.zero_le j) hjk ≫
            vert (Fin.zero_le i) (hij.trans hjk)) :=
          A.congr_map
            (Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))
        _ = A.map (horiz (Fin.zero_le j) hjk) ≫
            A.map (vert (Fin.zero_le i) (hij.trans hjk)) := A.map_comp _ _
    have hβ : A.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫
        A.map (vert hij hjk) = A.map (vert (Fin.zero_le j) hjk) := by
      calc
        A.map (vert (Fin.zero_le i) (hij.trans hjk)) ≫ A.map (vert hij hjk) =
            A.map (vert (Fin.zero_le i) (hij.trans hjk) ≫ vert hij hjk) :=
          (A.map_comp _ _).symm
        _ = A.map (vert (Fin.zero_le j) hjk) :=
          A.congr_map
            (Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    exact IsCofiberSequence.quotient_comp (hRow hij) hIJ (hRow hjk) hα hβ

end CategoryTheory.Waldhausen.SConstruction
