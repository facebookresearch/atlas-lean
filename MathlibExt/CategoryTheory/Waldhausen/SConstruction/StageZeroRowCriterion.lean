/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.CofiberCompositeQuotient
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage

/-!
# General finite stages from their original zero-row quotients

Zero diagonal values and actual cofiber rows from (0,i) through (0,j) to
(i,j) imply every cofiber triple of the full diagram. The quotient row of
a composite cofibration supplies the arbitrary i≤j≤k triple. This is a
general Waldhausen argument and uses no admissible-monomorphism flag or
exact-category reconstruction.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- The original zero-row cofiber pushouts determine the full finite
stage predicate, without a caller arbitrary-triple conclusion. -/
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
