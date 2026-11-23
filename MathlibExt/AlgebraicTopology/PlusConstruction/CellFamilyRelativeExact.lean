/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceIsIso
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFamilyRelativeHomology
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerExactness

/-!
# Exact sequence for actual cell-family attachments

The actual relative homology calculation for an arbitrary family of
`(n + 1)`-cells is inserted into the long exact homology sequence of its
original-space inclusion.  Adjacent relative vanishing gives the expected
absolute homology isomorphisms.  At the cell dimension the inclusion is
monic, one degree below it is epic, and the two central exact pairs are
written in the canonical family coproduct coordinate.

No splitting of either exact pair is chosen.  No connectedness, normality,
perfectness, spherical representative, or plus-construction hypothesis is
used.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology.CWComplex
  TopPair.HomologyTheoryData.IsExact

universe u

namespace AlgebraicTopology.CellFamilyAttachment

variable {ι : Type u} (X : TopCat.{u}) (n : ℕ)
variable (a : ι → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X))

/-- The actual attachment pair used throughout the family exact sequence. -/
abbrev relativeExactPair : TopPair.{u} :=
  CellCollarDeformation.attachmentPair X n a

/-- Integer-graded singular homology with the selected coefficient object. -/
abbrev relativeExactTheory (R : AddCommGrpCat.{u}) :=
  singularHomologyIntData AddCommGrpCat.{u} R

/-- The family coproduct coordinate in the integer cell degree.  It is the
already constructed natural-graded coordinate followed by the inverse of the
canonical natural-to-integer comparison. -/
noncomputable def attachmentRelativeDiagonalIntIso
    (R : AddCommGrpCat.{u}) :
    (∐ fun _ : ι => R) ≅
      ((relativeExactTheory R).Hₚ ((n + 1 : ℕ) : ℤ)).obj
        (relativeExactPair X n a) :=
  attachmentRelativeDiagonalIso X n a R ≪≫
    ((relativeSingularHomologyNatToIntIso
      AddCommGrpCat.{u} R (n + 1)).app (relativeExactPair X n a)).symm

/-- Returning the integer coordinate to natural grading recovers the original
family diagonal coordinate exactly. -/
@[reassoc]
theorem attachmentRelativeDiagonalIntIso_hom_comp_natToInt
    (R : AddCommGrpCat.{u}) :
    (attachmentRelativeDiagonalIntIso X n a R).hom ≫
        (relativeSingularHomologyNatToIntIso
          AddCommGrpCat.{u} R (n + 1)).hom.app (relativeExactPair X n a) =
      (attachmentRelativeDiagonalIso X n a R).hom := by
  simp [attachmentRelativeDiagonalIntIso]

private theorem attachment_isIso_natOfInt
    (R : AddCommGrpCat.{u}) (k : ℕ)
    (h : IsIso ((relativeExactTheory R).subspaceMap
      (k : ℤ) (relativeExactPair X n a))) :
    IsIso (((singularHomologyFunctor AddCommGrpCat.{u} k).obj R).map
      (relativeExactPair X n a).map) := by
  have hEq :
      (relativeExactTheory R).subspaceMap (k : ℤ) (relativeExactPair X n a) =
        ((relativeExactTheory R).H (k : ℤ)).map (relativeExactPair X n a).map :=
    rfl
  rw [hEq, singularHomologyIntData_H] at h
  have hnat :=
    (singularHomologyNatToIntIso AddCommGrpCat.{u} R k).hom.naturality
      (relativeExactPair X n a).map
  have hcomp : IsIso
      ((singularHomologyIntFunctor AddCommGrpCat.{u} R (k : ℤ)).map
          (relativeExactPair X n a).map ≫
        (singularHomologyNatToIntIso
          AddCommGrpCat.{u} R k).hom.app (relativeExactPair X n a).fst) :=
    inferInstance
  rw [hnat] at hcomp
  exact IsIso.of_isIso_comp_left
    ((singularHomologyNatToIntIso
      AddCommGrpCat.{u} R k).hom.app (relativeExactPair X n a).snd) _

private theorem attachment_epi_natOfInt
    (R : AddCommGrpCat.{u}) (k : ℕ)
    (h : Epi ((relativeExactTheory R).subspaceMap
      (k : ℤ) (relativeExactPair X n a))) :
    Epi (((singularHomologyFunctor AddCommGrpCat.{u} k).obj R).map
      (relativeExactPair X n a).map) := by
  have hEq :
      (relativeExactTheory R).subspaceMap (k : ℤ) (relativeExactPair X n a) =
        ((relativeExactTheory R).H (k : ℤ)).map (relativeExactPair X n a).map :=
    rfl
  rw [hEq, singularHomologyIntData_H] at h
  have hnat :=
    (singularHomologyNatToIntIso AddCommGrpCat.{u} R k).hom.naturality
      (relativeExactPair X n a).map
  have hcomp : Epi
      ((singularHomologyIntFunctor AddCommGrpCat.{u} R (k : ℤ)).map
          (relativeExactPair X n a).map ≫
        (singularHomologyNatToIntIso
          AddCommGrpCat.{u} R k).hom.app (relativeExactPair X n a).fst) :=
    inferInstance
  rw [hnat] at hcomp
  exact epi_of_epi
    ((singularHomologyNatToIntIso
      AddCommGrpCat.{u} R k).hom.app (relativeExactPair X n a).snd) _

private theorem attachment_mono_natOfInt
    (R : AddCommGrpCat.{u}) (k : ℕ)
    (h : Mono ((relativeExactTheory R).subspaceMap
      (k : ℤ) (relativeExactPair X n a))) :
    Mono (((singularHomologyFunctor AddCommGrpCat.{u} k).obj R).map
      (relativeExactPair X n a).map) := by
  have hEq :
      (relativeExactTheory R).subspaceMap (k : ℤ) (relativeExactPair X n a) =
        ((relativeExactTheory R).H (k : ℤ)).map (relativeExactPair X n a).map :=
    rfl
  rw [hEq, singularHomologyIntData_H] at h
  have hnat :=
    (singularHomologyNatToIntIso AddCommGrpCat.{u} R k).hom.naturality
      (relativeExactPair X n a).map
  have hcomp : Mono
      ((singularHomologyIntFunctor AddCommGrpCat.{u} R (k : ℤ)).map
          (relativeExactPair X n a).map ≫
        (singularHomologyNatToIntIso
          AddCommGrpCat.{u} R k).hom.app (relativeExactPair X n a).fst) :=
    inferInstance
  rw [hnat] at hcomp
  exact (mono_comp_iff_of_isIso _ _).mp hcomp

/-- The original-space inclusion is an isomorphism on `k`th homology whenever
the relative groups in degrees `k + 1` and `k` both vanish. -/
theorem isIso_attachmentSubspaceMap_of_isZero_relative
    (R : AddCommGrpCat.{u}) (k : ℕ)
    (hSucc : IsZero
      ((relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R
        ((k : ℤ) + 1)).obj (relativeExactPair X n a)))
    (hSelf : IsZero
      ((relativeSingularHomologyIntFunctor AddCommGrpCat.{u} R
        (k : ℤ)).obj (relativeExactPair X n a))) :
    IsIso (((singularHomologyFunctor AddCommGrpCat.{u} k).obj R).map
      (relativeExactPair X n a).map) := by
  have hIso := isIso_subspaceMap_of_isZero_relative
    (relativeExactTheory R) (k : ℤ) (relativeExactPair X n a) hSucc hSelf
  exact attachment_isIso_natOfInt X n a R k hIso

/-- Away from the two degrees adjacent to the cells, the original-space
inclusion induces an isomorphism on homology. -/
theorem isIso_attachmentSubspaceMap_of_ne_cellDimension
    (R : AddCommGrpCat.{u}) (k : ℕ)
    (hSucc : (k : ℤ) + 1 ≠ ((n + 1 : ℕ) : ℤ))
    (hSelf : (k : ℤ) ≠ ((n + 1 : ℕ) : ℤ)) :
    IsIso (((singularHomologyFunctor AddCommGrpCat.{u} k).obj R).map
      (relativeExactPair X n a).map) := by
  apply isIso_attachmentSubspaceMap_of_isZero_relative X n a R k
  · exact isZero_attachmentRelativeHomologyInt_of_ne
      X n a R ((k : ℤ) + 1) hSucc
  · exact isZero_attachmentRelativeHomologyInt_of_ne
      X n a R (k : ℤ) hSelf

/-- Attaching an arbitrary family of `(n + 1)`-cells induces an epimorphism
on `n`th homology. -/
theorem epi_attachmentSubspaceMap_pred
    (R : AddCommGrpCat.{u}) :
    Epi (((singularHomologyFunctor AddCommGrpCat.{u} n).obj R).map
      (relativeExactPair X n a).map) := by
  have hk : (n : ℤ) ≠ ((n + 1 : ℕ) : ℤ) := by
    push_cast
    omega
  have hZero := isZero_attachmentRelativeHomologyInt_of_ne
    X n a R (n : ℤ) hk
  have hExact := exact_subspaceMap_toRelative
    (relativeExactTheory R) (n : ℤ) (relativeExactPair X n a)
  have hEpi := hExact.epi_f (hZero.eq_of_tgt _ _)
  exact attachment_epi_natOfInt X n a R n hEpi

/-- Attaching an arbitrary family of `(n + 1)`-cells induces a monomorphism
on `(n + 1)`st homology. -/
theorem mono_attachmentSubspaceMap_top
    (R : AddCommGrpCat.{u}) :
    Mono (((singularHomologyFunctor AddCommGrpCat.{u} (n + 1)).obj R).map
      (relativeExactPair X n a).map) := by
  have hdeg : ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have hk : ((n + 2 : ℕ) : ℤ) ≠ ((n + 1 : ℕ) : ℤ) := by
    push_cast
    omega
  have hZero := isZero_attachmentRelativeHomologyInt_of_ne
    X n a R ((n + 2 : ℕ) : ℤ) hk
  have hExact := exact_boundary_subspaceMap
    (relativeExactTheory R) ((n + 2 : ℕ) : ℤ) (relativeExactPair X n a)
  have hMonoPrev : Mono ((relativeExactTheory R).subspaceMap
      (((n + 2 : ℕ) : ℤ) - 1) (relativeExactPair X n a)) :=
    hExact.mono_g (hZero.eq_of_src _ _)
  rw [hdeg] at hMonoPrev
  exact attachment_mono_natOfInt X n a R (n + 1) hMonoPrev

/-- In the family coproduct coordinate, the relative boundary followed by
the inclusion-induced map is exact at `H_n(X)`. -/
theorem exact_attachment_diagonal_boundary
    (R : AddCommGrpCat.{u}) :
    (ShortComplex.mk
      ((attachmentRelativeDiagonalIntIso X n a R).hom ≫
        (relativeExactTheory R).boundary
          ((n + 1 : ℕ) : ℤ) (relativeExactPair X n a))
      ((relativeExactTheory R).subspaceMap
        (((n + 1 : ℕ) : ℤ) - 1) (relativeExactPair X n a))
      (by
        rw [Category.assoc, boundary_comp_subspaceMap,
          Limits.comp_zero])).Exact := by
  have hExact := exact_boundary_subspaceMap
    (relativeExactTheory R) ((n + 1 : ℕ) : ℤ) (relativeExactPair X n a)
  refine ShortComplex.exact_of_iso ?_ hExact
  refine ShortComplex.isoMk
    (attachmentRelativeDiagonalIntIso X n a R).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ <;>
  simp only [Iso.refl_hom, Iso.symm_hom, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- In the family coproduct coordinate, the inclusion-induced map followed
by the absolute-to-relative map is exact at `H_{n+1}` of the attachment. -/
theorem exact_attachment_toRelative_diagonal
    (R : AddCommGrpCat.{u}) :
    (ShortComplex.mk
      ((relativeExactTheory R).subspaceMap
        ((n + 1 : ℕ) : ℤ) (relativeExactPair X n a))
      ((relativeExactTheory R).toRelative
          ((n + 1 : ℕ) : ℤ) (relativeExactPair X n a) ≫
        (attachmentRelativeDiagonalIntIso X n a R).inv)
      (by
        rw [← Category.assoc, subspaceMap_comp_toRelative,
          Limits.zero_comp])).Exact := by
  have hExact := exact_subspaceMap_toRelative
    (relativeExactTheory R) ((n + 1 : ℕ) : ℤ) (relativeExactPair X n a)
  refine ShortComplex.exact_of_iso ?_ hExact
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (attachmentRelativeDiagonalIntIso X n a R).symm ?_ ?_ <;>
  simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp,
    Category.comp_id]

end AlgebraicTopology.CellFamilyAttachment

end

end
