/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotal
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalCoefficientBar

/-!
# Bousfield--Kan homology spectral sequence

The generic first-quadrant bicomplex spectral sequence and its bounded
convergence theorem are specialized to the alternating Bousfield--Kan
bicomplex.  The second page is identified with category homology with the
pointwise homology coefficient system.  For a cofibered functor and its
right-comma diagram, this is the existing strict-fiber homology coefficient
object.

The abutment is homology of the alternating BK total complex.  The generic
bisimplicial Eilenberg--Zilber theorem identifies it with alternating chains
on the existing Bousfield--Kan homotopy-colimit carrier.  Comparison with the
nerve of a total category remains a separate specialization.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

noncomputable section

universe w v

namespace SSet

variable {J : Type w} [Category.{v} J]

/-- First-quadrant homological spectral sequence of the alternating
Bousfield--Kan bicomplex. -/
noncomputable abbrev bkHomologySpectralSequence
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) :=
  HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence
    (bkAlternatingBicomplex AddCommGrpCat.{max w v} R D)

/-- Alternating chains on the existing Bousfield--Kan homotopy-colimit
carrier. -/
noncomputable abbrev bkHocolimAlternatingComplex
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) : ChainComplex AddCommGrpCat.{max w v} ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max w v}).obj
    (bkLinearizedHocolim AddCommGrpCat.{max w v} R D)

/-- Homology of the signed BK total complex is canonically isomorphic to
homology of alternating chains on the BK homotopy colimit. -/
noncomputable def bkTotalHocolimHomologyIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (n : ℕ) :
    (bkAlternatingTotalComplex AddCommGrpCat.{max w v} R D).homology n ≅
      (bkHocolimAlternatingComplex R D).homology n :=
  (bkDiagonalTotalHomologyIso R D n).symm

/-- The second page is category homology with the pointwise homology
coefficient system. -/
noncomputable def bkSecondPageCoefficientHomologyIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (p q : ℕ) :
    ((bkHomologySpectralSequence R D).page 2).X (p, q) ≅
      CategoryTheory.CategoryHomology.homologyWithCoefficients
        (D ⋙ SSet.homologyFunctor R q) p :=
  HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso
      (bkAlternatingBicomplex AddCommGrpCat.{max w v} R D) p q ≪≫
    HomologicalComplex.homologyMapIso
      (bkVerticalHomologyCoefficientBarComplexIso R D q) p ≪≫
    ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := CategoryTheory.CategoryHomology.coefficientBarSimplicial
        (D ⋙ SSet.homologyFunctor R q))).toHomologyIso p).symm

/-- Finite filtration induced on homology of the alternating BK total
complex. -/
noncomputable abbrev bkTotalHomologyFiltration
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (n : ℕ) :=
  HomologicalComplex₂.horizontalTotalHomologyFiltration
    (bkAlternatingBicomplex AddCommGrpCat.{max w v} R D) n

/-- Associated graded piece of homology of the alternating BK total
complex. -/
noncomputable abbrev bkTotalHomologyGradedPiece
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (p q : ℕ) :=
  HomologicalComplex₂.horizontalTotalHomologyGradedPiece
    (bkAlternatingBicomplex AddCommGrpCat.{max w v} R D) p q

/-- Every sufficiently late BK page term is the corresponding associated
graded piece of total BK homology. -/
noncomputable def bkStablePageGradedIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((bkHomologySpectralSequence R D).page r).X (p, q) ≅
      bkTotalHomologyGradedPiece R D p q :=
  HomologicalComplex₂.horizontalStablePageGradedIso
    (bkAlternatingBicomplex AddCommGrpCat.{max w v} R D)
    r hr p q hlower hupper

end SSet

namespace CategoryTheory.Functor.IsCofibered

variable {S X : Type (max w v)} [Category.{v} S] [Category.{v} X]
  {f : X ⥤ S} [f.IsCofibered]

/-- For the right-comma diagram of a cofibered functor, the second page is
category homology with strict-fiber homology coefficients. -/
noncomputable def cofiberedBKSecondPageIso
    (R : AddCommGrpCat.{max w v}) (pDegree qDegree : ℕ) :
    ((SSet.bkHomologySpectralSequence R
      (SSet.rightCommaNerveDiagram f)).page 2).X (pDegree, qDegree) ≅
      fiberHomologyCategoryHomology (p := f) AddCommGrpCat.{max w v} R
        pDegree qDegree :=
  HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso
      (SSet.bkAlternatingBicomplex AddCommGrpCat.{max w v} R
        (SSet.rightCommaNerveDiagram f)) pDegree qDegree ≪≫
    cofiberedVerticalHorizontalHomologyIso (p := f) R pDegree qDegree

end CategoryTheory.Functor.IsCofibered

end
