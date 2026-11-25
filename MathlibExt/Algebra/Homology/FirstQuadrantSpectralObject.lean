/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationDiagram

/-!
# The spectral object of a first-quadrant total filtration

The canonical horizontal filtration of a first-quadrant total complex gives
a spectral object through Mathlib's mapping-cone construction.  First, the
filtered chain complexes are extended by zero to integer-indexed cochain
complexes.  Precomposing the universal mapping-cone spectral object with this
diagram gives a spectral object in the homotopy category.  In an abelian
category, applying homology gives the corresponding abelian spectral object.

This file constructs the spectral object but makes no page-identification or
convergence claim.  Those require a bounded-complete extension of the
filtration index and separate comparison theorems.
-/

@[expose] public section

open CategoryTheory Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The horizontal filtration diagram, reindexed as integer cochain
complexes by placing chain degree `n` in cochain degree `-n`. -/
noncomputable def horizontalFiltrationCochainDiagram :
    ℕ ⥤ CochainComplex C ℤ :=
  (horizontalTotalFiltration K).diagram ⋙
    ComplexShape.embeddingDownNat.extendFunctor C

@[simp]
theorem horizontalFiltrationCochainDiagram_obj (k : ℕ) :
    (horizontalFiltrationCochainDiagram K).obj k =
      (horizontalFilteredTotalComplex K k).extend
        ComplexShape.embeddingDownNat :=
  rfl

theorem horizontalFiltrationCochainDiagram_map
    {k l : ℕ} (h : k ≤ l) :
    (horizontalFiltrationCochainDiagram K).map (homOfLE h) =
      HomologicalComplex.extendMap
        (horizontalFilteredTotalComplexMap K h)
        ComplexShape.embeddingDownNat :=
  rfl

/-- The mapping-cone spectral object of the horizontal filtration in the
homotopy category of integer cochain complexes. -/
noncomputable def horizontalFiltrationTriangulatedSpectralObject :
    CategoryTheory.Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) ℕ :=
  (HomotopyCategory.spectralObjectMappingCone C).precomp
    (horizontalFiltrationCochainDiagram K)

/-- On a stage inequality, the triangulated spectral object is represented by
the mapping cone of the corresponding extended filtration map. -/
theorem horizontalFiltrationTriangulatedSpectralObject_ω₁_obj
    {k l : ℕ} (h : k ≤ l) :
    (horizontalFiltrationTriangulatedSpectralObject K).ω₁.obj
        (ComposableArrows.mk₁ (homOfLE h)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone
          ((horizontalFiltrationCochainDiagram K).map (homOfLE h))) :=
  rfl

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The abelian spectral object obtained by applying homology to the
mapping-cone spectral object of the horizontal filtration. -/
noncomputable def horizontalFiltrationSpectralObject :
    CategoryTheory.Abelian.SpectralObject C ℕ :=
  (horizontalFiltrationTriangulatedSpectralObject K).mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)

theorem horizontalFiltrationSpectralObject_H (n : ℤ) :
    (horizontalFiltrationSpectralObject K).H n =
      (horizontalFiltrationTriangulatedSpectralObject K).ω₁ ⋙
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).shift n :=
  rfl

end HomologicalComplex₂

end
