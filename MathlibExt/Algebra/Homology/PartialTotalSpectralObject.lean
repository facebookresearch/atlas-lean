/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalEIntFiltration
public import MathlibExt.Algebra.Homology.PartialTotalStepHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-!
# The spectral object of the partial-total filtration

The cochain partial-total filtration gives a mapping-cone spectral
object in the homotopy category and in the abelian coefficient category.
Its H functor on an interval is identified with mapping-cone homology.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The extended-integer partial-total filtration, regraded from chain degree
`n` to cochain degree `-n`. -/
noncomputable def partialTotalCochainFiltration :
    EInt ⥤ CochainComplex C ℤ :=
  B.partialTotalEIntFiltration ⋙
    ComplexShape.embeddingDownNat.extendFunctor C

/-- The mapping-cone spectral object of the partial-total cochain
filtration, valued in the homotopy category. -/
noncomputable def partialTotalHomotopySpectralObject :
    CategoryTheory.Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) EInt :=
  (HomotopyCategory.spectralObjectMappingCone C).precomp
    B.partialTotalCochainFiltration

/-- The partial-total spectral object after applying homology of cochain
complexes. -/
noncomputable def partialTotalSpectralObject :
    CategoryTheory.Abelian.SpectralObject C EInt :=
  B.partialTotalHomotopySpectralObject.mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)

set_option backward.isDefEq.respectTransparency false in
/-- The `H n` value of the partial-total spectral object on a filtration
interval is ordinary degree-`n` homology of the corresponding mapping cone. -/
noncomputable def partialTotalSpectralObjectHObjIso
    (n : ℤ) {i j : EInt} (h : i ≤ j) :
    ((B.partialTotalSpectralObject.H n).obj
        (CategoryTheory.ComposableArrows.mk₁ (homOfLE h))) ≅
      (CochainComplex.mappingCone
        (B.partialTotalCochainFiltration.map (homOfLE h))).homology n := by
  change ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).obj
        (CochainComplex.mappingCone
          (B.partialTotalCochainFiltration.map (homOfLE h)))) ≅ _
  exact (HomotopyCategory.homologyFunctorFactors
    C (ComplexShape.up ℤ) n).app _

end HomologicalComplex₂

end
