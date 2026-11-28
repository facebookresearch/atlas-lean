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
# The mapping-cone spectral object of a horizontal filtration

Let C be a preadditive category with a zero object and finite coproducts, and K a bicomplex of
shape (down ℕ,down ℕ). Reindex each horizontal chain stage G_i as an integer cochain complex
F_i by placing degree n in degree −n and setting positive cochain degrees to zero.

The cones Cone(F_i → F_j), for i≤j in ℕ, define a triangulated spectral object in the homotopy
category. Its triangles are the cone composition triangles for i≤j≤k. When C is abelian,
applying cochain homology gives an abelian spectral object whose relative terms are the
homologies of these cones. Object and morphism universes remain independent.
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

/-- Let C be a preadditive category with a zero object and finite coproducts, and K a bicomplex of
shape (down ℕ,down ℕ). Its horizontal filtration diagram G : ℕ → ChainComplex(C,ℕ) gives a
diagram F : ℕ → CochainComplex(C,ℤ) by extension along n ↦ −n. Thus F_i has the term (G_i)_n
in cochain degree −n and zero in positive cochain degrees. The maps F_i → F_j are the extended
horizontal-stage inclusions for i≤j. -/
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

/-- Let C be a preadditive category with a zero object and finite coproducts, and K a bicomplex of
shape (down ℕ,down ℕ). Let F_i be the horizontal stage G_i extended to an integer cochain
complex by chain degree n ↦ cochain degree −n. Precomposing the mapping-cone spectral object
with F gives a triangulated spectral object indexed by ℕ in HomotopyCategory(C,up ℤ). Its
relative object for i≤j is the homotopy-category image of Cone(F_i → F_j), and its triangles
come from composing two stage inclusions. -/
noncomputable def horizontalFiltrationTriangulatedSpectralObject :
    CategoryTheory.Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) ℕ :=
  (HomotopyCategory.spectralObjectMappingCone C).precomp
    (horizontalFiltrationCochainDiagram K)

/-- Let C be a preadditive category with a zero object and finite coproducts, K a bicomplex of
shape (down ℕ,down ℕ), and k,l ∈ ℕ with k≤l. The relative object of the horizontal
triangulated spectral object at the arrow k→l is exactly the image of Cone(F_k → F_l) under
the quotient functor to HomotopyCategory(C,up ℤ). Here F_i is the horizontal chain stage G_i
extended to cochain degree −n from chain degree n. -/
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

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). Applying the
degree-zero homological functor on HomotopyCategory(C,up ℤ) to the horizontal mapping-cone
triangulated spectral object gives an abelian spectral object indexed by ℕ. Its relative terms
in degree s are given by cochain homology of Cone(F_i → F_j), where F_i is the integer cochain
extension of horizontal stage G_i. The connecting maps are induced by the cone composition
triangles. -/
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
