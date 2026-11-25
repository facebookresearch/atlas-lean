/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFunctor

/-!
# Naturality of the complete-filtration spectral object

A bicomplex map induces a natural transformation of the complete filtration
diagrams, hence of their mapping-cone functors.  The mapping-cone comparison
commutes with the connecting maps, so it gives a morphism of triangulated
spectral objects.  Applying the existing homological-functor construction
gives the corresponding morphism of abelian spectral objects.

No spectral-sequence or page map is constructed here.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows Pretriangulated

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A bicomplex map induces a natural transformation between the complete
filtration diagrams reindexed as integer cochain complexes. -/
noncomputable def horizontalCompleteFiltrationCochainDiagramNatTrans
    (f : K ⟶ L) :
    horizontalCompleteFiltrationCochainDiagram K ⟶
      horizontalCompleteFiltrationCochainDiagram L :=
  Functor.whiskerRight
    (horizontalCompleteTotalFilteredObjectMap f).natTrans
    (ComplexShape.embeddingDownNat.extendFunctor C)

@[simp]
theorem horizontalCompleteFiltrationCochainDiagramNatTrans_app
    (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteFiltrationCochainDiagramNatTrans f).app i =
      HomologicalComplex.extendMap
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i)
        ComplexShape.embeddingDownNat :=
  rfl

/-- A bicomplex map induces a natural transformation between the mapping-cone
functors of the two complete filtrations. -/
noncomputable def horizontalCompleteFiltrationMappingConeNatTrans
    (f : K ⟶ L) :
    horizontalCompleteFiltrationMappingConeFunctor K ⟶
      horizontalCompleteFiltrationMappingConeFunctor L where
  app D :=
    let η := horizontalCompleteFiltrationCochainDiagramNatTrans f
    CochainComplex.mappingCone.map
      ((horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1))
      ((horizontalCompleteFiltrationCochainDiagram L).map (D.map' 0 1))
      (η.app (D.obj 0)) (η.app (D.obj 1))
      (η.naturality (D.map' 0 1))
  naturality X Y φ := by
    let η := horizontalCompleteFiltrationCochainDiagramNatTrans f
    dsimp [horizontalCompleteFiltrationMappingConeFunctor]
    rw [← CochainComplex.mappingCone.map_comp,
      ← CochainComplex.mappingCone.map_comp]
    congr 1
    · exact η.naturality (φ.app 0)
    · exact η.naturality (φ.app 1)

@[simp]
theorem horizontalCompleteFiltrationMappingConeNatTrans_app
    (f : K ⟶ L) (D : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationMappingConeNatTrans f).app D =
      CochainComplex.mappingCone.map
        ((horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1))
        ((horizontalCompleteFiltrationCochainDiagram L).map (D.map' 0 1))
        ((horizontalCompleteFiltrationCochainDiagramNatTrans f).app (D.obj 0))
        ((horizontalCompleteFiltrationCochainDiagramNatTrans f).app (D.obj 1))
        ((horizontalCompleteFiltrationCochainDiagramNatTrans f).naturality
          (D.map' 0 1)) :=
  rfl

private noncomputable def functorMappingConeCompTriangleMap
    {F G : EInt ⥤ CochainComplex C ℤ} (η : F ⟶ G)
    {i j k : EInt} (a : i ⟶ j) (b : j ⟶ k) :
    functorMappingConeCompTriangle F a b ⟶
      functorMappingConeCompTriangle G a b :=
  Triangle.homMk _ _
    (CochainComplex.mappingCone.map
      (F.map a) (G.map a) (η.app i) (η.app j) (η.naturality a))
    (CochainComplex.mappingCone.map
      (F.map (a ≫ b)) (G.map (a ≫ b))
      (η.app i) (η.app k) (η.naturality (a ≫ b)))
    (CochainComplex.mappingCone.map
      (F.map b) (G.map b) (η.app j) (η.app k) (η.naturality b))
    (by
      dsimp [functorMappingConeCompTriangle]
      rw [← CochainComplex.mappingCone.map_comp,
        ← CochainComplex.mappingCone.map_comp]
      congr 1
      · simp
      · exact η.naturality b)
    (by
      dsimp [functorMappingConeCompTriangle]
      rw [← CochainComplex.mappingCone.map_comp,
        ← CochainComplex.mappingCone.map_comp]
      congr 1
      · exact η.naturality a
      · simp)
    (by
      have h := CochainComplex.mappingConeCompTriangle_mor₃_naturality
        (F.map a) (F.map b) (G.map a) (G.map b)
          (homMk₂ (η.app i) (η.app j) (η.app k)
            (η.naturality a) (η.naturality b))
      simpa [functorMappingConeCompTriangle] using h.symm)

/-- A bicomplex map induces a morphism between the triangulated spectral
objects of the complete horizontal filtrations. -/
noncomputable def horizontalCompleteFiltrationTriangulatedSpectralObjectMap
    (f : K ⟶ L) :
    horizontalCompleteFiltrationTriangulatedSpectralObject K ⟶
      horizontalCompleteFiltrationTriangulatedSpectralObject L where
  hom := Functor.whiskerRight
    (horizontalCompleteFiltrationMappingConeNatTrans f)
    (HomotopyCategory.quotient C (ComplexShape.up ℤ))
  comm {i j k} a b := by
    let F := horizontalCompleteFiltrationCochainDiagram K
    let G := horizontalCompleteFiltrationCochainDiagram L
    let η := horizontalCompleteFiltrationCochainDiagramNatTrans f
    let τ := functorMappingConeCompTriangleMap η a b
    have h := ((HomotopyCategory.quotient C
      (ComplexShape.up ℤ)).mapTriangle.map τ).comm₃
    simpa [F, G, η, τ,
      CategoryTheory.Triangulated.SpectralObject.δ,
      horizontalCompleteFiltrationTriangulatedSpectralObject,
      horizontalCompleteFiltrationMappingConeNatTrans,
      functorMappingConeCompTriangleMap] using h

@[simp]
theorem horizontalCompleteFiltrationTriangulatedSpectralObjectMap_hom_app
    (f : K ⟶ L) (D : ComposableArrows EInt 1) :
    (horizontalCompleteFiltrationTriangulatedSpectralObjectMap f).hom.app D =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((horizontalCompleteFiltrationMappingConeNatTrans f).app D) :=
  rfl

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A bicomplex map induces a morphism between the abelian spectral objects of
the complete horizontal filtrations. -/
noncomputable def horizontalCompleteFiltrationSpectralObjectMap (f : K ⟶ L) :
    horizontalCompleteFiltrationSpectralObject K ⟶
      horizontalCompleteFiltrationSpectralObject L :=
  (CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctorFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0) EInt).map
      (horizontalCompleteFiltrationTriangulatedSpectralObjectMap f)

end HomologicalComplex₂

end
