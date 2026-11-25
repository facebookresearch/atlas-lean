/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.CokernelCompShortExact

/-!
# Mapping-cone and cokernel-composition connecting morphisms

For composable maps `f : A ⟶ B` and `g : B ⟶ D`, the mapping-cone
composition triangle has objects `cone(f)`, `cone(f ≫ g)`, and `cone(g)`.
The canonical maps from these cones to the corresponding cokernels compare
this triangle with the short exact sequence

`coker(f) ⟶ coker(f ≫ g) ⟶ coker(g)`.

This file constructs that triangle comparison and proves that its endpoint
is the expected mapping-cone-to-cokernel map.  Consequently the connecting
morphism of the mapping-cone composition triangle agrees with the connecting
morphism of the cokernel-composition short exact sequence.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace CochainComplex
namespace mappingCone

section HomEq

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]

/-- Equality of cochain maps induces the corresponding equality isomorphism
of mapping cones. -/
noncomputable def isoOfHomEq
    {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : f = g) :
    mappingCone f ≅ mappingCone g :=
  eqToIso (congrArg (fun z : K ⟶ L => mappingCone z) h)

/-- A map of cones whose target map is replaced by an equal map commutes with
the equality isomorphism on mapping cones. -/
theorem map_comp_isoOfHomEq
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f₁ : K₁ ⟶ L₁) {f₂ f₂' : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : f₂ = f₂')
    (w : f₁ ≫ b = a ≫ f₂) (w' : f₁ ≫ b = a ≫ f₂') :
    map f₁ f₂ a b w ≫ (isoOfHomEq h).hom =
      map f₁ f₂' a b w' := by
  subst h
  simp [isoOfHomEq]

/-- A map of cones whose source map is replaced by an equal map commutes with
the equality isomorphism on mapping cones. -/
theorem isoOfHomEq_hom_comp_map
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    {f₁ f₁' : K₁ ⟶ L₁} (f₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : f₁ = f₁')
    (w : f₁ ≫ b = a ≫ f₂) (w' : f₁' ≫ b = a ≫ f₂) :
    (isoOfHomEq h).hom ≫ map f₁' f₂ a b w' =
      map f₁ f₂ a b w := by
  subst h
  simp [isoOfHomEq]

end HomEq

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B D : CochainComplex C ℤ}
  (f : A ⟶ B) (g : B ⟶ D)

/-- Morphism from the cokernel sequence of `f` to that of `f ≫ g`. -/
noncomputable def cokernelSequenceMapComp :
    ShortComplex.cokernelSequence f ⟶
      ShortComplex.cokernelSequence (f ≫ g) where
  τ₁ := 𝟙 _
  τ₂ := g
  τ₃ := cokernel.map f (f ≫ g) (𝟙 _) g (by simp)
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- Morphism from the cokernel sequence of `f ≫ g` to that of `g`. -/
noncomputable def cokernelSequenceCompMap :
    ShortComplex.cokernelSequence (f ≫ g) ⟶
      ShortComplex.cokernelSequence g where
  τ₁ := f
  τ₂ := 𝟙 _
  τ₃ := cokernel.map (f ≫ g) g f (𝟙 _) (by simp)
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- The first map of the mapping-cone composition triangle commutes with the
canonical maps to cokernels. -/
theorem compTriangle_mor₁_desc :
    (mappingConeCompTriangle f g).mor₁ ≫
        descShortComplex (ShortComplex.cokernelSequence (f ≫ g)) =
      descShortComplex (ShortComplex.cokernelSequence f) ≫
        (CategoryTheory.cokernelCompShortComplex f g).f := by
  exact map_descShortComplex _ _ (cokernelSequenceMapComp f g)

/-- The second map of the mapping-cone composition triangle commutes with the
canonical maps to cokernels. -/
theorem compTriangle_mor₂_desc :
    (mappingConeCompTriangle f g).mor₂ ≫
        descShortComplex (ShortComplex.cokernelSequence g) =
      descShortComplex (ShortComplex.cokernelSequence (f ≫ g)) ≫
        cokernel.map (f ≫ g) g f (𝟙 _) (by simp) := by
  exact map_descShortComplex _ _ (cokernelSequenceCompMap f g)

/-- Map from `cone(g)` to the cone of the first map in the cokernel-composition
short complex. -/
noncomputable def compTriangleToCokernelCone :
    mappingCone g ⟶
      mappingCone (CategoryTheory.cokernelCompShortComplex f g).f :=
  (mappingConeCompHomotopyEquiv f g).hom ≫
    map (mappingConeCompTriangle f g).mor₁
      (CategoryTheory.cokernelCompShortComplex f g).f
      (descShortComplex (ShortComplex.cokernelSequence f))
      (descShortComplex (ShortComplex.cokernelSequence (f ≫ g)))
      (compTriangle_mor₁_desc f g)

/-- Before precomposing by the canonical homotopy equivalence, the induced
map of cones followed by the final cokernel comparison equals the inverse
homotopy equivalence followed by the direct comparison for `g`. -/
theorem compTriangleConeMap_desc :
    map (mappingConeCompTriangle f g).mor₁
          (CategoryTheory.cokernelCompShortComplex f g).f
          (descShortComplex (ShortComplex.cokernelSequence f))
          (descShortComplex (ShortComplex.cokernelSequence (f ≫ g)))
          (compTriangle_mor₁_desc f g) ≫
        descShortComplex (CategoryTheory.cokernelCompShortComplex f g) =
      (mappingConeCompHomotopyEquiv f g).inv ≫
        descShortComplex (ShortComplex.cokernelSequence g) := by
  ext n
  rw [ext_from_iff _ (n + 1) n rfl]
  constructor
  · simp [map, descShortComplex, mappingConeCompHomotopyEquiv,
      MappingConeCompHomotopyEquiv.inv]
    have hz := inl_v_descShortComplex_f
      (S := ShortComplex.cokernelSequence g) (n + 1) n (by omega)
    dsimp [ShortComplex.cokernelSequence, descShortComplex] at hz
    have hzero := congrArg
      (fun z => (snd f).v (n + 1) (n + 1) (add_zero (n + 1)) ≫ z) hz
    simp only [comp_zero] at hzero
    simp [ShortComplex.cokernelSequence] at hzero ⊢
  · simp [map, descShortComplex, mappingConeCompHomotopyEquiv,
      MappingConeCompHomotopyEquiv.inv]
    have h := (HomologicalComplex.congr_hom
      (compTriangle_mor₂_desc f g) n).symm
    dsimp [ShortComplex.cokernelSequence, descShortComplex,
      mappingConeCompTriangle, map] at h
    simpa [ShortComplex.cokernelSequence, Category.id_comp] using h

/-- The third cone comparison followed by the final cokernel comparison is
literally the canonical comparison from `cone(g)` to `coker(g)`. -/
theorem compTriangleToCokernelCone_desc :
    compTriangleToCokernelCone f g ≫
        descShortComplex (CategoryTheory.cokernelCompShortComplex f g) =
      descShortComplex (ShortComplex.cokernelSequence g) := by
  unfold compTriangleToCokernelCone
  simp only [Category.assoc]
  rw [compTriangleConeMap_desc f g]
  simp

/-- The mapping-cone composition triangle is canonically isomorphic to the
standard triangle on its first map in the homotopy category. -/
noncomputable def compTriangleIsoTriangleMor₁ :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (mappingConeCompTriangle f g) ≅
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (triangle (mappingConeCompTriangle f g).mor₁) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (HomotopyCategory.isoOfHomotopyEquiv
      (mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by
        simpa [mappingConeCompTriangleh] using
          mappingConeCompTriangleh_comm₁ f g) ?_
  dsimp [HomotopyCategory.isoOfHomotopyEquiv]
  rw [← Category.assoc, ← Functor.map_comp,
    mappingConeCompHomotopyEquiv_comm₂ f g]
  simp [mappingConeCompTriangle, triangle]

/-- Chain-level triangle morphism induced by the two canonical
mapping-cone-to-cokernel maps. -/
noncomputable def triangleMor₁ToCokernelTriangle :
    triangle (mappingConeCompTriangle f g).mor₁ ⟶
      triangle (CategoryTheory.cokernelCompShortComplex f g).f :=
  triangleMap (mappingConeCompTriangle f g).mor₁
    (CategoryTheory.cokernelCompShortComplex f g).f
    (descShortComplex (ShortComplex.cokernelSequence f))
    (descShortComplex (ShortComplex.cokernelSequence (f ≫ g)))
    (compTriangle_mor₁_desc f g)

/-- Triangle morphism in the homotopy category from the mapping-cone
composition triangle to the triangle on the cokernel-composition map. -/
noncomputable def compTriangleToCokernelTriangle :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (mappingConeCompTriangle f g) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
        (triangle (CategoryTheory.cokernelCompShortComplex f g).f) :=
  (compTriangleIsoTriangleMor₁ f g).hom ≫
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.map
      (triangleMor₁ToCokernelTriangle f g)

/-- The first component of the triangle morphism is the canonical comparison
from `cone(f)` to `coker(f)`. -/
theorem compTriangleToCokernelTriangle_hom₁ :
    (compTriangleToCokernelTriangle f g).hom₁ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (descShortComplex (ShortComplex.cokernelSequence f)) := by
  simp [compTriangleToCokernelTriangle,
    compTriangleIsoTriangleMor₁, triangleMor₁ToCokernelTriangle]

/-- The third component of the triangle morphism is the canonical map
constructed from `cone(g)`. -/
theorem compTriangleToCokernelTriangle_hom₃ :
    (compTriangleToCokernelTriangle f g).hom₃ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (compTriangleToCokernelCone f g) := by
  simp [compTriangleToCokernelTriangle,
    compTriangleIsoTriangleMor₁, triangleMor₁ToCokernelTriangle,
    compTriangleToCokernelCone]

/-- Under the canonical mapping-cone-to-cokernel comparisons, the connecting
morphism of the mapping-cone composition triangle is the connecting morphism
of the cokernel-composition short exact sequence. -/
theorem homologySequenceδ_cokernelComp [Mono g]
    (n n' : ℤ) (h : n + 1 = n') :
    ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
          (mappingConeCompTriangle f g)) n n' h) ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n').hom.app (mappingCone f) ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence f)) n' =
    (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n).hom.app (mappingCone g) ≫
      HomologicalComplex.homologyMap
        (descShortComplex (ShortComplex.cokernelSequence g)) n ≫
      (CategoryTheory.cokernelCompShortComplex_shortExact f g).δ n n' h := by
  let φ := compTriangleToCokernelTriangle f g
  let hT := CategoryTheory.cokernelCompShortComplex_shortExact f g
  have hnat := (HomotopyCategory.homologyFunctor C
    (ComplexShape.up ℤ) 0).homologySequenceδ_naturality φ n n' h
  change (HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) n).map φ.hom₃ ≫
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).homologySequenceδ _ n n' h =
      (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) 0).homologySequenceδ _ n n' h ≫
        (HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) n').map φ.hom₁ at hnat
  rw [compTriangleToCokernelTriangle_hom₁ f g,
    compTriangleToCokernelTriangle_hom₃ f g] at hnat
  change (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (compTriangleToCokernelCone f g)) ≫
      (HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
          (triangle (CategoryTheory.cokernelCompShortComplex f g).f))
        n n' h = _ at hnat
  rw [CochainComplex.mappingCone.homologySequenceδ_triangleh hT] at hnat
  have hnat' := congrArg (fun z => z ≫
    (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) n').hom.app
        (CategoryTheory.cokernelCompShortComplex f g).X₁) hnat
  simp only [Category.assoc] at hnat'
  rw [Iso.inv_hom_id_app] at hnat'
  have hthird := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n).hom.naturality
      (compTriangleToCokernelCone f g)
  change (HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (compTriangleToCokernelCone f g)) ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n).hom.app
          (mappingCone (CategoryTheory.cokernelCompShortComplex f g).f) = _
    at hthird
  rw [reassoc_of% hthird] at hnat'
  have hf := (HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up ℤ) n').hom.naturality
      (descShortComplex (ShortComplex.cokernelSequence f))
  change (HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) n').map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (descShortComplex (ShortComplex.cokernelSequence f))) ≫
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) n').hom.app
          (CategoryTheory.cokernelCompShortComplex f g).X₁ = _ at hf
  rw [hf] at hnat'
  have hcomp := HomologicalComplex.homologyMap_comp
    (compTriangleToCokernelCone f g)
    (descShortComplex (CategoryTheory.cokernelCompShortComplex f g)) n
  change HomologicalComplex.homologyMap
      (compTriangleToCokernelCone f g ≫
        descShortComplex (CategoryTheory.cokernelCompShortComplex f g)) n =
    (HomologicalComplex.homologyFunctor C
      (ComplexShape.up ℤ) n).map (compTriangleToCokernelCone f g) ≫
      HomologicalComplex.homologyMap
        (descShortComplex (CategoryTheory.cokernelCompShortComplex f g)) n
    at hcomp
  rw [← reassoc_of% hcomp] at hnat'
  rw [compTriangleToCokernelCone_desc f g] at hnat'
  have hid : hT.δ n n' h ≫
      𝟙 ((HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) n').obj
          (CategoryTheory.cokernelCompShortComplex f g).X₁) =
      hT.δ n n' h := Category.comp_id _
  rw [hid] at hnat'
  simpa [Category.assoc, ShortComplex.cokernelSequence] using hnat'.symm

end mappingCone
end CochainComplex

end
