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

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedMappingCylinderCore
public import MathlibExt.CategoryTheory.Waldhausen.CylinderNormalization

/-!
# Mapping cylinders of zero-source maps

The cylinder of the zero-source map to a bounded complex is canonically
isomorphic to that complex. Its forward map is the cylinder projection
and its inverse is the target endpoint inclusion. These isomorphisms are
natural in the target complex.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uC vC

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace HomologicalComplex.mappingCylinder

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
variable {F G : CochainComplex C ℤ}

/-- Inverse formula for the zero-source mapping-cylinder isomorphism. -/
def zeroSourceIso (f : F ⟶ G) (hF : IsZero F) : mappingCylinder f ≅ G :=
  (isoZeroBiprod hF ≪≫ (HomologicalComplex.homotopyCofiber.zeroSourceIso (arrow f) hF).symm).symm

/-- The inverse is the target endpoint inclusion. -/
theorem zeroSourceIso_inv (f : F ⟶ G) (hF : IsZero F) :
    (zeroSourceIso f hF).inv = target f := rfl

/-- Projection formula for the zero-source cylinder comparison. -/
theorem zeroSourceIso_hom (f : F ⟶ G) (hF : IsZero F) :
    (zeroSourceIso f hF).hom = projection f := by
  let e := zeroSourceIso f hF
  apply (cancel_epi e.inv).1
  calc
    e.inv ≫ e.hom = 𝟙 G := e.inv_hom_id
    _ = e.inv ≫ projection f := by
      change (𝟙 G) = target f ≫ projection f
      exact (target_projection f).symm

end HomologicalComplex.mappingCylinder

namespace CochainComplex.Bounded

variable (C : Type uC) [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Zero-source cylinder isomorphism in the bounded category. -/
def mappingCylinderZeroSourceIso (f : Arrow (Bounded C)) (hF : IsZero f.left) :
    (mappingCylinderFunctor C).obj f ≅ f.right :=
  (CochainComplex.bounded C).isoMk
    (HomologicalComplex.mappingCylinder.zeroSourceIso f.hom.hom ((ι C).map_isZero hF))

/-- The forward map is the bounded cylinder projection. -/
theorem mappingCylinderZeroSourceIso_hom (f : Arrow (Bounded C)) (hF : IsZero f.left) :
    (mappingCylinderZeroSourceIso C f hF).hom = (mappingCylinderProjection C).app f := by
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.zeroSourceIso_hom f.hom.hom ((ι C).map_isZero hF)

/-- The inverse is the bounded target endpoint inclusion. -/
theorem mappingCylinderZeroSourceIso_inv (f : Arrow (Bounded C)) (hF : IsZero f.left) :
    (mappingCylinderZeroSourceIso C f hF).inv = (mappingCylinderBack C).app f := by
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.zeroSourceIso_inv f.hom.hom ((ι C).map_isZero hF)

variable [HasZeroObject C]

/-- Naturality of the zero-source cylinder isomorphism on bounded complexes. -/
def mappingCylinderZeroNatIso :
    Waldhausen.zeroArrowFunctor ⋙ mappingCylinderFunctor C ≅ 𝟭 (Bounded C) :=
  NatIso.ofComponents
    (fun K => mappingCylinderZeroSourceIso C (Waldhausen.zeroArrowFunctor.obj K)
      (Waldhausen.zeroArrowFunctor_source_isZero (C := Bounded C) K))
    (fun {K L} f => by
      rw [mappingCylinderZeroSourceIso_hom, mappingCylinderZeroSourceIso_hom]
      exact (mappingCylinderProjection C).naturality (Waldhausen.zeroArrowFunctor.map f))

/-- The forward natural transformation is the whiskered cylinder projection. -/
theorem mappingCylinderZeroNatIso_hom :
    (mappingCylinderZeroNatIso C).hom =
      Functor.whiskerLeft Waldhausen.zeroArrowFunctor (mappingCylinderProjection C) := by
  apply NatTrans.ext
  funext K
  exact mappingCylinderZeroSourceIso_hom C (Waldhausen.zeroArrowFunctor.obj K)
    (Waldhausen.zeroArrowFunctor_source_isZero (C := Bounded C) K)

/-- The inverse natural transformation is the whiskered target inclusion. -/
theorem mappingCylinderZeroNatIso_inv :
    (mappingCylinderZeroNatIso C).inv =
      Functor.whiskerLeft Waldhausen.zeroArrowFunctor (mappingCylinderBack C) := by
  apply NatTrans.ext
  funext K
  exact mappingCylinderZeroSourceIso_inv C (Waldhausen.zeroArrowFunctor.obj K)
    (Waldhausen.zeroArrowFunctor_source_isZero (C := Bounded C) K)

/-- Natural normalization of the zero-source bounded cylinder. -/
def mappingCylinderNormalization :
    Waldhausen.CylinderNormalization (mappingCylinderFunctor C)
      (mappingCylinderBack C) (mappingCylinderProjection C) where
  zeroNormalization := mappingCylinderZeroNatIso C
  zeroNormalization_hom := mappingCylinderZeroNatIso_hom C
  zeroNormalization_inv := mappingCylinderZeroNatIso_inv C

end CochainComplex.Bounded

end
