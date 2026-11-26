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
# Mapping cylinders with zero source

Let C be a preadditive category with binary biproducts. If the source F of
an integer-indexed cochain map f:F → G is a zero object, then Cyl(f), the homotopy
cofiber of (1,−f):F → F ⊞ G, is canonically isomorphic to G.
The forward map is the cylinder projection and the inverse is the target
endpoint inclusion. The same comparison holds in the bounded category.

When C also has a zero object, these comparisons form a natural isomorphism
Cyl(0 → K) ≅ K on bounded cochain complexes. It normalizes the cylinder
of the zero-source arrow with exactly the projection and target inclusion
as its two maps.
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

/-- Let C be preadditive with binary biproducts and f:F → G a map of
integer-indexed cochain complexes. If F is a zero object in the cochain
category, the canonical isomorphism Cyl(f) ≅ G. Its forward map is the
cylinder projection and its inverse is the target inclusion. -/
def zeroSourceIso (f : F ⟶ G) (hF : IsZero F) : mappingCylinder f ≅ G :=
  (isoZeroBiprod hF ≪≫ (HomologicalComplex.homotopyCofiber.zeroSourceIso (arrow f) hF).symm).symm

/-- For a cochain map f:F → G in a preadditive category C with binary
biproducts, if F is a zero object, the inverse of the canonical isomorphism
Cyl(f) ≅ G is the target endpoint inclusion G → Cyl(f). -/
theorem zeroSourceIso_inv (f : F ⟶ G) (hF : IsZero F) :
    (zeroSourceIso f hF).inv = target f := rfl

/-- For a cochain map f:F → G in a preadditive category C with binary
biproducts, if F is a zero object, the forward map of the canonical
isomorphism Cyl(f) ≅ G is the cylinder projection Cyl(f) → G. -/
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

/-- Let C be preadditive with binary biproducts and f:F → G a bounded
integer-indexed cochain map. If F is a zero object in the bounded category,
the canonical bounded isomorphism Cyl(f) ≅ G, with projection as forward
map and target endpoint inclusion as inverse. -/
def mappingCylinderZeroSourceIso (f : Arrow (Bounded C)) (hF : IsZero f.left) :
    (mappingCylinderFunctor C).obj f ≅ f.right :=
  (CochainComplex.bounded C).isoMk
    (HomologicalComplex.mappingCylinder.zeroSourceIso f.hom.hom ((ι C).map_isZero hF))

/-- For a bounded cochain map f:F → G in a preadditive category C with
binary biproducts and zero source F, the forward map of the canonical
bounded comparison Cyl(f) ≅ G equals the component at f of the natural
mapping-cylinder projection. -/
theorem mappingCylinderZeroSourceIso_hom (f : Arrow (Bounded C)) (hF : IsZero f.left) :
    (mappingCylinderZeroSourceIso C f hF).hom = (mappingCylinderProjection C).app f := by
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.zeroSourceIso_hom f.hom.hom ((ι C).map_isZero hF)

/-- For a bounded cochain map f:F → G in a preadditive category C with
binary biproducts and zero source F, the inverse of the canonical bounded
comparison Cyl(f) ≅ G equals the component at f of the natural target
endpoint inclusion. -/
theorem mappingCylinderZeroSourceIso_inv (f : Arrow (Bounded C)) (hF : IsZero f.left) :
    (mappingCylinderZeroSourceIso C f hF).inv = (mappingCylinderBack C).app f := by
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.zeroSourceIso_inv f.hom.hom ((ι C).map_isZero hF)

variable [HasZeroObject C]

/-- For a preadditive category C with a zero object and binary biproducts,
the natural isomorphism on bounded integer-indexed cochain complexes
Cyl(0 → K) ≅ K. Its components are the zero-source cylinder comparisons. -/
def mappingCylinderZeroNatIso :
    Waldhausen.zeroArrowFunctor ⋙ mappingCylinderFunctor C ≅ 𝟭 (Bounded C) :=
  NatIso.ofComponents
    (fun K => mappingCylinderZeroSourceIso C (Waldhausen.zeroArrowFunctor.obj K)
      (Waldhausen.zeroArrowFunctor_source_isZero (C := Bounded C) K))
    (fun {K L} f => by
      rw [mappingCylinderZeroSourceIso_hom, mappingCylinderZeroSourceIso_hom]
      exact (mappingCylinderProjection C).naturality (Waldhausen.zeroArrowFunctor.map f))

/-- In a preadditive category C with a zero object and binary biproducts,
the forward natural transformation of Cyl(0 → K) ≅ K is the cylinder
projection, restricted along the functor sending K to its arrow 0 → K. -/
theorem mappingCylinderZeroNatIso_hom :
    (mappingCylinderZeroNatIso C).hom =
      Functor.whiskerLeft Waldhausen.zeroArrowFunctor (mappingCylinderProjection C) := by
  apply NatTrans.ext
  funext K
  exact mappingCylinderZeroSourceIso_hom C (Waldhausen.zeroArrowFunctor.obj K)
    (Waldhausen.zeroArrowFunctor_source_isZero (C := Bounded C) K)

/-- In a preadditive category C with a zero object and binary biproducts,
the inverse natural transformation of Cyl(0 → K) ≅ K is the target
endpoint inclusion, restricted along the functor sending K to 0 → K. -/
theorem mappingCylinderZeroNatIso_inv :
    (mappingCylinderZeroNatIso C).inv =
      Functor.whiskerLeft Waldhausen.zeroArrowFunctor (mappingCylinderBack C) := by
  apply NatTrans.ext
  funext K
  exact mappingCylinderZeroSourceIso_inv C (Waldhausen.zeroArrowFunctor.obj K)
    (Waldhausen.zeroArrowFunctor_source_isZero (C := Bounded C) K)

/-- For a preadditive category C with a zero object and binary biproducts,
the normalization of the bounded mapping-cylinder functor given by the
natural isomorphism Cyl(0 → K) ≅ K. Its forward and inverse maps are
respectively the cylinder projection and the target endpoint inclusion. -/
def mappingCylinderNormalization :
    Waldhausen.CylinderNormalization (mappingCylinderFunctor C)
      (mappingCylinderBack C) (mappingCylinderProjection C) where
  zeroNormalization := mappingCylinderZeroNatIso C
  zeroNormalization_hom := mappingCylinderZeroNatIso_hom C
  zeroNormalization_inv := mappingCylinderZeroNatIso_inv C

end CochainComplex.Bounded

end
