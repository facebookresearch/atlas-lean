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

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded
public import MathlibExt.Algebra.Homology.HomologicalComplexBiprodMaps
public import MathlibExt.Algebra.Homology.FiniteSupportConeAugmentation
public import MathlibExt.Algebra.Homology.MappingCylinderQuasiIso
public import MathlibExt.CategoryTheory.Waldhausen.MappingCylinderCore

/-!
# Mapping cylinders of bounded cochain complexes

The signed cofiber and endpoint biproduct charts give a bounded mapping
cylinder. Its support window is determined by the bounded endpoints.
The endpoint inclusions admit degreewise retractions. Projection composes
with the source inclusion to give the map and with the target inclusion
to give the identity.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uC vC

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

/-- Every integer degree has a predecessor. -/
theorem mappingCylinderPredecessors : ∀ j : ℤ, ∃ i : ℤ, (ComplexShape.up ℤ).Rel i j :=
  fun j => ⟨j - 1, by change (j - 1) + 1 = j; omega⟩

variable (C : Type uC) [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Support window of a cylinder obtained from its signed cofiber and endpoint biproduct. -/
theorem mappingCylinder_isZero_outside {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (a b c e : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hL : ∀ j : ℤ, j < c ∨ e < j → IsZero (L.X j))
    (j : ℤ) (hj : j < min (a - 1) (min a c) ∨ max (b - 1) (max b e) < j) :
    IsZero ((HomologicalComplex.mappingCylinder f).X j) :=
  CochainComplex.mappingCone.isZero_outside_of_finiteSupport
    (HomologicalComplex.mappingCylinder.arrow f) a b (min a c) (max b e) hK
    (CochainComplex.biprod_isZero_outside C K L a b c e hK hL) j hj

/-- Mapping cylinders of bounded cochain maps are bounded. -/
theorem mappingCylinder_bounded {K L : Bounded C} (f : K ⟶ L) :
    CochainComplex.bounded C (HomologicalComplex.mappingCylinder f.hom) := by
  obtain ⟨a, b, hK⟩ := K.property
  obtain ⟨c, e, hL⟩ := L.property
  exact ⟨min (a - 1) (min a c), max (b - 1) (max b e),
    mappingCylinder_isZero_outside C f.hom a b c e hK hL⟩

/-- Mapping-cylinder functor on bounded cochain maps. -/
def mappingCylinderFunctor : Arrow (Bounded C) ⥤ Bounded C :=
  ObjectProperty.lift (CochainComplex.bounded C)
    ((ι C).mapArrow ⋙ HomologicalComplex.mappingCylinder.functor mappingCylinderPredecessors)
    (fun f => mappingCylinder_bounded C f.hom)

/-- Underlying complex of a bounded mapping cylinder. -/
theorem mappingCylinderFunctor_obj_obj (f : Arrow (Bounded C)) :
    ((mappingCylinderFunctor C).obj f).obj = HomologicalComplex.mappingCylinder f.hom.hom := rfl

/-- Underlying cylinder map induced by a commutative square. -/
theorem mappingCylinderFunctor_map_hom {f g : Arrow (Bounded C)} (a : f ⟶ g) :
    ((mappingCylinderFunctor C).map a).hom =
      HomologicalComplex.mappingCylinder.map f.hom.hom g.hom.hom mappingCylinderPredecessors
        ((ι C).mapArrow.map a) := rfl

/-- Component chart through the cofiber and endpoint biproducts. -/
def mappingCylinderTermIso (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ≅
      f.left.obj.X (j + 1) ⊞ (f.left.obj.X j ⊞ f.right.obj.X j) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j (j + 1) rfl ≪≫
      biprod.mapIso (Iso.refl _) (HomologicalComplex.biprodXIso f.left.obj f.right.obj j)

/-- Source endpoint inclusion as a natural transformation. -/
def mappingCylinderFront : (Arrow.leftFunc : Arrow (Bounded C) ⥤ Bounded C) ⟶
    mappingCylinderFunctor C where
  app f := ObjectProperty.homMk
    ((HomologicalComplex.mappingCylinder.sourceNatTrans mappingCylinderPredecessors).app
      ((ι C).mapArrow.obj f))
  naturality {f g} a := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.mappingCylinder.sourceNatTrans mappingCylinderPredecessors).naturality
      ((ι C).mapArrow.map a)

/-- Target endpoint inclusion as a natural transformation. -/
def mappingCylinderBack : (Arrow.rightFunc : Arrow (Bounded C) ⥤ Bounded C) ⟶
    mappingCylinderFunctor C where
  app f := ObjectProperty.homMk
    ((HomologicalComplex.mappingCylinder.targetNatTrans mappingCylinderPredecessors).app
      ((ι C).mapArrow.obj f))
  naturality {f g} a := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.mappingCylinder.targetNatTrans mappingCylinderPredecessors).naturality
      ((ι C).mapArrow.map a)

/-- Cylinder projection as a natural transformation. -/
def mappingCylinderProjection : mappingCylinderFunctor C ⟶
    (Arrow.rightFunc : Arrow (Bounded C) ⥤ Bounded C) where
  app f := ObjectProperty.homMk
    ((HomologicalComplex.mappingCylinder.projectionNatTrans mappingCylinderPredecessors).app
      ((ι C).mapArrow.obj f))
  naturality {f g} a := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.mappingCylinder.projectionNatTrans mappingCylinderPredecessors).naturality
      ((ι C).mapArrow.map a)

/-- Underlying source endpoint inclusion. -/
theorem mappingCylinderFront_app_hom (f : Arrow (Bounded C)) :
    ((mappingCylinderFront C).app f).hom = HomologicalComplex.mappingCylinder.source f.hom.hom := rfl

/-- Underlying target endpoint inclusion. -/
theorem mappingCylinderBack_app_hom (f : Arrow (Bounded C)) :
    ((mappingCylinderBack C).app f).hom = HomologicalComplex.mappingCylinder.target f.hom.hom := rfl

/-- Underlying cylinder projection. -/
theorem mappingCylinderProjection_app_hom (f : Arrow (Bounded C)) :
    ((mappingCylinderProjection C).app f).hom = HomologicalComplex.mappingCylinder.projection f.hom.hom := rfl

/-- The source inclusion followed by projection is the arrow natural transformation. -/
theorem mappingCylinderFront_projection :
    mappingCylinderFront C ≫ mappingCylinderProjection C = Arrow.leftToRight := by
  apply NatTrans.ext
  funext f
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.source_projection f.hom.hom

/-- The target inclusion followed by projection is the target identity. -/
theorem mappingCylinderBack_projection :
    mappingCylinderBack C ≫ mappingCylinderProjection C =
      (𝟙 _ : (Arrow.rightFunc : Arrow (Bounded C) ⥤ Bounded C) ⟶ Arrow.rightFunc) := by
  apply NatTrans.ext
  funext f
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.target_projection f.hom.hom

/-- A degreewise retraction of the source endpoint inclusion. -/
def mappingCylinderFrontRetraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ⟶ f.left.obj.X j :=
  HomologicalComplex.homotopyCofiber.sndX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
    (biprod.fst : f.left.obj ⊞ f.right.obj ⟶ f.left.obj).f j

/-- A degreewise retraction of the target endpoint inclusion. -/
def mappingCylinderBackRetraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ⟶ f.right.obj.X j :=
  HomologicalComplex.homotopyCofiber.sndX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
    (biprod.snd : f.left.obj ⊞ f.right.obj ⟶ f.right.obj).f j

/-- The source endpoint component followed by its retraction is the identity. -/
theorem mappingCylinderFront_f_retraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFront C).app f).hom.f j ≫ mappingCylinderFrontRetraction C f j =
      𝟙 (f.left.obj.X j) := by
  change ((biprod.inl : f.left.obj ⟶ f.left.obj ⊞ f.right.obj).f j ≫
    HomologicalComplex.homotopyCofiber.inrX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j) ≫
      (HomologicalComplex.homotopyCofiber.sndX
        (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
          (biprod.fst : f.left.obj ⊞ f.right.obj ⟶ f.left.obj).f j) = _
  simp only [Category.assoc, HomologicalComplex.homotopyCofiber.inrX_sndX_assoc,
    HomologicalComplex.biprod_inl_fst_f]

/-- The target endpoint component followed by its retraction is the identity. -/
theorem mappingCylinderBack_f_retraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderBack C).app f).hom.f j ≫ mappingCylinderBackRetraction C f j =
      𝟙 (f.right.obj.X j) := by
  change ((biprod.inr : f.right.obj ⟶ f.left.obj ⊞ f.right.obj).f j ≫
    HomologicalComplex.homotopyCofiber.inrX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j) ≫
      (HomologicalComplex.homotopyCofiber.sndX
        (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
          (biprod.snd : f.left.obj ⊞ f.right.obj ⟶ f.right.obj).f j) = _
  simp only [Category.assoc, HomologicalComplex.homotopyCofiber.inrX_sndX_assoc,
    HomologicalComplex.biprod_inr_snd_f]

/-- Both endpoint inclusions are split monomorphisms in each degree. -/
theorem mappingCylinder_endpoints_split (f : Arrow (Bounded C)) :
    degreewiseSplitMonomorphisms C ((mappingCylinderFront C).app f) ∧
      degreewiseSplitMonomorphisms C ((mappingCylinderBack C).app f) := by
  exact ⟨fun j => IsSplitMono.mk' ⟨mappingCylinderFrontRetraction C f j,
    mappingCylinderFront_f_retraction C f j⟩,
    fun j => IsSplitMono.mk' ⟨mappingCylinderBackRetraction C f j,
      mappingCylinderBack_f_retraction C f j⟩⟩

end CochainComplex.Bounded

end
