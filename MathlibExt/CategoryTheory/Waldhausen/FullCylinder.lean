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

public import MathlibExt.CategoryTheory.Waldhausen.MappingCylinderCore
public import MathlibExt.CategoryTheory.Waldhausen.CylinderNormalization
public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrow
public import MathlibExt.CategoryTheory.Waldhausen.BinaryCoproductCofibration

/-!
# Full mapping cylinders for the original Waldhausen category

The cylinder functor is defined on the actual arrow category with its
original front, back and projection transformations. It retains all four
conditions of Weibel IV.Definition 8.8, including the relative pushout
corner for every pointwise cofibration square. The zero-arrow identity is
expressed by the existing natural normalization isomorphism, whose maps
are the same projection and back inclusion.

The Cylinder Axiom remains a separate condition. A full cylinder supplies
the existing minimal mapping-cylinder core and the literal approximation
cofibration replacement, without asserting the Approximation Theorem.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory Limits

universe u v uD vD

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

section Corner

variable [HasBinaryCoproducts C]

/-- The original combined front and back inclusion of one cylinder arrow. -/
def cylinderBoundaryMap (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T) (f : Arrow C) :
    f.left ⨿ f.right ⟶ T.obj f := coprod.desc (front.app f) (back.app f)

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- The original joint boundary retains its whole front inclusion. -/
theorem cylinderBoundaryMap_inl (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T) (f : Arrow C) :
    coprod.inl ≫ cylinderBoundaryMap T front back f = front.app f := by
  dsimp only [cylinderBoundaryMap]
  exact coprod.inl_desc _ _

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- The original joint boundary retains its whole back inclusion. -/
theorem cylinderBoundaryMap_inr (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T) (f : Arrow C) :
    coprod.inr ≫ cylinderBoundaryMap T front back f = back.app f := by
  dsimp only [cylinderBoundaryMap]
  exact coprod.inr_desc _ _

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- The original combined inclusion is natural in every commutative arrow square. -/
theorem cylinderBoundaryMap_naturality (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    {f g : Arrow C} (α : f ⟶ g) :
    cylinderBoundaryMap T front back f ≫ T.map α =
      coprod.map α.left α.right ≫ cylinderBoundaryMap T front back g := by
  dsimp only [cylinderBoundaryMap]
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, coprod.inl_map_assoc, coprod.inl_desc]
    exact (front.naturality α).symm
  · rw [coprod.inr_desc_assoc, coprod.inr_map_assoc, coprod.inr_desc]
    exact (back.naturality α).symm

/-- The source's relative cylinder corner exists from its original boundary cofibration. -/
theorem cylinderCorner_hasPushout (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    HasPushout (cylinderBoundaryMap T front back f) (coprod.map α.left α.right) := by
  obtain ⟨P, inNew, inOld, hp, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
    (C := C) (cylinderBoundaryMap T front back f) (hBoundary f)
    (g.left ⨿ g.right) (coprod.map α.left α.right)
  exact hp.flip.hasPushout

/-- The actual relative corner map from the boundary pushout to the new cylinder. -/
def cylinderCornerMap (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    letI := cylinderCorner_hasPushout T front back hBoundary α
    pushout (cylinderBoundaryMap T front back f) (coprod.map α.left α.right) ⟶ T.obj g := by
  letI := cylinderCorner_hasPushout T front back hBoundary α
  exact pushout.desc (T.map α) (cylinderBoundaryMap T front back g)
    (cylinderBoundaryMap_naturality T front back α)

/-- The corner's old-cylinder leg is the original functor map. -/
theorem cylinderCornerMap_inl (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    letI := cylinderCorner_hasPushout T front back hBoundary α
    pushout.inl _ _ ≫ cylinderCornerMap T front back hBoundary α = T.map α := by
  let := cylinderCorner_hasPushout T front back hBoundary α
  exact pushout.inl_desc _ _ _

/-- The corner's new-boundary leg is the original front and back inclusion. -/
theorem cylinderCornerMap_inr (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    letI := cylinderCorner_hasPushout T front back hBoundary α
    pushout.inr _ _ ≫ cylinderCornerMap T front back hBoundary α =
      cylinderBoundaryMap T front back g := by
  let := cylinderCorner_hasPushout T front back hBoundary α
  exact pushout.inr_desc _ _ _

end Corner

/-- Source-faithful full mapping-cylinder data, including the actual relative corner.
Binary coproducts are the named values derived from the original Waldhausen
pushouts. The zero-arrow equality is represented by its canonical natural isomorphism. -/
structure FullCylinder (C : Type u) [Category.{v} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C] extends WaldhausenMappingCylinderCore C where
  /-- The original projection and back inclusion normalize the zero-arrow cylinder. -/
  normalization : CylinderNormalization functor back projection
  /-- Both original boundary components jointly form a cofibration. -/
  boundary_cofibration :
    letI := waldhausenHasBinaryCoproducts C
    ∀ f, IsCofibration (cylinderBoundaryMap functor front back f)
  /-- Original pointwise weak equivalences are carried to weak cylinder maps. -/
  map_weakEquivalence : ∀ {f g : Arrow C} (α : f ⟶ g),
    arrowWeakEquivalences C α → IsWeakEquivalence (functor.map α)
  /-- Original pointwise cofibrations are carried to cylinder cofibrations. -/
  map_cofibration : ∀ {f g : Arrow C} (α : f ⟶ g),
    arrowCofibrations C α → IsCofibration (functor.map α)
  /-- The actual relative boundary-pushout corner is a cofibration. -/
  corner_cofibration :
    letI := waldhausenHasBinaryCoproducts C
    ∀ {f g : Arrow C} (α : f ⟶ g), arrowCofibrations C α →
      letI := cylinderCorner_hasPushout functor front back boundary_cofibration α
      IsCofibration (cylinderCornerMap functor front back boundary_cofibration α)

namespace FullCylinder

/-- A full cylinder retains its original minimal core as its canonical parent. -/
instance : Coe (FullCylinder C) (WaldhausenMappingCylinderCore C) where
  coe := FullCylinder.toWaldhausenMappingCylinderCore


variable (T : FullCylinder C)

/-- The Cylinder Axiom asks that every original cylinder projection be weak. -/
@[expose]
def SatisfiesCylinderAxiom : Prop := T.toWaldhausenMappingCylinderCore.SatisfiesCylinderAxiom

/-- The Cylinder Axiom makes every original full-cylinder projection a weak equivalence. -/
theorem projection_isWeakEquivalence (hCyl : T.SatisfiesCylinderAxiom) (f : Arrow C) :
    IsWeakEquivalence (T.projection.app f) := hCyl f

/-- The original front and back maps jointly form the same boundary cofibration. -/
theorem boundary_isCofibration :
    letI := waldhausenHasBinaryCoproducts C
    ∀ f, IsCofibration (cylinderBoundaryMap T.functor T.front T.back f) :=
  T.boundary_cofibration

/-- The back inclusion is a cofibration, derived from its coproduct injection
and the full cylinder's actual joint boundary cofibration. -/
theorem back_isCofibration (f : Arrow C) : IsCofibration (T.back.app f) := by
  let := waldhausenHasBinaryCoproducts C
  have hInr : IsCofibration (coprod.inr : f.right ⟶ f.left ⨿ f.right) := by
    have hp := IsPushout.of_is_coproduct (coprodIsCoprod f.left f.right)
      (isZero_zero C).isInitial
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout hp.flip
      (WaldhausenCategoryWithoutGluing.zero_isCofibration f.left _)
  have hComp := (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem
    (coprod.inr : f.right ⟶ f.left ⨿ f.right)
    (cylinderBoundaryMap T.functor T.front T.back f) hInr (T.boundary_cofibration f)
  simpa only [cylinderBoundaryMap, coprod.inr_desc] using hComp

/-- Zero-arrow normalization keeps the original projection followed by back identity. -/
theorem projection_back_zero (A : C) :
    T.projection.app (zeroArrowFunctor.obj A) ≫ T.back.app (zeroArrowFunctor.obj A) =
      𝟙 (T.functor.obj (zeroArrowFunctor.obj A)) := T.normalization.projection_back A

/-- A cylinder with zero source and target is zero, through its original
zero-arrow normalization and the actual arrow isomorphism. -/
theorem obj_isZero_of_endpoints {f : Arrow C} (hSource : IsZero f.left)
    (hTarget : IsZero f.right) : IsZero (T.functor.obj f) := by
  let e : f ≅ zeroArrowFunctor.obj f.right :=
    Arrow.isoMk hSource.isoZero (Iso.refl f.right)
      (by apply hSource.eq_of_src)
  let eT := (T.functor.mapIso e) ≪≫ (T.normalization.zeroNormalization.app f.right)
  exact IsZero.of_iso hTarget eT

/-- Full source cylinders give the literal approximation cofibration replacement
with the original front map and weak composite projection. -/
theorem cofibrationApproximation {D : Type uD} [Category.{vD} D]
    [HasZeroObject D] [WaldhausenCategoryWithoutGluing D] {F : C ⥤ D}
    (hF : F.IsWaldhausenExact) (hApp : F.WaldhausenApproximationProperty)
    (hCyl : T.SatisfiesCylinderAxiom) :
    ∀ (X : C) (Y : D) (g : F.obj X ⟶ Y),
      ∃ (Xnext : C) (i : X ⟶ Xnext) (p : F.obj Xnext ⟶ Y),
        IsCofibration i ∧ IsWeakEquivalence p ∧ F.map i ≫ p = g :=
  T.toWaldhausenMappingCylinderCore.cofibrationApproximation_of_approximation
    hF hApp hCyl

end FullCylinder
end CategoryTheory.Waldhausen
