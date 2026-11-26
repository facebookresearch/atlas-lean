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
# Full mapping-cylinder data and boundary cofibrations

Let C have a zero object and a WaldhausenCategoryWithoutGluing structure. A mapping-cylinder
functor T : Arrow C ⥤ C has natural maps j_f : f.left → T(f), k_f : f.right → T(f) and p_f :
T(f) → f.right, with j_f ≫ p_f = f.hom and k_f ≫ p_f = id. The front maps j_f are
cofibrations. The binary coproducts used below are obtained from cofibration pushouts.

Full cylinder data also identify T(0 → A) with A by p and k, require the joint boundary b_f =
desc(j_f,k_f) to be a cofibration, and carry pointwise weak equivalences and cofibrations of
arrows to the corresponding cylinder maps. For a pointwise cofibration square α : f → g, the
induced corner T(f) ⨿_{f.left⨿f.right} (g.left⨿g.right) → T(g) is required to be a
cofibration.

The Cylinder Axiom is the separate condition that every p_f is a weak equivalence. Together
with an exact functor satisfying the approximation property, it gives cofibration-valued
factorizations of maps from its image. The source and target category worlds remain
independent.
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

/-- Joint front and back boundary of a cylinder arrow.

For T : Arrow C ⥤ C with natural front and back maps and binary coproducts in C, define b_f :
f.left ⨿ f.right → T(f) as coprod.desc(front_f,back_f). Its two restrictions are the given
front and back inclusions. -/
def cylinderBoundaryMap (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T) (f : Arrow C) :
    f.left ⨿ f.right ⟶ T.obj f := coprod.desc (front.app f) (back.app f)

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- Front restriction of the joint cylinder boundary.

For the joint boundary b_f = desc(front_f,back_f), the coproduct injection from f.left
satisfies coprod.inl ≫ b_f = front_f. The statement requires binary coproducts in the
category. -/
theorem cylinderBoundaryMap_inl (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T) (f : Arrow C) :
    coprod.inl ≫ cylinderBoundaryMap T front back f = front.app f := by
  dsimp only [cylinderBoundaryMap]
  exact coprod.inl_desc _ _

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- Back restriction of the joint cylinder boundary.

For the joint boundary b_f = desc(front_f,back_f), the coproduct injection from f.right
satisfies coprod.inr ≫ b_f = back_f. The statement requires binary coproducts in the category. -/
theorem cylinderBoundaryMap_inr (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T) (f : Arrow C) :
    coprod.inr ≫ cylinderBoundaryMap T front back f = back.app f := by
  dsimp only [cylinderBoundaryMap]
  exact coprod.inr_desc _ _

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
/-- Naturality of the joint cylinder boundary.

For any commuting arrow square α : f → g and natural front and back maps of T, b_f ≫ T(α) =
coprod.map(α.left,α.right) ≫ b_g. Here b is the descendant of the two boundary maps and the
category has binary coproducts. -/
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

/-- Existence of the relative cylinder-boundary pushout.

Let C have a zero object, binary coproducts and a WaldhausenCategoryWithoutGluing structure.
If every joint boundary b_f of T is a cofibration, its pushout along
coprod.map(α.left,α.right) exists for any arrow square α : f → g. This uses the pushout axiom
for cofibrations. -/
theorem cylinderCorner_hasPushout (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    HasPushout (cylinderBoundaryMap T front back f) (coprod.map α.left α.right) := by
  obtain ⟨P, inNew, inOld, hp, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
    (C := C) (cylinderBoundaryMap T front back f) (hBoundary f)
    (g.left ⨿ g.right) (coprod.map α.left α.right)
  exact hp.flip.hasPushout

/-- Relative corner map of a cylinder square.

With every joint boundary b_f a cofibration, form P = T(f) ⨿_{f.left⨿f.right} (g.left⨿g.right)
for an arrow square α : f → g. Naturality of the boundary gives a descendant P → T(g), whose
old-cylinder leg is T(α) and whose new-boundary leg is b_g. -/
def cylinderCornerMap (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    letI := cylinderCorner_hasPushout T front back hBoundary α
    pushout (cylinderBoundaryMap T front back f) (coprod.map α.left α.right) ⟶ T.obj g := by
  letI := cylinderCorner_hasPushout T front back hBoundary α
  exact pushout.desc (T.map α) (cylinderBoundaryMap T front back g)
    (cylinderBoundaryMap_naturality T front back α)

/-- Old-cylinder leg of the relative corner.

For the relative corner c_α : P → T(g), where P is the boundary pushout for α : f → g, the
pushout leg from T(f) satisfies pushout.inl ≫ c_α = T(α). The boundary maps are assumed
cofibrations. -/
theorem cylinderCornerMap_inl (T : Arrow C ⥤ C)
    (front : Arrow.leftFunc ⟶ T) (back : Arrow.rightFunc ⟶ T)
    (hBoundary : ∀ f, IsCofibration (cylinderBoundaryMap T front back f))
    {f g : Arrow C} (α : f ⟶ g) :
    letI := cylinderCorner_hasPushout T front back hBoundary α
    pushout.inl _ _ ≫ cylinderCornerMap T front back hBoundary α = T.map α := by
  let := cylinderCorner_hasPushout T front back hBoundary α
  exact pushout.inl_desc _ _ _

/-- New-boundary leg of the relative corner.

For the relative corner c_α : P → T(g) of a boundary pushout, the leg from g.left ⨿ g.right
satisfies pushout.inr ≫ c_α = b_g, the joint front and back boundary of the new cylinder. -/
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

/-- Full cylinder structure over cofibrations and weak equivalences.

For C with zero object and WaldhausenCategoryWithoutGluing, extend the mapping-cylinder core
by zero-arrow normalization, joint boundary cofibrations, preservation of pointwise weak
equivalences and cofibrations, and cofibrations of relative boundary-pushout corners. The core
retains the functor T and maps j,k,p with j_f ≫ p_f = f.hom and k_f ≫ p_f = id. The Cylinder
Axiom remains a separate predicate on these data. -/
structure FullCylinder (C : Type u) [Category.{v} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C] extends WaldhausenMappingCylinderCore C where
  /-- Zero-arrow normalization of a full cylinder.

For every A : C, the projection p_{0→A} and back inclusion k_{0→A} identify T(0 → A) with A,
naturally in A. This field supplies CylinderNormalization for the cylinder functor, back map
and projection. -/
  normalization : CylinderNormalization functor back projection
  /-- Joint boundary cofibration of each cylinder.

Using the binary coproducts derived from the WaldhausenCategoryWithoutGluing structure,
require b_f = desc(j_f,k_f) : f.left ⨿ f.right → T(f) to be a cofibration for every arrow f. -/
  boundary_cofibration :
    letI := waldhausenHasBinaryCoproducts C
    ∀ f, IsCofibration (cylinderBoundaryMap functor front back f)
  /-- Cylinder maps of pointwise weak-equivalence squares.

For an arrow square α : f → g whose source and target components are weak equivalences, the
full cylinder requires T(α) : T(f) → T(g) to be a weak equivalence. -/
  map_weakEquivalence : ∀ {f g : Arrow C} (α : f ⟶ g),
    arrowWeakEquivalences C α → IsWeakEquivalence (functor.map α)
  /-- Cylinder maps of pointwise cofibration squares.

For an arrow square α : f → g whose two components are cofibrations, the full cylinder
requires T(α) : T(f) → T(g) to be a cofibration. -/
  map_cofibration : ∀ {f g : Arrow C} (α : f ⟶ g),
    arrowCofibrations C α → IsCofibration (functor.map α)
  /-- Cofibration of a relative cylinder-boundary corner.

For each pointwise cofibration square α : f → g, require the corner T(f) ⨿_{f.left⨿f.right}
(g.left⨿g.right) → T(g) induced by T(α) and b_g to be a cofibration. Existence of its pushout
follows from the joint boundary cofibration. -/
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

/-- Cylinder Axiom for full mapping-cylinder data.

For a full cylinder T, SatisfiesCylinderAxiom means that every projection p_f : T(f) → f.right
is a weak equivalence. This condition is imposed separately from the fields defining
FullCylinder. -/
@[expose]
def SatisfiesCylinderAxiom : Prop := T.toWaldhausenMappingCylinderCore.SatisfiesCylinderAxiom

/-- Weak equivalence of a full-cylinder projection.

If a full cylinder T satisfies the Cylinder Axiom, its projection p_f : T(f) → f.right is a
weak equivalence for every arrow f. -/
theorem projection_isWeakEquivalence (hCyl : T.SatisfiesCylinderAxiom) (f : Arrow C) :
    IsWeakEquivalence (T.projection.app f) := hCyl f

/-- Boundary cofibration supplied by a full cylinder.

For a full cylinder T, the combined map desc(j_f,k_f) : f.left ⨿ f.right → T(f) is a
cofibration for every f, using the binary coproducts derived from the category's cofibration
pushouts. -/
theorem boundary_isCofibration :
    letI := waldhausenHasBinaryCoproducts C
    ∀ f, IsCofibration (cylinderBoundaryMap T.functor T.front T.back f) :=
  T.boundary_cofibration

/-- Back cofibration derived from the joint cylinder boundary.

For a full cylinder T, the back inclusion k_f : f.right → T(f) is a cofibration. It is the
composite of the right coproduct injection with the joint boundary b_f, and both are
cofibrations in the WaldhausenCategoryWithoutGluing structure. -/
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

/-- Inverse normalization equation on zero-source arrows.

For a full cylinder T and A : C, the projection followed by the back inclusion on 0 → A
satisfies p_{0→A} ≫ k_{0→A} = id_{T(0→A)}. The opposite composition is the core
back-projection identity on A. -/
theorem projection_back_zero (A : C) :
    T.projection.app (zeroArrowFunctor.obj A) ≫ T.back.app (zeroArrowFunctor.obj A) =
      𝟙 (T.functor.obj (zeroArrowFunctor.obj A)) := T.normalization.projection_back A

/-- Zero cylinder object for an arrow between zero objects.

If both endpoints of f are zero objects, a full cylinder T has IsZero(T(f)). Identify f with 0
→ f.right and apply the natural zero-arrow normalization T(0 → f.right) ≅ f.right. -/
theorem obj_isZero_of_endpoints {f : Arrow C} (hSource : IsZero f.left)
    (hTarget : IsZero f.right) : IsZero (T.functor.obj f) := by
  let e : f ≅ zeroArrowFunctor.obj f.right :=
    Arrow.isoMk hSource.isoZero (Iso.refl f.right)
      (by apply hSource.eq_of_src)
  let eT := (T.functor.mapIso e) ≪≫ (T.normalization.zeroNormalization.app f.right)
  exact IsZero.of_iso hTarget eT

/-- Cofibration-valued factorization using a full cylinder.

Let F : C ⥤ D be exact for WaldhausenCategoryWithoutGluing structures and satisfy the
approximation property. If C has a full cylinder satisfying the Cylinder Axiom, then every g :
F(X) → Y factors as F(i) ≫ p, where i : X → Xnext is a cofibration and p : F(Xnext) → Y is a
weak equivalence. The cylinder front replaces the source map from the approximation
factorization, and the cylinder projection contributes to the new weak map. -/
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
