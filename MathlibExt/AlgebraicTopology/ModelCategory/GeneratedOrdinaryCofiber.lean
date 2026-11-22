/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryCone
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppeRotation

/-!
# Original generated cofibers and their replacement maps

The chosen Puppe cofiber uses the cone supplied by the original I factor
factory. Cofibrant pushout gluing proves its weak invariance at the actual
cofibrant endpoints. Applying the same original Q to both components of an
Arrow gives a cofiber functor on every input arrow, with its natural counit
comparison and both original pushout legs. No properness or cofiber-weakness
conclusion is supplied as an additional input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedOrdinaryCofiber

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The full cofiber functor of the original generated cone and chosen pushouts. -/
def cofiber : Arrow C ⥤ C :=
  OrdinaryHoChosenPuppe.cofiberFunctor (GeneratedOrdinaryCone.cone d Z hZ)
    (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ)

/-- Every input target injects into its original cofiber by the chosen right leg. -/
def targetInclusion : Arrow.rightFunc ⟶ cofiber d Z hZ where
  app F := (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inr
  naturality _ _ a :=
    (OrdinaryHoChosenPuppe.cofiberMap_target (GeneratedOrdinaryCone.cone d Z hZ)
      (GeneratedOrdinaryCone.inclusion d Z hZ)
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
      (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) a).symm

/-- The two original pushout squares give weak invariance at cofibrant endpoints. -/
theorem cofiber_map_weak {F G : Arrow C} (a : F ⟶ G)
    [IsCofibrant F.left] [IsCofibrant F.right]
    [IsCofibrant G.left] [IsCofibrant G.right]
    (hl : weakEquivalences C a.left) (hr : weakEquivalences C a.right) :
    weakEquivalences C ((cofiber d Z hZ).map a) := by
  let _ : IsCofibrant ((𝟭 C).obj F.left) := inferInstanceAs (IsCofibrant F.left)
  let _ : IsCofibrant ((𝟭 C).obj G.left) := inferInstanceAs (IsCofibrant G.left)
  let _ : Cofibration ((GeneratedOrdinaryCone.inclusion d Z hZ).app F.left) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration d Z hZ F.left)
  let _ : Cofibration ((GeneratedOrdinaryCone.inclusion d Z hZ).app G.left) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration d Z hZ G.left)
  let _ : WeakEquivalence a.left := (weakEquivalence_iff _).mpr hl
  let _ : WeakEquivalence a.right := (weakEquivalence_iff _).mpr hr
  let _ : WeakEquivalence ((GeneratedOrdinaryCone.cone d Z hZ).map a.left) :=
    (weakEquivalence_iff _).mpr (GeneratedOrdinaryCone.cone_map_weak d Z hZ a.left)
  exact (weakEquivalence_iff _).mp
    (weakEquivalence_map_of_isPushouts_of_cofibrant
      (IsPushout.of_isColimit (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ F))
      (IsPushout.of_isColimit (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ G))
      (a := a.left) (b := (GeneratedOrdinaryCone.cone d Z hZ).map a.left)
      (c := a.right) (d := (cofiber d Z hZ).map a)
      ((GeneratedOrdinaryCone.inclusion d Z hZ).naturality a.left).symm a.w.symm
      (OrdinaryHoChosenPuppe.cofiberMap_cone (GeneratedOrdinaryCone.cone d Z hZ)
        (GeneratedOrdinaryCone.inclusion d Z hZ)
        (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
        (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) a)
      (OrdinaryHoChosenPuppe.cofiberMap_target (GeneratedOrdinaryCone.cone d Z hZ)
        (GeneratedOrdinaryCone.inclusion d Z hZ)
        (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
        (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) a))

/-- Both components of the input arrow use the same original generated Q. -/
def replacementArrow : Arrow C ⥤ Arrow C :=
  (GeneratedFunctorialReplacements.Q d).mapArrow

/-- The canonical Arrow functor retains both original Q counits and their square. -/
def replacementArrowCounit : replacementArrow d ⟶ 𝟭 (Arrow C) :=
  (Functor.mapArrowFunctor C C).map (GeneratedFunctorialReplacements.counit d)

/-- The complete source component is the original Q counit. -/
theorem replacementArrowCounit_left (F : Arrow C) :
    ((replacementArrowCounit d).app F).left =
      (GeneratedFunctorialReplacements.counit d).app F.left := rfl

/-- The complete target component is the original Q counit. -/
theorem replacementArrowCounit_right (F : Arrow C) :
    ((replacementArrowCounit d).app F).right =
      (GeneratedFunctorialReplacements.counit d).app F.right := rfl

/-- The whole original arrow is recovered through its two actual counits. -/
theorem replacementArrowCounit_square (F : Arrow C) :
    (GeneratedFunctorialReplacements.Q d).map F.hom ≫
        ((replacementArrowCounit d).app F).right =
      ((replacementArrowCounit d).app F).left ≫ F.hom :=
  ((replacementArrowCounit d).app F).w.symm

/-- The original cone cofiber is applied to the entire original Q-image arrow. -/
def derivedCofiber : Arrow C ⥤ C := replacementArrow d ⋙ cofiber d Z hZ

/-- The original Q counit square induces the full natural cofiber comparison. -/
def replacementComparison : derivedCofiber d Z hZ ⟶ cofiber d Z hZ where
  app F := (cofiber d Z hZ).map ((replacementArrowCounit d).app F)
  naturality F G a := by
    change (cofiber d Z hZ).map ((replacementArrow d).map a) ≫
        (cofiber d Z hZ).map ((replacementArrowCounit d).app G) =
      (cofiber d Z hZ).map ((replacementArrowCounit d).app F) ≫
        (cofiber d Z hZ).map a
    rw [← (cofiber d Z hZ).map_comp, ← (cofiber d Z hZ).map_comp]
    exact (cofiber d Z hZ).congr_map ((replacementArrowCounit d).naturality a)

/-- Every replacement cofiber is cofibrant by its actual target inclusion. -/
theorem derivedCofiber_isCofibrant (F : Arrow C) :
    IsCofibrant ((derivedCofiber d Z hZ).obj F) := by
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  let _ : Cofibration
      ((GeneratedOrdinaryCone.inclusion d Z hZ).app ((replacementArrow d).obj F).left) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration d Z hZ _)
  let _ : Cofibration
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ ((replacementArrow d).obj F)).inr :=
    OrdinaryHoChosenPuppe.cofiberTarget_cofibration (GeneratedOrdinaryCone.cone d Z hZ)
      (GeneratedOrdinaryCone.inclusion d Z hZ)
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
      (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) ((replacementArrow d).obj F)
  exact isCofibrant_of_cofibration (X := ((replacementArrow d).obj F).right)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ ((replacementArrow d).obj F)).inr

/-- Original pointwise weak arrow maps give weak replacement-cofiber maps. -/
theorem derivedCofiber_map_weak {F G : Arrow C} (a : F ⟶ G)
    (hl : weakEquivalences C a.left) (hr : weakEquivalences C a.right) :
    weakEquivalences C ((derivedCofiber d Z hZ).map a) := by
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  let _ : IsCofibrant ((replacementArrow d).obj G).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d G.left
  let _ : IsCofibrant ((replacementArrow d).obj G).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d G.right
  exact cofiber_map_weak d Z hZ ((replacementArrow d).map a)
    (GeneratedFunctorialReplacements.Q_map_weak d a.left hl)
    (GeneratedFunctorialReplacements.Q_map_weak d a.right hr)

/-- The same original counit comparison is weak at cofibrant input endpoints. -/
theorem replacementComparison_weak (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] :
    weakEquivalences C ((replacementComparison d Z hZ).app F) := by
  let _ : IsCofibrant ((𝟭 (Arrow C)).obj F).left := inferInstanceAs (IsCofibrant F.left)
  let _ : IsCofibrant ((𝟭 (Arrow C)).obj F).right := inferInstanceAs (IsCofibrant F.right)
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  exact cofiber_map_weak d Z hZ ((replacementArrowCounit d).app F)
    (GeneratedFunctorialReplacements.counit_weak d F.left)
    (GeneratedFunctorialReplacements.counit_weak d F.right)

/-- The full comparison keeps the cone leg and the original source counit. -/
theorem replacementComparison_cone (F : Arrow C) :
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ ((replacementArrow d).obj F)).inl ≫
        (replacementComparison d Z hZ).app F =
      (GeneratedOrdinaryCone.cone d Z hZ).map
        ((GeneratedFunctorialReplacements.counit d).app F.left) ≫
          (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inl :=
  OrdinaryHoChosenPuppe.cofiberMap_cone (GeneratedOrdinaryCone.cone d Z hZ)
    (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) ((replacementArrowCounit d).app F)

/-- The full comparison keeps the target leg and the original target counit. -/
theorem replacementComparison_target (F : Arrow C) :
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ ((replacementArrow d).obj F)).inr ≫
        (replacementComparison d Z hZ).app F =
      (GeneratedFunctorialReplacements.counit d).app F.right ≫
        (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inr :=
  OrdinaryHoChosenPuppe.cofiberMap_target (GeneratedOrdinaryCone.cone d Z hZ)
    (GeneratedOrdinaryCone.inclusion d Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) ((replacementArrowCounit d).app F)

end HomotopicalAlgebra.GeneratedOrdinaryCofiber
