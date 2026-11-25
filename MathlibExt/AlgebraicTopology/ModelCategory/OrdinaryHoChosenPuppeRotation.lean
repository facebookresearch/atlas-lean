/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# Rotation of the actual chosen Puppe cofiber

The cofiber of the original target inclusion is compared with the same
chosen suspension by its two original pushout legs. The comparison is
weak by cofibrant pushout gluing. Its next boundary is the suspended
original map followed by suspension reversal.

Reversal is constructed in the ordinary homotopy category from the two
weak collapses of the actual double cone. In particular, the next
boundary is not identified with the unsigned suspended map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OrdinaryHoChosenPuppe

namespace HomotopicalAlgebra.OrdinaryHoChosenPuppeRotation

variable {C : Type u} [Category.{v} C]
  (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

/-- The original target inclusion, with the same selected cofiber. -/
abbrev targetArrow (F : Arrow C) : Arrow C := Arrow.mk (c F).inr

/-- Every original Arrow square induces its full target-inclusion square. -/
def targetArrowMap {F G : Arrow C} (q : F ⟶ G) :
    targetArrow cone ι c F ⟶ targetArrow cone ι c G :=
  Arrow.homMk q.right (cofiberMap cone ι c hc q)
    (cofiberMap_target cone ι c hc q).symm

/-- The target-inclusion construction retains both components on all Arrows. -/
def targetArrowFunctor : Arrow C ⥤ Arrow C where
  obj := targetArrow cone ι c
  map q := targetArrowMap cone ι c hc q
  map_id F := by
    apply Arrow.hom_ext
    · rfl
    · exact cofiberMap_id cone ι c hc F
  map_comp q r := by
    apply Arrow.hom_ext
    · rfl
    · exact cofiberMap_comp cone ι c hc q r

/-- The next cofiber is selected by the same original family of cocones. -/
abbrev nextCofiberCone (F : Arrow C) := c (targetArrow cone ι c F)

/-- Its functor uses the same original cofiber maps on the whole inclusion square. -/
def nextCofiberFunctor : Arrow C ⥤ C :=
  targetArrowFunctor cone ι c hc ⋙ cofiberFunctor cone ι c hc

/-- The insertion into the cone is an actual functor on the original objects. -/
def coneArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (ι.app X)
  map f := Arrow.homMk f (cone.map f) (ι.naturality f)
  map_id X := by
    apply Arrow.hom_ext
    · rfl
    · exact cone.map_id X
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · exact cone.map_comp f g

/-- Both copies of the original cone are retained in the selected double cone. -/
abbrev doubleCone (X : C) := c (Arrow.mk (ι.app X))

/-- The whole double-cone functor uses the original insertion squares. -/
def doubleConeFunctor : C ⥤ C :=
  coneArrowFunctor cone ι ⋙ cofiberFunctor cone ι c hc

/-- The complete map on the two original cone copies. -/
def doubleConeMap {X Y : C} (f : X ⟶ Y) :
    (doubleCone cone ι c X).pt ⟶ (doubleCone cone ι c Y).pt :=
  cofiberMap cone ι c hc ((coneArrowFunctor cone ι).map f)

/-- The first double-cone leg retains the actual cone functor map. -/
theorem doubleConeMap_left {X Y : C} (f : X ⟶ Y) :
    (doubleCone cone ι c X).inl ≫ doubleConeMap cone ι c hc f =
      cone.map f ≫ (doubleCone cone ι c Y).inl :=
  cofiberMap_cone cone ι c hc ((coneArrowFunctor cone ι).map f)

/-- The second double-cone leg retains that same whole cone functor map. -/
theorem doubleConeMap_right {X Y : C} (f : X ⟶ Y) :
    (doubleCone cone ι c X).inr ≫ doubleConeMap cone ι c hc f =
      cone.map f ≫ (doubleCone cone ι c Y).inr :=
  cofiberMap_target cone ι c hc ((coneArrowFunctor cone ι).map f)

/-- Exchange the two full original cone copies by the selected colimit desc. -/
def doubleConeSwap (X : C) : (doubleCone cone ι c X).pt ⟶ (doubleCone cone ι c X).pt :=
  PushoutCocone.IsColimit.desc (hc (Arrow.mk (ι.app X)))
    (doubleCone cone ι c X).inr (doubleCone cone ι c X).inl
    (doubleCone cone ι c X).condition.symm

/-- Exchange sends the first original cone leg to the second one. -/
theorem doubleConeSwap_left (X : C) :
    (doubleCone cone ι c X).inl ≫ doubleConeSwap cone ι c hc X =
      (doubleCone cone ι c X).inr :=
  PushoutCocone.IsColimit.inl_desc (hc (Arrow.mk (ι.app X))) _ _ _

/-- Exchange sends the second original cone leg to the first one. -/
theorem doubleConeSwap_right (X : C) :
    (doubleCone cone ι c X).inr ≫ doubleConeSwap cone ι c hc X =
      (doubleCone cone ι c X).inl :=
  PushoutCocone.IsColimit.inr_desc (hc (Arrow.mk (ι.app X))) _ _ _

/-- Both original legs prove that exchange is an involution on the entire double cone. -/
theorem doubleConeSwap_involutive (X : C) :
    doubleConeSwap cone ι c hc X ≫ doubleConeSwap cone ι c hc X =
      𝟙 (doubleCone cone ι c X).pt := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Arrow.mk (ι.app X)))
  · rw [← Category.assoc, doubleConeSwap_left, doubleConeSwap_right, Category.comp_id]
  · rw [← Category.assoc, doubleConeSwap_right, doubleConeSwap_left, Category.comp_id]

variable (Z : C) (hZ : IsZero Z)

/-- Collapse the first cone and keep the second, using the original zero endpoint. -/
def collapseLeft (X : C) :
    (doubleCone cone ι c X).pt ⟶ (suspensionCone cone ι c Z hZ X).pt :=
  PushoutCocone.IsColimit.desc (hc (Arrow.mk (ι.app X)))
    (toZero Z hZ (cone.obj X) ≫ (suspensionCone cone ι c Z hZ X).inr)
    (suspensionCone cone ι c Z hZ X).inl (by
      change ι.app X ≫ (toZero Z hZ (cone.obj X) ≫
        (suspensionCone cone ι c Z hZ X).inr) =
        ι.app X ≫ (suspensionCone cone ι c Z hZ X).inl
      rw [← Category.assoc, toZero_comp]
      exact (suspensionCone cone ι c Z hZ X).condition.symm)

/-- Collapse the second cone and keep the first by the original Puppe boundary. -/
def collapseRight (X : C) :
    (doubleCone cone ι c X).pt ⟶ (suspensionCone cone ι c Z hZ X).pt :=
  boundary cone ι c hc Z hZ (Arrow.mk (ι.app X))

/-- The first collapse retains its entire collapsed-cone endpoint map. -/
theorem collapseLeft_left (X : C) :
    (doubleCone cone ι c X).inl ≫ collapseLeft cone ι c hc Z hZ X =
      toZero Z hZ (cone.obj X) ≫ (suspensionCone cone ι c Z hZ X).inr :=
  PushoutCocone.IsColimit.inl_desc (hc (Arrow.mk (ι.app X))) _ _ _

/-- The first collapse keeps the second original cone-to-suspension leg. -/
theorem collapseLeft_right (X : C) :
    (doubleCone cone ι c X).inr ≫ collapseLeft cone ι c hc Z hZ X =
      (suspensionCone cone ι c Z hZ X).inl :=
  PushoutCocone.IsColimit.inr_desc (hc (Arrow.mk (ι.app X))) _ _ _

/-- The second collapse keeps the first original cone-to-suspension leg. -/
theorem collapseRight_left (X : C) :
    (doubleCone cone ι c X).inl ≫ collapseRight cone ι c hc Z hZ X =
      (suspensionCone cone ι c Z hZ X).inl :=
  boundary_cone cone ι c hc Z hZ (Arrow.mk (ι.app X))

/-- The second collapse retains its entire collapsed-cone endpoint map. -/
theorem collapseRight_right (X : C) :
    (doubleCone cone ι c X).inr ≫ collapseRight cone ι c hc Z hZ X =
      toZero Z hZ (cone.obj X) ≫ (suspensionCone cone ι c Z hZ X).inr :=
  boundary_target cone ι c hc Z hZ (Arrow.mk (ι.app X))

/-- Exchange followed by the first collapse is the second actual collapse. -/
theorem doubleConeSwap_collapseLeft (X : C) :
    doubleConeSwap cone ι c hc X ≫ collapseLeft cone ι c hc Z hZ X =
      collapseRight cone ι c hc Z hZ X := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Arrow.mk (ι.app X)))
  · rw [← Category.assoc, doubleConeSwap_left, collapseLeft_right, collapseRight_left]
  · rw [← Category.assoc, doubleConeSwap_right, collapseLeft_left, collapseRight_right]

/-- Exchange followed by the second collapse is the first actual collapse. -/
theorem doubleConeSwap_collapseRight (X : C) :
    doubleConeSwap cone ι c hc X ≫ collapseRight cone ι c hc Z hZ X =
      collapseLeft cone ι c hc Z hZ X := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Arrow.mk (ι.app X)))
  · rw [← Category.assoc, doubleConeSwap_left, collapseRight_right, collapseLeft_left]
  · rw [← Category.assoc, doubleConeSwap_right, collapseRight_left, collapseLeft_right]

/-- The first collapse is natural on the full original source morphism. -/
theorem collapseLeft_naturality {X Y : C} (f : X ⟶ Y) :
    doubleConeMap cone ι c hc f ≫ collapseLeft cone ι c hc Z hZ Y =
      collapseLeft cone ι c hc Z hZ X ≫ suspensionMap cone ι c hc Z hZ f := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Arrow.mk (ι.app X)))
  · rw [← Category.assoc, doubleConeMap_left, Category.assoc, collapseLeft_left,
      ← Category.assoc, toZero_comp, ← Category.assoc, collapseLeft_left,
      Category.assoc, suspensionMap_zero]
    rfl
  · rw [← Category.assoc, doubleConeMap_right, Category.assoc, collapseLeft_right,
      ← Category.assoc, collapseLeft_right, suspensionMap_cone]

/-- The second collapse is natural on that same whole source morphism. -/
theorem collapseRight_naturality {X Y : C} (f : X ⟶ Y) :
    doubleConeMap cone ι c hc f ≫ collapseRight cone ι c hc Z hZ Y =
      collapseRight cone ι c hc Z hZ X ≫ suspensionMap cone ι c hc Z hZ f :=
  boundary_naturality cone ι c hc Z hZ ((coneArrowFunctor cone ι).map f)

/-- The first collapse is a whole natural transformation of the actual chosen functors. -/
def collapseLeftNatTrans : doubleConeFunctor cone ι c hc ⟶
    suspensionFunctor cone ι c hc Z hZ where
  app X := collapseLeft cone ι c hc Z hZ X
  naturality _ _ f := collapseLeft_naturality cone ι c hc Z hZ f

/-- The second collapse is a whole natural transformation of those same original functors. -/
def collapseRightNatTrans : doubleConeFunctor cone ι c hc ⟶
    suspensionFunctor cone ι c hc Z hZ where
  app X := collapseRight cone ι c hc Z hZ X
  naturality _ _ f := collapseRight_naturality cone ι c hc Z hZ f

/-- The two original cofiber legs prove naturality of the cone comparison. -/
theorem coneComparison_naturality {F G : Arrow C} (q : F ⟶ G) :
    cofiberMap cone ι c hc q ≫ coneComparison cone ι c hc G =
      coneComparison cone ι c hc F ≫ cone.map q.right := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [← Category.assoc, cofiberMap_cone, Category.assoc, coneComparison_cone,
      ← Category.assoc, coneComparison_cone, ← Functor.map_comp, ← Functor.map_comp, q.w]
  · rw [← Category.assoc, cofiberMap_target, Category.assoc, coneComparison_target,
      ← Category.assoc, coneComparison_target]
    exact ι.naturality q.right

/-- Compare the actual next cofiber with the same selected suspension of the original source. -/
def rotationComparison (F : Arrow C) :
    (nextCofiberCone cone ι c F).pt ⟶ (suspensionCone cone ι c Z hZ F.left).pt :=
  PushoutCocone.IsColimit.desc (hc (targetArrow cone ι c F))
    (toZero Z hZ (cone.obj F.right) ≫ (suspensionCone cone ι c Z hZ F.left).inr)
    (boundary cone ι c hc Z hZ F) (by
      change ι.app F.right ≫ (toZero Z hZ (cone.obj F.right) ≫
        (suspensionCone cone ι c Z hZ F.left).inr) =
        (c F).inr ≫ boundary cone ι c hc Z hZ F
      rw [← Category.assoc, toZero_comp]
      exact (boundary_target cone ι c hc Z hZ F).symm)

/-- The next comparison collapses the entire original target cone. -/
theorem rotationComparison_cone (F : Arrow C) :
    (nextCofiberCone cone ι c F).inl ≫ rotationComparison cone ι c hc Z hZ F =
      toZero Z hZ (cone.obj F.right) ≫ (suspensionCone cone ι c Z hZ F.left).inr :=
  PushoutCocone.IsColimit.inl_desc (hc (targetArrow cone ι c F)) _ _ _

/-- Its other leg is the unchanged original boundary on the whole original cofiber. -/
theorem rotationComparison_cofiber (F : Arrow C) :
    (nextCofiberCone cone ι c F).inr ≫ rotationComparison cone ι c hc Z hZ F =
      boundary cone ι c hc Z hZ F :=
  PushoutCocone.IsColimit.inr_desc (hc (targetArrow cone ι c F)) _ _ _

/-- The comparison square is a pushout constructed from the two actual chosen colimits. -/
theorem rotationComparison_isPushout (F : Arrow C) :
    IsPushout (nextCofiberCone cone ι c F).inl
      (toZero Z hZ (cone.obj F.right)) (rotationComparison cone ι c hc Z hZ F)
      (suspensionCone cone ι c Z hZ F.left).inr := by
  have hOuter : IsPushout (c F).inr
      (ι.app F.right ≫ toZero Z hZ (cone.obj F.right))
      ((nextCofiberCone cone ι c F).inr ≫ rotationComparison cone ι c hc Z hZ F)
      (suspensionCone cone ι c Z hZ F.left).inr := by
    rw [toZero_comp, rotationComparison_cofiber]
    exact targetQuotientIsPushout cone ι c hc Z hZ F
  exact hOuter.of_top (rotationComparison_cone cone ι c hc Z hZ F)
    (IsPushout.of_isColimit (hc (targetArrow cone ι c F))).flip

/-- Rotation comparison is natural on both components of every original Arrow square. -/
theorem rotationComparison_naturality {F G : Arrow C} (q : F ⟶ G) :
    cofiberMap cone ι c hc (targetArrowMap cone ι c hc q) ≫
        rotationComparison cone ι c hc Z hZ G =
      rotationComparison cone ι c hc Z hZ F ≫ suspensionMap cone ι c hc Z hZ q.left := by
  apply PushoutCocone.IsColimit.hom_ext (hc (targetArrow cone ι c F))
  · rw [← Category.assoc, cofiberMap_cone]
    change (cone.map q.right ≫ (nextCofiberCone cone ι c G).inl) ≫ _ = _
    rw [Category.assoc, rotationComparison_cone, ← Category.assoc, toZero_comp,
      ← Category.assoc, rotationComparison_cone, Category.assoc, suspensionMap_zero]
  · rw [← Category.assoc, cofiberMap_target]
    change (cofiberMap cone ι c hc q ≫ (nextCofiberCone cone ι c G).inr) ≫ _ = _
    rw [Category.assoc, rotationComparison_cofiber, ← Category.assoc,
      rotationComparison_cofiber, boundary_naturality]

/-- The entire rotation comparison is a natural transformation on all original Arrows. -/
def rotationComparisonNatTrans : nextCofiberFunctor cone ι c hc ⟶
    Arrow.leftFunc ⋙ suspensionFunctor cone ι c hc Z hZ where
  app F := rotationComparison cone ι c hc Z hZ F
  naturality _ _ q := rotationComparison_naturality cone ι c hc Z hZ q

/-- Map the next cofiber to the original target double cone with both actual legs. -/
def rotationToDoubleCone (F : Arrow C) :
    (nextCofiberCone cone ι c F).pt ⟶ (doubleCone cone ι c F.right).pt :=
  PushoutCocone.IsColimit.desc (hc (targetArrow cone ι c F))
    (doubleCone cone ι c F.right).inl
    (coneComparison cone ι c hc F ≫ (doubleCone cone ι c F.right).inr) (by
      change ι.app F.right ≫ (doubleCone cone ι c F.right).inl =
        (c F).inr ≫ (coneComparison cone ι c hc F ≫ (doubleCone cone ι c F.right).inr)
      rw [← Category.assoc, coneComparison_target]
      exact (doubleCone cone ι c F.right).condition)

/-- The first component keeps the original target-cone inclusion. -/
theorem rotationToDoubleCone_cone (F : Arrow C) :
    (nextCofiberCone cone ι c F).inl ≫ rotationToDoubleCone cone ι c hc F =
      (doubleCone cone ι c F.right).inl :=
  PushoutCocone.IsColimit.inl_desc (hc (targetArrow cone ι c F)) _ _ _

/-- The second component keeps the whole original cofiber-to-cone comparison. -/
theorem rotationToDoubleCone_cofiber (F : Arrow C) :
    (nextCofiberCone cone ι c F).inr ≫ rotationToDoubleCone cone ι c hc F =
      coneComparison cone ι c hc F ≫ (doubleCone cone ι c F.right).inr :=
  PushoutCocone.IsColimit.inr_desc (hc (targetArrow cone ι c F)) _ _ _

/-- The whole double-cone comparison is natural on every original Arrow square. -/
theorem rotationToDoubleCone_naturality {F G : Arrow C} (q : F ⟶ G) :
    cofiberMap cone ι c hc (targetArrowMap cone ι c hc q) ≫
        rotationToDoubleCone cone ι c hc G =
      rotationToDoubleCone cone ι c hc F ≫ doubleConeMap cone ι c hc q.right := by
  apply PushoutCocone.IsColimit.hom_ext (hc (targetArrow cone ι c F))
  · rw [← Category.assoc, cofiberMap_cone]
    change (cone.map q.right ≫ (nextCofiberCone cone ι c G).inl) ≫ _ = _
    rw [Category.assoc, rotationToDoubleCone_cone, ← Category.assoc,
      rotationToDoubleCone_cone, doubleConeMap_left]
  · rw [← Category.assoc, cofiberMap_target]
    change (cofiberMap cone ι c hc q ≫ (nextCofiberCone cone ι c G).inr) ≫ _ = _
    rw [Category.assoc, rotationToDoubleCone_cofiber, ← Category.assoc,
      coneComparison_naturality, Category.assoc, ← doubleConeMap_right,
      ← Category.assoc, ← Category.assoc, rotationToDoubleCone_cofiber]

/-- The double-cone comparison retains every Arrow as a complete natural transformation. -/
def rotationToDoubleConeNatTrans : nextCofiberFunctor cone ι c hc ⟶
    Arrow.rightFunc ⋙ doubleConeFunctor cone ι c hc where
  app F := rotationToDoubleCone cone ι c hc F
  naturality _ _ q := rotationToDoubleCone_naturality cone ι c hc q

/-- The first collapse recovers precisely the original unsigned suspended map. -/
theorem rotationToDoubleCone_collapseLeft (F : Arrow C) :
    rotationToDoubleCone cone ι c hc F ≫ collapseLeft cone ι c hc Z hZ F.right =
      rotationComparison cone ι c hc Z hZ F ≫ suspensionMap cone ι c hc Z hZ F.hom := by
  apply PushoutCocone.IsColimit.hom_ext (hc (targetArrow cone ι c F))
  · rw [← Category.assoc, rotationToDoubleCone_cone, collapseLeft_left,
      ← Category.assoc, rotationComparison_cone, Category.assoc, suspensionMap_zero]
  · rw [← Category.assoc, rotationToDoubleCone_cofiber, Category.assoc,
      collapseLeft_right, ← Category.assoc, rotationComparison_cofiber,
      boundary_suspension_factors_cone]

/-- The second collapse recovers the actual next Puppe boundary. -/
theorem rotationToDoubleCone_collapseRight (F : Arrow C) :
    rotationToDoubleCone cone ι c hc F ≫ collapseRight cone ι c hc Z hZ F.right =
      boundary cone ι c hc Z hZ (targetArrow cone ι c F) := by
  apply PushoutCocone.IsColimit.hom_ext (hc (targetArrow cone ι c F))
  · rw [← Category.assoc, rotationToDoubleCone_cone, collapseRight_left, boundary_cone]
    rfl
  · rw [← Category.assoc, rotationToDoubleCone_cofiber, Category.assoc,
      collapseRight_right, ← Category.assoc, toZero_comp, boundary_target]
    rfl

section Model

variable [ModelCategory C]

/-- The first actual double-cone collapse is weak by cofibrant pushout gluing. -/
theorem collapseLeft_weak (X : C) [IsCofibrant X] [Cofibration (ι.app X)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj X))) :
    weakEquivalences C (collapseLeft cone ι c hc Z hZ X) := by
  let _ : IsCofibrant ((𝟭 C).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : IsCofibrant (cone.obj X) := isCofibrant_of_cofibration (ι.app X)
  let _ : IsCofibrant Z := by
    rw [isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial]
    infer_instance
  let _ : WeakEquivalence (toZero Z hZ (cone.obj X)) := (weakEquivalence_iff _).mpr hCone
  have hD : IsPushout (ι.app X) (ι.app X)
      (doubleCone cone ι c X).inl (doubleCone cone ι c X).inr :=
    IsPushout.of_isColimit (hc (Arrow.mk (ι.app X)))
  have hS : IsPushout (ι.app X) (toZero Z hZ X)
      (suspensionCone cone ι c Z hZ X).inl (suspensionCone cone ι c Z hZ X).inr :=
    IsPushout.of_isColimit (hc (Arrow.mk (toZero Z hZ X)))
  apply (weakEquivalence_iff _).mp
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (A := X) (A' := X)
    hD.flip hS
    (a := 𝟙 X) (b := 𝟙 (cone.obj X)) (c := toZero Z hZ (cone.obj X))
    (by simp) (hZ.isTerminal.hom_ext _ _)
    ((collapseLeft_right cone ι c hc Z hZ X).trans (Category.id_comp _).symm)
    (collapseLeft_left cone ι c hc Z hZ X)

/-- The second actual double-cone collapse is weak by that same gluing theorem. -/
theorem collapseRight_weak (X : C) [IsCofibrant X] [Cofibration (ι.app X)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj X))) :
    weakEquivalences C (collapseRight cone ι c hc Z hZ X) := by
  let _ : IsCofibrant ((𝟭 C).obj X) := inferInstanceAs (IsCofibrant X)
  let _ : IsCofibrant (cone.obj X) := isCofibrant_of_cofibration (ι.app X)
  let _ : IsCofibrant Z := by
    rw [isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial]
    infer_instance
  let _ : WeakEquivalence (toZero Z hZ (cone.obj X)) := (weakEquivalence_iff _).mpr hCone
  have hD : IsPushout (ι.app X) (ι.app X)
      (doubleCone cone ι c X).inl (doubleCone cone ι c X).inr :=
    IsPushout.of_isColimit (hc (Arrow.mk (ι.app X)))
  have hS : IsPushout (ι.app X) (toZero Z hZ X)
      (suspensionCone cone ι c Z hZ X).inl (suspensionCone cone ι c Z hZ X).inr :=
    IsPushout.of_isColimit (hc (Arrow.mk (toZero Z hZ X)))
  apply (weakEquivalence_iff _).mp
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (A := X) (A' := X)
    hD hS
    (a := 𝟙 X) (b := 𝟙 (cone.obj X)) (c := toZero Z hZ (cone.obj X))
    (by simp) (hZ.isTerminal.hom_ext _ _)
    ((collapseRight_left cone ι c hc Z hZ X).trans (Category.id_comp _).symm)
    (collapseRight_right cone ι c hc Z hZ X)

/-- The unchanged suspension map preserves weak maps between cofibrant objects.
Weakness of its cone component is derived from the two original cone contractions. -/
theorem suspensionMap_weak_of_cofibrant {X Y : C} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] [WeakEquivalence f]
    [Cofibration (ι.app X)] [Cofibration (ι.app Y)]
    (hX : weakEquivalences C (toZero Z hZ (cone.obj X)))
    (hY : weakEquivalences C (toZero Z hZ (cone.obj Y))) :
    weakEquivalences C (suspensionMap cone ι c hc Z hZ f) := by
  let _ : WeakEquivalence (toZero Z hZ (cone.obj X)) := (weakEquivalence_iff _).mpr hX
  let _ : WeakEquivalence (toZero Z hZ (cone.obj Y)) := (weakEquivalence_iff _).mpr hY
  let _ : WeakEquivalence (cone.map f) :=
    weakEquivalence_of_postcomp_of_fac (toZero_comp Z hZ (cone.map f))
  let _ : IsCofibrant Z := by
    rw [isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial]
    infer_instance
  have hSX : IsPushout (ι.app X) (toZero Z hZ X)
      (suspensionCone cone ι c Z hZ X).inl (suspensionCone cone ι c Z hZ X).inr :=
    IsPushout.of_isColimit (hc (Arrow.mk (toZero Z hZ X)))
  have hSY : IsPushout (ι.app Y) (toZero Z hZ Y)
      (suspensionCone cone ι c Z hZ Y).inl (suspensionCone cone ι c Z hZ Y).inr :=
    IsPushout.of_isColimit (hc (Arrow.mk (toZero Z hZ Y)))
  apply (weakEquivalence_iff _).mp
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (A := X) (A' := Y)
    hSX hSY
    (a := f) (b := cone.map f) (c := 𝟙 Z)
    (ι.naturality f).symm
    (hZ.isTerminal.hom_ext _ _)
    (suspensionMap_cone cone ι c hc Z hZ f)
    ((suspensionMap_zero cone ι c hc Z hZ f).trans (Category.id_comp _).symm)

/-- The actual next-cofiber comparison is weak, without a properness hypothesis. -/
theorem rotationComparison_weak (F : Arrow C) [IsCofibrant F.right]
    [Cofibration (ι.app F.left)] [Cofibration (ι.app F.right)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj F.right))) :
    weakEquivalences C (rotationComparison cone ι c hc Z hZ F) := by
  let _ : Cofibration (c F).inr := cofiberTarget_cofibration cone ι c hc F
  let _ : Cofibration (nextCofiberCone cone ι c F).inl := by
    rw [cofibration_iff]
    exact (cofibrations C).of_isPushout
      (IsPushout.of_isColimit (hc (targetArrow cone ι c F)))
      (mem_cofibrations (c F).inr)
  let _ : IsCofibrant ((𝟭 C).obj F.right) := inferInstanceAs (IsCofibrant F.right)
  let _ : IsCofibrant (cone.obj F.right) := isCofibrant_of_cofibration (ι.app F.right)
  let _ : IsCofibrant Z := by
    rw [isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial]
    infer_instance
  let _ : WeakEquivalence (toZero Z hZ (cone.obj F.right)) :=
    (weakEquivalence_iff _).mpr hCone
  exact (weakEquivalence_iff _).mp
    (weakEquivalence_of_isPushout_of_cofibrant
      (A := cone.obj F.right) (X := Z)
      (rotationComparison_isPushout cone ι c hc Z hZ F))

/-- Suspension reversal is the whole Iso constructed from the two actual weak collapses. -/
def suspensionReversal (X : C) [IsCofibrant X] [Cofibration (ι.app X)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj X))) :
    ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ X).pt ≅
      ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ X).pt := by
  let _ : IsIso (((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X)) :=
    Localization.inverts ((weakEquivalences C).Q) (weakEquivalences C)
    (collapseLeft cone ι c hc Z hZ X) (collapseLeft_weak cone ι c hc Z hZ X hCone)
  let _ : IsIso (((weakEquivalences C).Q).map (collapseRight cone ι c hc Z hZ X)) :=
    Localization.inverts ((weakEquivalences C).Q) (weakEquivalences C)
    (collapseRight cone ι c hc Z hZ X) (collapseRight_weak cone ι c hc Z hZ X hCone)
  exact (asIso (((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X))).symm ≪≫
    asIso (((weakEquivalences C).Q).map (collapseRight cone ι c hc Z hZ X))

/-- Reversal sends the complete first collapse to the complete second collapse. -/
theorem collapseLeft_reversal (X : C) [IsCofibrant X] [Cofibration (ι.app X)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj X))) :
    ((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X) ≫
        (suspensionReversal cone ι c hc Z hZ X hCone).hom =
      ((weakEquivalences C).Q).map (collapseRight cone ι c hc Z hZ X) := by
  simp [suspensionReversal]

/-- Reversal also sends the entire second collapse to the first one. -/
theorem collapseRight_reversal (X : C) [IsCofibrant X] [Cofibration (ι.app X)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj X))) :
    ((weakEquivalences C).Q).map (collapseRight cone ι c hc Z hZ X) ≫
        (suspensionReversal cone ι c hc Z hZ X hCone).hom =
      ((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X) := by
  rw [← doubleConeSwap_collapseLeft cone ι c hc Z hZ X, Functor.map_comp,
    Category.assoc, collapseLeft_reversal, ← Functor.map_comp,
    doubleConeSwap_collapseRight]

/-- The constructed full suspension reversal is an involution. -/
theorem suspensionReversal_involutive (X : C) [IsCofibrant X] [Cofibration (ι.app X)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj X))) :
    (suspensionReversal cone ι c hc Z hZ X hCone).hom ≫
        (suspensionReversal cone ι c hc Z hZ X hCone).hom =
      𝟙 (((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ X).pt) := by
  let _ : IsIso (((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X)) :=
    Localization.inverts ((weakEquivalences C).Q) (weakEquivalences C)
    (collapseLeft cone ι c hc Z hZ X) (collapseLeft_weak cone ι c hc Z hZ X hCone)
  apply (cancel_epi (((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X))).mp
  rw [← Category.assoc, collapseLeft_reversal, collapseRight_reversal, Category.comp_id]

/-- Reversal is natural for every entire original source morphism and both cone contractions. -/
theorem suspensionReversal_naturality {X Y : C} (f : X ⟶ Y)
    [IsCofibrant X] [IsCofibrant Y] [Cofibration (ι.app X)] [Cofibration (ι.app Y)]
    (hX : weakEquivalences C (toZero Z hZ (cone.obj X)))
    (hY : weakEquivalences C (toZero Z hZ (cone.obj Y))) :
    ((weakEquivalences C).Q).map (suspensionMap cone ι c hc Z hZ f) ≫
        (suspensionReversal cone ι c hc Z hZ Y hY).hom =
      (suspensionReversal cone ι c hc Z hZ X hX).hom ≫
        ((weakEquivalences C).Q).map (suspensionMap cone ι c hc Z hZ f) := by
  let _ : IsIso (((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X)) :=
    Localization.inverts ((weakEquivalences C).Q) (weakEquivalences C)
    (collapseLeft cone ι c hc Z hZ X) (collapseLeft_weak cone ι c hc Z hZ X hX)
  apply (cancel_epi (((weakEquivalences C).Q).map (collapseLeft cone ι c hc Z hZ X))).mp
  rw [← Category.assoc, ← Functor.map_comp, ← collapseLeft_naturality,
    Functor.map_comp, Category.assoc, collapseLeft_reversal,
    ← Functor.map_comp, collapseRight_naturality, Functor.map_comp,
    ← Category.assoc, collapseLeft_reversal]

/-- Rotation retains the sign: the next boundary is suspension followed by actual reversal. -/
theorem rotationComparison_boundary (F : Arrow C) [IsCofibrant F.right]
    [Cofibration (ι.app F.right)]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj F.right))) :
    ((weakEquivalences C).Q).map (rotationComparison cone ι c hc Z hZ F) ≫
        ((weakEquivalences C).Q).map (suspensionMap cone ι c hc Z hZ F.hom) ≫
        (suspensionReversal cone ι c hc Z hZ F.right hCone).hom =
      ((weakEquivalences C).Q).map
        (boundary cone ι c hc Z hZ (targetArrow cone ι c F)) := by
  rw [← Category.assoc, ← Functor.map_comp, ← rotationToDoubleCone_collapseLeft,
    Functor.map_comp, Category.assoc, collapseLeft_reversal,
    ← Functor.map_comp, rotationToDoubleCone_collapseRight]

end Model

end HomotopicalAlgebra.OrdinaryHoChosenPuppeRotation
