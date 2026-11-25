/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Whiskering

/-!
# Functorial limits created from a selected target cone family

The creation data and every target cone are explicit inputs. The resulting
functor retains the points of the actual native lifted cones, rather than
selecting the unrelated canonical `lim` functor. Its image is naturally
isomorphic to the selected target-cone point functor. Changes of creation
data and target cones are compared by the actual universal properties.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe vJ vC vE uJ uC uE

namespace CategoryTheory.Limits.CreatedLimitFunctor

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  {E : Type uE} [Category.{vE} E] (R : C ⥤ E)
  (creation : CreatesLimitsOfShape J R)
  (cones : ∀ F : J ⥤ C, Cone (F ⋙ R))
  (limits : ∀ F, IsLimit (cones F))

/-- The original cone is the actual lift selected by the supplied creation data. -/
def cone (F : J ⥤ C) : Cone F := by
  letI := creation
  exact liftLimit (limits F)

/-- The same original lifted cone has the native created universal property. -/
def isLimit (F : J ⥤ C) : IsLimit (cone R creation cones limits F) := by
  letI := creation
  exact liftedLimitIsLimit (limits F)

/-- The full native cone comparison retains the actual target cone. -/
def imageIso (F : J ⥤ C) : R.mapCone (cone R creation cones limits F) ≅ cones F := by
  letI := creation
  exact liftedLimitMapsToOriginal (limits F)

/-- The point comparison is extracted from the same full cone isomorphism. -/
def pointIso (F : J ⥤ C) : R.obj (cone R creation cones limits F).pt ≅ (cones F).pt :=
  (Cone.forget (F ⋙ R)).mapIso (imageIso R creation cones limits F)

/-- Every original projection is retained by the forward point comparison. -/
theorem pointIso_hom_π (F : J ⥤ C) (j : J) :
    (pointIso R creation cones limits F).hom ≫ (cones F).π.app j =
      R.map ((cone R creation cones limits F).π.app j) :=
  (imageIso R creation cones limits F).hom.w j

/-- Every original projection is retained by the inverse point comparison. -/
theorem pointIso_inv_π (F : J ⥤ C) (j : J) :
    (pointIso R creation cones limits F).inv ≫
      R.map ((cone R creation cones limits F).π.app j) = (cones F).π.app j :=
  (imageIso R creation cones limits F).inv.w j

/-- The target point functor uses the actual selected cones and their universal maps. -/
def targetFunctor : (J ⥤ C) ⥤ E where
  obj F := (cones F).pt
  map {F G} α := (limits G).map (cones F) (Functor.whiskerRight α R)
  map_id F := by
    apply (limits F).hom_ext
    intro j
    simp
  map_comp α β := by
    apply (limits _).hom_ext
    intro j
    simp [Category.assoc]

/-- Every target functor map has its full original projection equation. -/
theorem target_map_π {F G : J ⥤ C} (α : F ⟶ G) (j : J) :
    (targetFunctor R cones limits).map α ≫ (cones G).π.app j =
      (cones F).π.app j ≫ R.map (α.app j) :=
  IsLimit.map_π _ _ _ _

/-- The original created-limit functor retains the actual lifted cone points. -/
def functor : (J ⥤ C) ⥤ C where
  obj F := (cone R creation cones limits F).pt
  map {F G} α := (isLimit R creation cones limits G).map
    (cone R creation cones limits F) α
  map_id F := by
    apply (isLimit R creation cones limits F).hom_ext
    intro j
    simp
  map_comp α β := by
    apply (isLimit R creation cones limits _).hom_ext
    intro j
    simp [Category.assoc]

/-- The complete original map function is the actual created universal map. -/
theorem map_eq {F G : J ⥤ C} :
    (functor R creation cones limits).map (X := F) (Y := G) =
      fun α ↦ (isLimit R creation cones limits G).map
        (cone R creation cones limits F) α := rfl

/-- Every original diagram map satisfies every original projection equation. -/
theorem map_π {F G : J ⥤ C} (α : F ⟶ G) (j : J) :
    (functor R creation cones limits).map α ≫
      (cone R creation cones limits G).π.app j =
        (cone R creation cones limits F).π.app j ≫ α.app j :=
  IsLimit.map_π _ _ _ _

/-- The full point-comparison family is natural for all original diagram maps. -/
theorem map_pointIso_hom {F G : J ⥤ C} (α : F ⟶ G) :
    R.map ((functor R creation cones limits).map α) ≫
        (pointIso R creation cones limits G).hom =
      (pointIso R creation cones limits F).hom ≫ (targetFunctor R cones limits).map α := by
  let m : (cone R creation cones limits F).pt ⟶ (cone R creation cones limits G).pt :=
    (functor R creation cones limits).map α
  let n : (cones F).pt ⟶ (cones G).pt := (targetFunctor R cones limits).map α
  change R.map m ≫ (pointIso R creation cones limits G).hom =
    (pointIso R creation cones limits F).hom ≫ n
  apply (limits G).hom_ext
  intro j
  have hm : m ≫ (cone R creation cones limits G).π.app j =
      (cone R creation cones limits F).π.app j ≫ α.app j :=
    map_π R creation cones limits α j
  have hn : n ≫ (cones G).π.app j = (cones F).π.app j ≫ R.map (α.app j) :=
    target_map_π R cones limits α j
  calc
    (R.map m ≫ (pointIso R creation cones limits G).hom) ≫ (cones G).π.app j =
        R.map m ≫ R.map ((cone R creation cones limits G).π.app j) := by
      rw [Category.assoc, pointIso_hom_π]
    _ = R.map (m ≫ (cone R creation cones limits G).π.app j) := (R.map_comp _ _).symm
    _ = R.map ((cone R creation cones limits F).π.app j ≫ α.app j) := congrArg R.map hm
    _ = R.map ((cone R creation cones limits F).π.app j) ≫ R.map (α.app j) := R.map_comp _ _
    _ = ((pointIso R creation cones limits F).hom ≫ (cones F).π.app j) ≫ R.map (α.app j) := by
      rw [pointIso_hom_π]
    _ = ((pointIso R creation cones limits F).hom ≫ n) ≫ (cones G).π.app j := by
      simpa only [Category.assoc] using
        (congrArg (fun t ↦ (pointIso R creation cones limits F).hom ≫ t) hn).symm

/-- The natural comparison uses the actual original point isomorphisms. -/
def comparison : functor R creation cones limits ⋙ R ≅ targetFunctor R cones limits :=
  NatIso.ofComponents (pointIso R creation cones limits)
    (fun α ↦ map_pointIso_hom R creation cones limits α)

/-- The full forward comparison component is the native lifted-cone point map. -/
theorem comparison_hom_app (F : J ⥤ C) :
    (comparison R creation cones limits).hom.app F =
      (imageIso R creation cones limits F).hom.hom := rfl

/-- The full inverse comparison component is the native inverse lifted-cone point map. -/
theorem comparison_inv_app (F : J ⥤ C) :
    (comparison R creation cones limits).inv.app F =
      (imageIso R creation cones limits F).inv.hom := rfl

/-- The inverse comparison is natural on every original map. -/
theorem map_pointIso_inv {F G : J ⥤ C} (α : F ⟶ G) :
    (targetFunctor R cones limits).map α ≫ (pointIso R creation cones limits G).inv =
      (pointIso R creation cones limits F).inv ≫
        R.map ((functor R creation cones limits).map α) :=
  (comparison R creation cones limits).inv.naturality α

/-- The actual original universal lift retains the selected lifted cone. -/
def lift (F : J ⥤ C) (s : Cone F) : s.pt ⟶ (functor R creation cones limits).obj F :=
  (isLimit R creation cones limits F).lift s

/-- The original universal lift satisfies every original projection. -/
theorem lift_π (F : J ⥤ C) (s : Cone F) (j : J) :
    lift R creation cones limits F s ≫ (cone R creation cones limits F).π.app j =
      s.π.app j :=
  (isLimit R creation cones limits F).fac s j

/-- The original universal lift is unique with those full original projections. -/
theorem lift_unique (F : J ⥤ C) (s : Cone F)
    (m : s.pt ⟶ (functor R creation cones limits).obj F)
    (hm : ∀ j, m ≫ (cone R creation cones limits F).π.app j = s.π.app j) :
    m = lift R creation cones limits F s :=
  (isLimit R creation cones limits F).uniq s m hm

section Changes

variable (creation' : CreatesLimitsOfShape J R)
  (cones' : ∀ F : J ⥤ C, Cone (F ⋙ R)) (limits' : ∀ F, IsLimit (cones' F))

/-- Independently supplied creation data and target cones give an actual natural
isomorphism between the resulting original functors, rather than an equality. -/
def compareChoices : functor R creation cones limits ≅ functor R creation' cones' limits' :=
  NatIso.ofComponents
    (fun F ↦ IsLimit.conePointUniqueUpToIso
      (isLimit R creation cones limits F) (isLimit R creation' cones' limits' F))
    (by
      intro F G α
      let m : (cone R creation cones limits F).pt ⟶ (cone R creation cones limits G).pt :=
        (functor R creation cones limits).map α
      let n : (cone R creation' cones' limits' F).pt ⟶
          (cone R creation' cones' limits' G).pt := (functor R creation' cones' limits').map α
      let iF := IsLimit.conePointUniqueUpToIso (isLimit R creation cones limits F)
        (isLimit R creation' cones' limits' F)
      let iG := IsLimit.conePointUniqueUpToIso (isLimit R creation cones limits G)
        (isLimit R creation' cones' limits' G)
      change m ≫ iG.hom = iF.hom ≫ n
      apply (isLimit R creation' cones' limits' G).hom_ext
      intro j
      have hm : m ≫ (cone R creation cones limits G).π.app j =
          (cone R creation cones limits F).π.app j ≫ α.app j :=
        map_π R creation cones limits α j
      have hn : n ≫ (cone R creation' cones' limits' G).π.app j =
          (cone R creation' cones' limits' F).π.app j ≫ α.app j :=
        map_π R creation' cones' limits' α j
      have hiF : iF.hom ≫ (cone R creation' cones' limits' F).π.app j =
          (cone R creation cones limits F).π.app j :=
        IsLimit.conePointUniqueUpToIso_hom_comp _ _ j
      have hiG : iG.hom ≫ (cone R creation' cones' limits' G).π.app j =
          (cone R creation cones limits G).π.app j :=
        IsLimit.conePointUniqueUpToIso_hom_comp _ _ j
      calc
        (m ≫ iG.hom) ≫ (cone R creation' cones' limits' G).π.app j =
            m ≫ (cone R creation cones limits G).π.app j := by
          simpa only [Category.assoc] using congrArg (fun t ↦ m ≫ t) hiG
        _ = (cone R creation cones limits F).π.app j ≫ α.app j := hm
        _ = (iF.hom ≫ (cone R creation' cones' limits' F).π.app j) ≫ α.app j := by rw [hiF]
        _ = (iF.hom ≫ n) ≫ (cone R creation' cones' limits' G).π.app j := by
          simpa only [Category.assoc] using (congrArg (fun t ↦ iF.hom ≫ t) hn).symm)

/-- The forward choice comparison retains every original projection. -/
theorem compareChoices_hom_π (F : J ⥤ C) (j : J) :
    (compareChoices R creation cones limits creation' cones' limits').hom.app F ≫
      (cone R creation' cones' limits' F).π.app j =
        (cone R creation cones limits F).π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimit R creation cones limits F)
    (isLimit R creation' cones' limits' F) j

/-- The inverse choice comparison retains every original projection. -/
theorem compareChoices_inv_π (F : J ⥤ C) (j : J) :
    (compareChoices R creation cones limits creation' cones' limits').inv.app F ≫
      (cone R creation cones limits F).π.app j =
        (cone R creation' cones' limits' F).π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimit R creation cones limits F)
    (isLimit R creation' cones' limits' F) j

/-- The comparison of original choices agrees with the actual target-cone
choice comparison on the full forward component functions. -/
theorem compareChoices_pointIso (F : J ⥤ C) :
    R.map ((compareChoices R creation cones limits creation' cones' limits').hom.app F) ≫
        (pointIso R creation' cones' limits' F).hom =
      (pointIso R creation cones limits F).hom ≫
        (IsLimit.conePointUniqueUpToIso (limits F) (limits' F)).hom := by
  let m : (cone R creation cones limits F).pt ⟶ (cone R creation' cones' limits' F).pt :=
    (compareChoices R creation cones limits creation' cones' limits').hom.app F
  let i : (cones F).pt ⟶ (cones' F).pt :=
    (IsLimit.conePointUniqueUpToIso (limits F) (limits' F)).hom
  change R.map m ≫ (pointIso R creation' cones' limits' F).hom =
    (pointIso R creation cones limits F).hom ≫ i
  apply (limits' F).hom_ext
  intro j
  have hm : m ≫ (cone R creation' cones' limits' F).π.app j =
      (cone R creation cones limits F).π.app j :=
    compareChoices_hom_π R creation cones limits creation' cones' limits' F j
  have hi : i ≫ (cones' F).π.app j = (cones F).π.app j :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ j
  calc
    (R.map m ≫ (pointIso R creation' cones' limits' F).hom) ≫ (cones' F).π.app j =
        R.map m ≫ R.map ((cone R creation' cones' limits' F).π.app j) := by
      rw [Category.assoc, pointIso_hom_π]
    _ = R.map (m ≫ (cone R creation' cones' limits' F).π.app j) := (R.map_comp _ _).symm
    _ = R.map ((cone R creation cones limits F).π.app j) := congrArg R.map hm
    _ = (pointIso R creation cones limits F).hom ≫ (cones F).π.app j :=
      (pointIso_hom_π R creation cones limits F j).symm
    _ = ((pointIso R creation cones limits F).hom ≫ i) ≫ (cones' F).π.app j := by
      simpa only [Category.assoc] using
        (congrArg (fun t ↦ (pointIso R creation cones limits F).hom ≫ t) hi).symm

end Changes

end CategoryTheory.Limits.CreatedLimitFunctor
