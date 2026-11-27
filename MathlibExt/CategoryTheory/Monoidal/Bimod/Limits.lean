/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Bimod
import all Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits and colimits of the original bimodule carrier

The forgetful functor from `Bimod A B` creates limits. It also creates
colimits of a shape preserved by tensoring on the left by `A` and on the
right by `B`. The constructions keep the supplied underlying cone or cocone,
including its point and all its legs.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u vJ uJ

open CategoryTheory Limits MonoidalCategory MonObj
open scoped MonoidalCategory

namespace Bimod


variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : Mon C}

instance forgetFaithful : (forget (B := B) A).Faithful where
  map_injective h := hom_ext _ _ h

instance forgetReflectsIsomorphisms : (forget (B := B) A).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    let : IsIso f.hom := ‹IsIso ((forget (B := B) A).map f)›
    let e : M ≅ N := isoOfIso (asIso f.hom) f.left_act_hom f.right_act_hom
    have he : e.hom = f := by ext; rfl
    rw [← he]
    infer_instance

namespace ForgetCreatesLimits

variable {J : Type uJ} [Category.{vJ} J]
  (F : J ⥤ Bimod A B) (c : Cone (F ⋙ forget (B := B) A)) (h : IsLimit c)

/-- The supplied leg with its actual bimodule carrier made explicit. -/
def leg (j : J) : c.pt ⟶ (F.obj j).X := c.π.app j

/-- The entire original cone naturality equation on the actual carriers. -/
theorem leg_comp {j k : J} (f : j ⟶ k) :
    leg F c j ≫ (F.map f).hom = leg F c k := c.w f

/-- The original cone with each leg preceded by its left action. -/
@[reducible] def leftCone : Cone (F ⋙ forget (B := B) A) where
  pt := A.X ⊗ c.pt
  π :=
    { app := fun j => (A.X ◁ leg F c j) ≫ (F.obj j).actLeft
      naturality := fun j k f => by
        change 𝟙 (A.X ⊗ c.pt) ≫ (A.X ◁ leg F c k) ≫ (F.obj k).actLeft =
          ((A.X ◁ leg F c j) ≫ (F.obj j).actLeft) ≫ (F.map f).hom
        rw [Category.id_comp, Category.assoc, (F.map f).left_act_hom,
          ← whiskerLeft_comp_assoc, leg_comp] }

/-- The original cone with each leg preceded by its right action. -/
@[reducible] def rightCone : Cone (F ⋙ forget (B := B) A) where
  pt := c.pt ⊗ B.X
  π :=
    { app := fun j => (leg F c j ▷ B.X) ≫ (F.obj j).actRight
      naturality := fun j k f => by
        change 𝟙 (c.pt ⊗ B.X) ≫ (leg F c k ▷ B.X) ≫ (F.obj k).actRight =
          ((leg F c j ▷ B.X) ≫ (F.obj j).actRight) ≫ (F.map f).hom
        rw [Category.id_comp, Category.assoc, (F.map f).right_act_hom,
          ← comp_whiskerRight_assoc, leg_comp] }

/-- The left action constructed on the supplied limit point. -/
@[reducible] def leftAction : A.X ⊗ c.pt ⟶ c.pt := h.lift (leftCone F c)

/-- The right action constructed on that same supplied limit point. -/
@[reducible] def rightAction : c.pt ⊗ B.X ⟶ c.pt := h.lift (rightCone F c)

/-- Each original limit leg commutes with the constructed left action. -/
theorem leftAction_fac (j : J) :
    leftAction F c h ≫ leg F c j = (A.X ◁ leg F c j) ≫ (F.obj j).actLeft :=
  h.fac (leftCone F c) j

/-- Each original limit leg commutes with the constructed right action. -/
theorem rightAction_fac (j : J) :
    rightAction F c h ≫ leg F c j = (leg F c j ▷ B.X) ≫ (F.obj j).actRight :=
  h.fac (rightCone F c) j

/-- The actual original limit point, equipped with both commuting actions. -/
@[reducible] def conePoint : Bimod A B where
  X := c.pt
  actLeft := leftAction F c h
  actRight := rightAction F c h
  one_actLeft := by
    apply h.hom_ext
    intro j
    change (η[A.X] ▷ c.pt ≫ leftAction F c h) ≫ leg F c j = (λ_ c.pt).hom ≫ leg F c j
    rw [Category.assoc, leftAction_fac, ← whisker_exchange_assoc,
      (F.obj j).one_actLeft, leftUnitor_naturality]
  left_assoc := by
    apply h.hom_ext
    intro j
    change (μ[A.X] ▷ c.pt ≫ leftAction F c h) ≫ leg F c j =
      ((α_ A.X A.X c.pt).hom ≫ A.X ◁ leftAction F c h ≫ leftAction F c h) ≫ leg F c j
    simp only [Category.assoc, leftAction_fac]
    rw [← whisker_exchange_assoc, (F.obj j).left_assoc]
    rw [associator_naturality_right_assoc]
    rw [← whiskerLeft_comp_assoc, ← leftAction_fac F c h j, whiskerLeft_comp_assoc]
    rw [leftAction_fac F c h j]
  actRight_one := by
    apply h.hom_ext
    intro j
    change (c.pt ◁ η[B.X] ≫ rightAction F c h) ≫ leg F c j = (ρ_ c.pt).hom ≫ leg F c j
    rw [Category.assoc, rightAction_fac, whisker_exchange_assoc,
      (F.obj j).actRight_one, rightUnitor_naturality]
  right_assoc := by
    apply h.hom_ext
    intro j
    change (c.pt ◁ μ[B.X] ≫ rightAction F c h) ≫ leg F c j =
      ((α_ c.pt B.X B.X).inv ≫ rightAction F c h ▷ B.X ≫ rightAction F c h) ≫ leg F c j
    simp only [Category.assoc, rightAction_fac]
    rw [whisker_exchange_assoc, (F.obj j).right_assoc]
    rw [associator_inv_naturality_left_assoc]
    rw [← comp_whiskerRight_assoc, ← rightAction_fac F c h j, comp_whiskerRight_assoc]
    rw [rightAction_fac F c h j]
  middle_assoc := by
    apply h.hom_ext
    intro j
    change (leftAction F c h ▷ B.X ≫ rightAction F c h) ≫ leg F c j =
      ((α_ A.X c.pt B.X).hom ≫ A.X ◁ rightAction F c h ≫ leftAction F c h) ≫ leg F c j
    simp only [Category.assoc, leftAction_fac, rightAction_fac]
    rw [← comp_whiskerRight_assoc, leftAction_fac, comp_whiskerRight_assoc,
      (F.obj j).middle_assoc, associator_naturality_middle_assoc]
    rw [← whiskerLeft_comp_assoc, ← rightAction_fac F c h j, whiskerLeft_comp_assoc]

/-- Lift the supplied cone, retaining its point and its complete family of legs. -/
@[reducible] def liftedCone : Cone F where
  pt := conePoint F c h
  π :=
    { app := fun j =>
        { hom := leg F c j
          left_act_hom := leftAction_fac F c h j
          right_act_hom := rightAction_fac F c h j }
      naturality := fun j k f => by
        apply hom_ext
        exact c.π.naturality f }

/-- The universal underlying map into the original limit point, with explicit carriers. -/
def liftedMap (s : Cone F) : s.pt.X ⟶ c.pt := h.lift ((forget (B := B) A).mapCone s)

/-- The universal map retains every original leg. -/
theorem liftedMap_fac (s : Cone F) (j : J) :
    liftedMap F c h s ≫ leg F c j = (s.π.app j).hom :=
  h.fac ((forget (B := B) A).mapCone s) j

/-- The lifted cone is limiting in the existing bimodule category. -/
def liftedConeIsLimit : IsLimit (liftedCone F c h) where
  lift s :=
    { hom := liftedMap F c h s
      left_act_hom := by
        apply h.hom_ext
        intro j
        change (s.pt.actLeft ≫ liftedMap F c h s) ≫ leg F c j =
          (A.X ◁ liftedMap F c h s ≫ leftAction F c h) ≫ leg F c j
        simp only [Category.assoc, leftAction_fac]
        rw [liftedMap_fac, ← whiskerLeft_comp_assoc, liftedMap_fac]
        exact (s.π.app j).left_act_hom
      right_act_hom := by
        apply h.hom_ext
        intro j
        change (s.pt.actRight ≫ liftedMap F c h s) ≫ leg F c j =
          (liftedMap F c h s ▷ B.X ≫ rightAction F c h) ≫ leg F c j
        simp only [Category.assoc, rightAction_fac]
        rw [liftedMap_fac, ← comp_whiskerRight_assoc, liftedMap_fac]
        exact (s.π.app j).right_act_hom }
  fac s j := by
    apply hom_ext
    exact liftedMap_fac F c h s j
  uniq s m hm := by
    apply hom_ext
    apply h.hom_ext
    intro j
    change m.hom ≫ leg F c j = liftedMap F c h s ≫ leg F c j
    rw [liftedMap_fac]
    exact congrArg Hom.hom (hm j)

end ForgetCreatesLimits

variable (A B) {J : Type uJ} [Category.{vJ} J]

/-- Forgetting creates a limit on exactly the underlying supplied cone. -/
noncomputable instance forgetCreatesLimit (F : J ⥤ Bimod A B) :
    CreatesLimit F (forget (B := B) A) :=
  createsLimitOfReflectsIso fun c h =>
    { liftedCone := ForgetCreatesLimits.liftedCone F c h
      validLift := Cone.ext (Iso.refl _) fun _ => by
        simp [ForgetCreatesLimits.liftedCone, ForgetCreatesLimits.leg, forget]
      makesLimit := ForgetCreatesLimits.liftedConeIsLimit F c h }

noncomputable instance forgetCreatesLimitsOfShape : CreatesLimitsOfShape J (forget (B := B) A) where
  CreatesLimit := inferInstance

noncomputable instance forgetCreatesLimitsOfSize :
    CreatesLimitsOfSize.{vJ, uJ} (forget (B := B) A) where
  CreatesLimitsOfShape := inferInstance

/-- Existing bimodules have every limit supplied by the ambient category. -/
theorem hasLimits [HasLimitsOfSize.{vJ, uJ} C] : HasLimitsOfSize.{vJ, uJ} (Bimod A B) :=
  hasLimits_of_hasLimits_createsLimits (forget (B := B) A)

namespace ForgetCreatesColimits

variable {A B} (F : J ⥤ Bimod A B) (c : Cocone (F ⋙ forget (B := B) A)) (h : IsColimit c)
  [PreservesColimitsOfShape J (tensorLeft A.X)]
  [PreservesColimitsOfShape J (tensorRight B.X)]

/-- The supplied colimit leg with its actual bimodule carrier made explicit. -/
def leg (j : J) : (F.obj j).X ⟶ c.pt := c.ι.app j

omit [PreservesColimitsOfShape J (tensorLeft A.X)] [PreservesColimitsOfShape J (tensorRight B.X)] in
/-- The entire original cocone naturality equation on the actual carriers. -/
theorem comp_leg {j k : J} (f : j ⟶ k) :
    (F.map f).hom ≫ leg F c k = leg F c j := c.w f

/-- The supplied cocone following each original left action. -/
@[reducible] def leftCocone : Cocone ((F ⋙ forget (B := B) A) ⋙ tensorLeft A.X) where
  pt := c.pt
  ι :=
    { app := fun j => (F.obj j).actLeft ≫ leg F c j
      naturality := fun j k f => by
        change A.X ◁ (F.map f).hom ≫ (F.obj k).actLeft ≫ leg F c k =
          ((F.obj j).actLeft ≫ leg F c j) ≫ 𝟙 c.pt
        rw [Category.comp_id, ← (F.map f).left_act_hom_assoc, comp_leg] }

/-- The supplied cocone following each original right action. -/
@[reducible] def rightCocone : Cocone ((F ⋙ forget (B := B) A) ⋙ tensorRight B.X) where
  pt := c.pt
  ι :=
    { app := fun j => (F.obj j).actRight ≫ leg F c j
      naturality := fun j k f => by
        change (F.map f).hom ▷ B.X ≫ (F.obj k).actRight ≫ leg F c k =
          ((F.obj j).actRight ≫ leg F c j) ≫ 𝟙 c.pt
        rw [Category.comp_id, ← (F.map f).right_act_hom_assoc, comp_leg] }

/-- The left action on exactly the supplied colimit point. -/
def leftAction : A.X ⊗ c.pt ⟶ c.pt :=
  (isColimitOfPreserves (tensorLeft A.X) h).desc (leftCocone F c)

/-- The right action on exactly that same supplied colimit point. -/
def rightAction : c.pt ⊗ B.X ⟶ c.pt :=
  (isColimitOfPreserves (tensorRight B.X) h).desc (rightCocone F c)

omit [PreservesColimitsOfShape J (tensorRight B.X)] in
/-- Each original colimit leg commutes with the constructed left action. -/
theorem leftAction_fac (j : J) :
    (A.X ◁ leg F c j) ≫ leftAction F c h = (F.obj j).actLeft ≫ leg F c j :=
  (isColimitOfPreserves (tensorLeft A.X) h).fac (leftCocone F c) j

omit [PreservesColimitsOfShape J (tensorLeft A.X)] in
/-- Each original colimit leg commutes with the constructed right action. -/
theorem rightAction_fac (j : J) :
    (leg F c j ▷ B.X) ≫ rightAction F c h = (F.obj j).actRight ≫ leg F c j :=
  (isColimitOfPreserves (tensorRight B.X) h).fac (rightCocone F c) j

/-- The original colimit point with its two derived commuting actions. -/
@[reducible] def coconePoint : Bimod A B where
  X := c.pt
  actLeft := leftAction F c h
  actRight := rightAction F c h
  one_actLeft := by
    rw [← cancel_epi (λ_ c.pt).inv]
    apply h.hom_ext
    intro j
    change leg F c j ≫ (λ_ c.pt).inv ≫ η[A.X] ▷ c.pt ≫ leftAction F c h =
      leg F c j ≫ (λ_ c.pt).inv ≫ (λ_ c.pt).hom
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
      leftAction_fac, (F.obj j).one_actLeft_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  left_assoc := by
    rw [← cancel_epi (α_ A.X A.X c.pt).inv]
    apply (isColimitOfPreserves (tensorLeft A.X) (isColimitOfPreserves (tensorLeft A.X) h)).hom_ext
    intro j
    change A.X ◁ (A.X ◁ leg F c j) ≫ (α_ A.X A.X c.pt).inv ≫ μ[A.X] ▷ c.pt ≫ leftAction F c h =
      A.X ◁ (A.X ◁ leg F c j) ≫ (α_ A.X A.X c.pt).inv ≫
        (α_ A.X A.X c.pt).hom ≫ A.X ◁ leftAction F c h ≫ leftAction F c h
    rw [Iso.inv_hom_id_assoc, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      leftAction_fac, (F.obj j).left_assoc_assoc, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, leftAction_fac, whiskerLeft_comp_assoc, leftAction_fac]
  actRight_one := by
    rw [← cancel_epi (ρ_ c.pt).inv]
    apply h.hom_ext
    intro j
    change leg F c j ≫ (ρ_ c.pt).inv ≫ c.pt ◁ η[B.X] ≫ rightAction F c h =
      leg F c j ≫ (ρ_ c.pt).inv ≫ (ρ_ c.pt).hom
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      rightAction_fac, (F.obj j).actRight_one_assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  right_assoc := by
    rw [← cancel_epi (α_ c.pt B.X B.X).hom]
    apply (isColimitOfPreserves (tensorRight B.X)
      (isColimitOfPreserves (tensorRight B.X) h)).hom_ext
    intro j
    change (leg F c j ▷ B.X) ▷ B.X ≫ (α_ c.pt B.X B.X).hom ≫ c.pt ◁ μ[B.X] ≫ rightAction F c h =
      (leg F c j ▷ B.X) ▷ B.X ≫ (α_ c.pt B.X B.X).hom ≫
        (α_ c.pt B.X B.X).inv ≫ rightAction F c h ▷ B.X ≫ rightAction F c h
    rw [Iso.hom_inv_id_assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc,
      rightAction_fac, (F.obj j).right_assoc_assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, rightAction_fac, comp_whiskerRight_assoc, rightAction_fac]
  middle_assoc := by
    apply (isColimitOfPreserves (tensorRight B.X) (isColimitOfPreserves (tensorLeft A.X) h)).hom_ext
    intro j
    change (A.X ◁ leg F c j) ▷ B.X ≫ leftAction F c h ▷ B.X ≫ rightAction F c h =
      (A.X ◁ leg F c j) ▷ B.X ≫ (α_ A.X c.pt B.X).hom ≫
        A.X ◁ rightAction F c h ≫ leftAction F c h
    rw [← comp_whiskerRight_assoc, leftAction_fac, comp_whiskerRight_assoc,
      rightAction_fac, (F.obj j).middle_assoc_assoc, associator_naturality_middle_assoc]
    rw [← whiskerLeft_comp_assoc, rightAction_fac, whiskerLeft_comp_assoc, leftAction_fac]

/-- Lift the supplied cocone without changing its point or any leg. -/
@[reducible] def liftedCocone : Cocone F where
  pt := coconePoint F c h
  ι :=
    { app := fun j =>
        { hom := leg F c j
          left_act_hom := (leftAction_fac F c h j).symm
          right_act_hom := (rightAction_fac F c h j).symm }
      naturality := fun j k f => by
        apply hom_ext
        exact c.ι.naturality f }

/-- The universal underlying map from the same original colimit point. -/
def liftedMap (s : Cocone F) : c.pt ⟶ s.pt.X := h.desc ((forget (B := B) A).mapCocone s)

omit [PreservesColimitsOfShape J (tensorLeft A.X)] [PreservesColimitsOfShape J (tensorRight B.X)] in
/-- The universal map keeps the supplied colimit legs. -/
theorem liftedMap_fac (s : Cocone F) (j : J) :
    leg F c j ≫ liftedMap F c h s = (s.ι.app j).hom :=
  h.fac ((forget (B := B) A).mapCocone s) j

/-- The lifted cocone is colimiting in the existing bimodule category. -/
def liftedCoconeIsColimit : IsColimit (liftedCocone F c h) where
  desc s :=
    { hom := liftedMap F c h s
      left_act_hom := by
        apply (isColimitOfPreserves (tensorLeft A.X) h).hom_ext
        intro j
        change A.X ◁ leg F c j ≫ leftAction F c h ≫ liftedMap F c h s =
          A.X ◁ leg F c j ≫ A.X ◁ liftedMap F c h s ≫ s.pt.actLeft
        rw [← Category.assoc, leftAction_fac, Category.assoc, liftedMap_fac,
          ← whiskerLeft_comp_assoc, liftedMap_fac]
        exact (s.ι.app j).left_act_hom
      right_act_hom := by
        apply (isColimitOfPreserves (tensorRight B.X) h).hom_ext
        intro j
        change leg F c j ▷ B.X ≫ rightAction F c h ≫ liftedMap F c h s =
          leg F c j ▷ B.X ≫ liftedMap F c h s ▷ B.X ≫ s.pt.actRight
        rw [← Category.assoc, rightAction_fac, Category.assoc, liftedMap_fac,
          ← comp_whiskerRight_assoc, liftedMap_fac]
        exact (s.ι.app j).right_act_hom }
  fac s j := by
    apply hom_ext
    exact liftedMap_fac F c h s j
  uniq s m hm := by
    apply hom_ext
    apply h.hom_ext
    intro j
    change leg F c j ≫ m.hom = leg F c j ≫ liftedMap F c h s
    rw [liftedMap_fac]
    exact congrArg Hom.hom (hm j)

end ForgetCreatesColimits

/-- Forgetting creates colimits when the two original coefficient tensors preserve the shape. -/
noncomputable instance forgetCreatesColimit (F : J ⥤ Bimod A B)
    [PreservesColimitsOfShape J (tensorLeft A.X)] [PreservesColimitsOfShape J (tensorRight B.X)] :
    CreatesColimit F (forget (B := B) A) :=
  createsColimitOfReflectsIso fun c h =>
    { liftedCocone := ForgetCreatesColimits.liftedCocone F c h
      validLift := Cocone.ext (Iso.refl _) fun _ => by
        simp [ForgetCreatesColimits.liftedCocone, ForgetCreatesColimits.leg, forget]
      makesColimit := ForgetCreatesColimits.liftedCoconeIsColimit F c h }

noncomputable instance forgetCreatesColimitsOfShape
    [PreservesColimitsOfShape J (tensorLeft A.X)] [PreservesColimitsOfShape J (tensorRight B.X)] :
    CreatesColimitsOfShape J (forget (B := B) A) where
  CreatesColimit := inferInstance

noncomputable instance forgetCreatesColimitsOfSize
    [PreservesColimitsOfSize.{vJ, uJ} (tensorLeft A.X)]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorRight B.X)] :
    CreatesColimitsOfSize.{vJ, uJ} (forget (B := B) A) where
  CreatesColimitsOfShape := inferInstance

/-- Existing bimodules have all colimits preserved by the two original coefficient tensors. -/
theorem hasColimits [HasColimitsOfSize.{vJ, uJ} C]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorLeft A.X)]
    [PreservesColimitsOfSize.{vJ, uJ} (tensorRight B.X)] :
    HasColimitsOfSize.{vJ, uJ} (Bimod A B) :=
  hasColimits_of_hasColimits_createsColimits (forget (B := B) A)

end Bimod
