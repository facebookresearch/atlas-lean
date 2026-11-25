/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.UnderColimits
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Original root-change connected colimits

The same native Under.map keeps every original right object and function.
Its actual composite with forget creates the needed connected-colimit
comparison. Fixed-cardinal accessibility and mapped native presentations
retain the original root arrow, without a compactness premise on roots.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w v u vJ uJ

namespace CategoryTheory.SmallObject.RootChangeColimits

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y : C} (ρ : X ⟶ Y)

/-- The ORIGINAL root-change functor preserves every connected diagram colimit. -/
instance preservesConnected {J : Type uJ} [Category.{vJ} J] [IsConnected J] :
    PreservesColimitsOfShape J (Under.map ρ) where
  preservesColimit {F} := by
    let : PreservesColimit F (Under.map ρ ⋙ Under.forget X) := by
      rw [Under.mapForget_eq]
      infer_instance
    exact preservesColimit_of_reflects_of_preserves (Under.map ρ) (Under.forget X)

/-- The original connected diagram is reflected through the same target forgetful functor. -/
instance reflectsConnected {J : Type uJ} [Category.{vJ} J] [IsConnected J] :
    ReflectsColimitsOfShape J (Under.map ρ) where
  reflectsColimit {F} := by
    refine ⟨?_⟩
    intro c hc
    refine ⟨?_⟩
    have h := isColimitOfPreserves (Under.forget X) hc
    change IsColimit ((Under.forget Y).mapCocone c) at h
    exact isColimitOfReflects (Under.forget Y) h

/-- The SAME original root arrow induces an accessible functor at this exact regular rank. -/
instance cardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (Under.map ρ).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    let : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
    let : IsConnected J := IsFiltered.isConnected J
    infer_instance

section Cocone

variable {J : Type uJ} [Category.{vJ} J] [IsConnected J] {F : J ⥤ Under Y}

/-- The actual given cocone is mapped by the same native root-change functor. -/
abbrev mappedCocone (c : Cocone F) : Cocone (F ⋙ Under.map ρ) :=
  (Under.map ρ).mapCocone c

/-- The chosen connected colimit, with the same point and every native mapped leg. -/
abbrev mappedColimit (c : ColimitCocone F) : ColimitCocone (F ⋙ Under.map ρ) where
  cocone := mappedCocone ρ c.cocone
  isColimit := isColimitOfPreserves (Under.map ρ) c.isColimit

/-- Connected root change both preserves and reflects the actual given universal property. -/
theorem mappedCocone_isColimit_iff (c : Cocone F) :
    Nonempty (IsColimit (mappedCocone ρ c)) ↔ Nonempty (IsColimit c) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨isColimitOfReflects (Under.map ρ) h⟩
  · rintro ⟨h⟩
    exact ⟨isColimitOfPreserves (Under.map ρ) h⟩

/-- The actual preserved colimit's descender, with its original selected point. -/
abbrev desc (c : ColimitCocone F) (s : Cocone (F ⋙ Under.map ρ)) :
    (Under.map ρ).obj c.cocone.pt ⟶ s.pt :=
  (mappedColimit ρ c).isColimit.desc s

/-- Its underlying descender retains the actual original root equation. -/
theorem desc_root (c : ColimitCocone F) (s : Cocone (F ⋙ Under.map ρ)) :
    (ρ ≫ c.cocone.pt.hom) ≫ (desc ρ c s).right = s.pt.hom :=
  Under.w (desc ρ c s)

/-- Every original right leg factors through the same actual descender. -/
@[reassoc]
theorem desc_leg_right (c : ColimitCocone F) (s : Cocone (F ⋙ Under.map ρ)) (j : J) :
    (c.cocone.ι.app j).right ≫ (desc ρ c s).right = (s.ι.app j).right :=
  congrArg Under.Hom.right ((mappedColimit ρ c).isColimit.fac s j)

/-- The original root-compatible right map is uniquely detected by all original legs. -/
theorem desc_right_unique (c : ColimitCocone F) (s : Cocone (F ⋙ Under.map ρ))
    (m : c.cocone.pt.right ⟶ s.pt.right)
    (hRoot : (ρ ≫ c.cocone.pt.hom) ≫ m = s.pt.hom)
    (hLeg : ∀ j, (c.cocone.ι.app j).right ≫ m = (s.ι.app j).right) :
    m = (desc ρ c s).right := by
  let p : (Under.map ρ).obj c.cocone.pt ⟶ s.pt := Under.homMk m hRoot
  have h : p = desc ρ c s := (mappedColimit ρ c).isColimit.uniq s p (fun j =>
    Under.UnderMorphism.ext (hLeg j))
  exact congrArg Under.Hom.right h

end Cocone

section Presentation

variable {J : Type uJ} [Category.{vJ} J] [IsConnected J]
  {E : Under Y} (p : ColimitPresentation J E)

/-- Map the GIVEN original colimit presentation with the same native root-change functor. -/
def mappedPresentation : ColimitPresentation J ((Under.map ρ).obj E) :=
  p.map (Under.map ρ)

@[simp]
theorem mappedPresentation_diag :
    (mappedPresentation ρ p).diag = p.diag ⋙ Under.map ρ := rfl

/-- The native mapped presentation has the same complete original diagram-object function. -/
theorem mappedPresentation_object_right_function :
    (fun j => ((mappedPresentation ρ p).diag.obj j).right) =
      (fun j => (p.diag.obj j).right) := rfl

/-- Its actual piece roots are precisely the original root-change composites. -/
theorem mappedPresentation_object_root_function :
    (fun j => ((mappedPresentation ρ p).diag.obj j).hom) =
      (fun j => ρ ≫ (p.diag.obj j).hom) := rfl

/-- The entire original diagram-map function is retained, with all source and target objects. -/
theorem mappedPresentation_map_right_function :
    (fun (i j : J) (f : i ⟶ j) => ((mappedPresentation ρ p).diag.map f).right) =
      (fun (i j : J) (f : i ⟶ j) => (p.diag.map f).right) := rfl

/-- Each original leg right function survives the native presentation mapping. -/
theorem mappedPresentation_leg_right (j : J) :
    ((mappedPresentation ρ p).ι.app j).right = (p.ι.app j).right := by
  change ((Under.map ρ).map (p.ι.app j) ≫ 𝟙 _).right = (p.ι.app j).right
  rw [Category.comp_id, Under.map_map_right]

/-- The ENTIRE original leg-right FUNCTION remains the original given function. -/
theorem mappedPresentation_leg_right_function :
    (fun j => ((mappedPresentation ρ p).ι.app j).right) =
      (fun j => (p.ι.app j).right) := by
  funext j
  exact mappedPresentation_leg_right ρ p j

end Presentation

theorem compositionIso_hom_right {Z : C} (σ : Y ⟶ Z) (U : Under Z) :
    ((Under.mapComp ρ σ).hom.app U).right = 𝟙 U.right := by
  simp only [Under.mapComp, eqToIso.hom, eqToHom_app,
    Under.eqToHom_right, eqToHom_refl, Under.map_obj_right]

theorem compositionIso_inv_right {Z : C} (σ : Y ⟶ Z) (U : Under Z) :
    ((Under.mapComp ρ σ).inv.app U).right = 𝟙 U.right := by
  simp only [Under.mapComp, eqToIso.inv, eqToHom_app,
    Under.eqToHom_right, eqToHom_refl, Functor.comp_obj, Under.map_obj_right]

/-- Original composite roots agree by the actual associativity equation. -/
theorem composition_root_function {Z : C} (σ : Y ⟶ Z) :
    (fun U : Under Z => ((Under.map (ρ ≫ σ)).obj U).hom) =
      (fun U : Under Z => ((Under.map ρ).obj ((Under.map σ).obj U)).hom) := by
  funext U
  exact Category.assoc ρ σ U.hom

end CategoryTheory.SmallObject.RootChangeColimits
