/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.FunctorPresentability
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeColimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Relative compactness of an actual whole under-functor

The native under evaluation and every original structure action retain the
original diagram and root transformation. A whole under-Hom functor is the
actual limit of all relative component equations. Source compactness stays
relative; no underlying coefficient compactness or under-category LP is input.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD uC vC

namespace CategoryTheory.Presentable.UnderFunctorPresentability

open Limits Opposite

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C] (F : D ⥤ C)

/-- The original native relative component evaluation at the actual index object. -/
abbrev relativeEvaluation (d : D) : Under F ⥤ Under (F.obj d) :=
  Under.post ((evaluation D C).obj d)

/-- Every original object keeps its actual coefficient and component root. -/
theorem relativeEvaluation_object_function (d : D) :
    (fun V : Under F => (relativeEvaluation F d).obj V) =
      (fun V : Under F => Under.mk (V.hom.app d)) := rfl

/-- Every whole under-morphism keeps its actual original component function. -/
theorem relativeEvaluation_map_right_function (d : D) :
    (fun (V W : Under F) (a : V ⟶ W) => ((relativeEvaluation F d).map a).right) =
      (fun (V W : Under F) (a : V ⟶ W) => a.right.app d) := rfl

/-- The native postMap uses the original evaluation action, including its root naturality. -/
abbrev structureAction {d e : D} (g : d ⟶ e) :
    relativeEvaluation F d ⟶ relativeEvaluation F e ⋙ Under.map (F.map g) :=
  Under.postMap ((evaluation D C).map g)

/-- The entire original structure map function is the original diagram action. -/
theorem structureAction_right_function {d e : D} (g : d ⟶ e) :
    (fun V : Under F => ((structureAction F g).app V).right) =
      (fun V : Under F => V.right.map g) := rfl

/-- Genuine working-size coefficient colimits make relative evaluation accessible. -/
instance relativeEvaluation_cardinalAccessible [HasColimitsOfSize.{w, w} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] (d : D) :
    (relativeEvaluation F d).IsCardinalAccessible chi where
  preservesColimitOfShape J _ _ := by
    let : IsFiltered J := isFiltered_of_isCardinalFiltered J chi
    let : IsConnected J := IsFiltered.isConnected J
    let : HasColimitsOfShape J C := inferInstance
    exact
      { preservesColimit := fun {K} => by
          let : PreservesColimit K (relativeEvaluation F d ⋙ Under.forget (F.obj d)) := by
            change PreservesColimit K (Under.forget F ⋙ (evaluation D C).obj d)
            infer_instance
          exact preservesColimit_of_reflects_of_preserves
            (relativeEvaluation F d) (Under.forget (F.obj d)) }

/-- The relative component-Hom equations use every actual original Arrow D label. -/
@[implicit_reducible]
def equationIndex (U : Under F) :
    MulticospanIndex (multicospanShapeEnd D) (Under F ⥤ Type (max uD vD vC)) where
  left d := relativeEvaluation F d ⋙
    uliftCoyoneda.{max uD vD}.obj (op ((relativeEvaluation F d).obj U))
  right g := relativeEvaluation F g.right ⋙ Under.map (F.map g.hom) ⋙
    uliftCoyoneda.{max uD vD}.obj (op ((relativeEvaluation F g.left).obj U))
  fst g :=
    { app V := ↾fun a => ULift.up (a.down ≫ (structureAction F g.hom).app V)
      naturality := by
        intro V W a
        ext h
        let t : (relativeEvaluation F g.left).obj U ⟶
            (relativeEvaluation F g.left).obj V := h.down
        change ULift.up ((t ≫ (relativeEvaluation F g.left).map a) ≫
            (structureAction F g.hom).app W) =
          ULift.up ((t ≫ (structureAction F g.hom).app V) ≫
            (Under.map (F.map g.hom)).map ((relativeEvaluation F g.right).map a))
        congr 1
        rw [Category.assoc, Category.assoc, (structureAction F g.hom).naturality a]
        rfl }
  snd g :=
    { app V := ↾fun a => ULift.up
        ((structureAction F g.hom).app U ≫ (Under.map (F.map g.hom)).map a.down)
      naturality := by
        intro V W a
        ext h
        let t : (relativeEvaluation F g.right).obj U ⟶
            (relativeEvaluation F g.right).obj V := h.down
        change ULift.up ((structureAction F g.hom).app U ≫
            (Under.map (F.map g.hom)).map (t ≫ (relativeEvaluation F g.right).map a)) =
          ULift.up (((structureAction F g.hom).app U ≫
            (Under.map (F.map g.hom)).map t) ≫
              (Under.map (F.map g.hom)).map ((relativeEvaluation F g.right).map a))
        congr 1
        simp only [Functor.map_comp, Category.assoc] }

/-- The projection preserves each complete original under-component morphism. -/
def componentProjection (U : Under F) (d : D) :
    uliftCoyoneda.{max uD vD}.obj (op U) ⟶ (equationIndex F U).left d where
  app V := ↾fun a => ULift.up ((relativeEvaluation F d).map a.down)
  naturality := by
    intro V W a
    ext h
    change ULift.up ((relativeEvaluation F d).map (h.down ≫ a)) =
      ULift.up ((relativeEvaluation F d).map h.down ≫ (relativeEvaluation F d).map a)
    rw [Functor.map_comp]

/-- Every actual whole under-morphism gives the native multifork of its original components. -/
def componentCone (U : Under F) : Multifork (equationIndex F U) :=
  Multifork.ofι _ (uliftCoyoneda.{max uD vD}.obj (op U))
    (componentProjection F U) (by
      intro g
      ext V a
      change ULift.up ((relativeEvaluation F g.left).map a.down ≫
          (structureAction F g.hom).app V) =
        ULift.up ((structureAction F g.hom).app U ≫
          (Under.map (F.map g.hom)).map ((relativeEvaluation F g.right).map a.down))
      congr 1
      exact (structureAction F g.hom).naturality a.down)

/-- Reconstruct the genuine whole under-morphism from the ACTUAL native equation condition. -/
def componentLiftMorphism (U : Under F) (T : Multifork (equationIndex F U))
    (V : Under F) (x : T.pt.obj V) : U ⟶ V :=
  Under.homMk
    { app d := (((T.ι d).app V) x).down.right
      naturality := by
        intro d e g
        have h := NatTrans.congr_app (T.condition (Arrow.mk g)) V
        have hx := congrArg ULift.down (ConcreteCategory.congr_hom h x)
        exact (congrArg Under.Hom.right hx).symm }
    (by
      apply NatTrans.ext
      funext d
      exact Under.w ((((T.ι d).app V) x).down))

/-- Every original component function is literally the multifork's original projection. -/
theorem componentLiftMorphism_right_app (U : Under F)
    (T : Multifork (equationIndex F U)) (V : Under F) (x : T.pt.obj V) (d : D) :
    (componentLiftMorphism F U T V x).right.app d = (((T.ι d).app V) x).down.right := rfl

/-- Its whole root compatibility is the actual pointwise under-morphism root equation. -/
theorem componentLiftMorphism_root (U : Under F)
    (T : Multifork (equationIndex F U)) (V : Under F) (x : T.pt.obj V) :
    U.hom ≫ (componentLiftMorphism F U T V x).right = V.hom :=
  Under.w (componentLiftMorphism F U T V x)

/-- The whole original lift is natural on every whole original under-morphism. -/
def componentLift (U : Under F) (T : Multifork (equationIndex F U)) :
    T.pt ⟶ (componentCone F U).pt where
  app V := ↾fun x => ULift.up (componentLiftMorphism F U T V x)
  naturality := by
    intro V W a
    apply ConcreteCategory.hom_ext
    intro x
    apply congrArg ULift.up
    apply Under.UnderMorphism.ext
    apply NatTrans.ext
    funext d
    have h := (T.ι d).naturality a
    have hx := congrArg ULift.down (ConcreteCategory.congr_hom h x)
    exact congrArg Under.Hom.right hx

/-- The actual whole under-Hom functor is the limit of all original relative equations. -/
def componentConeIsLimit (U : Under F) : IsLimit (componentCone F U) :=
  Multifork.IsLimit.mk _ (componentLift F U)
    (by
      intro T d
      ext V x
      apply ULift.ext
      apply Under.UnderMorphism.ext
      rfl)
    (by
      intro T m hm
      apply NatTrans.ext
      funext V
      apply ConcreteCategory.hom_ext
      intro x
      apply ULift.ext
      apply Under.UnderMorphism.ext
      apply NatTrans.ext
      funext d
      have h := NatTrans.congr_app (hm d) V
      have hx := congrArg ULift.down (ConcreteCategory.congr_hom h x)
      exact congrArg Under.Hom.right hx)

/-- The actual native universal lift is the whole original component reconstruction. -/
theorem componentConeIsLimit_lift (U : Under F) (T : Multifork (equationIndex F U)) :
    (componentConeIsLimit F U).lift T = componentLift F U T := rfl

/-- Relative component compactness gives compactness of the SAME whole original Under F object. -/
theorem relative_diagram_presentable [HasColimitsOfSize.{w, w} C]
    (chi : Cardinal.{w}) [Fact chi.IsRegular] (hArrow : HasCardinalLT (Arrow D) chi)
    (U : Under F)
    (hU : ∀ d, IsCardinalPresentable (Under.mk (U.hom.app d)) chi) :
    IsCardinalPresentable U chi := by
  let (d : D) : IsCardinalPresentable ((relativeEvaluation F d).obj U) chi := hU d
  have hLeft (d : D) : ((equationIndex F U).left d).IsCardinalAccessible chi :=
    inferInstanceAs ((relativeEvaluation F d ⋙
      uliftCoyoneda.{max uD vD}.obj (op ((relativeEvaluation F d).obj U))).IsCardinalAccessible chi)
  have hRight (g : Arrow D) : ((equationIndex F U).right g).IsCardinalAccessible chi := by
    let : (Under.map (F.map g.hom)).IsCardinalAccessible chi :=
      SmallObject.RootChangeColimits.cardinalAccessible (F.map g.hom) chi
    exact inferInstanceAs ((relativeEvaluation F g.right ⋙ Under.map (F.map g.hom) ⋙
      uliftCoyoneda.{max uD vD}.obj (op ((relativeEvaluation F g.left).obj U))).IsCardinalAccessible
        chi)
  let (k : WalkingMulticospan (multicospanShapeEnd D)) :
      ((equationIndex F U).multicospan.obj k).IsCardinalAccessible chi := by
    cases k with
    | left d => exact hLeft d
    | right g => exact hRight g
  have h := Functor.isCardinalAccessible_of_isLimit (componentCone F U)
    (componentConeIsLimit F U) chi (FunctorPresentability.endShapeArrow_bound chi hArrow)
  exact (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{max uD vD} U chi).2 h

end CategoryTheory.Presentable.UnderFunctorPresentability
