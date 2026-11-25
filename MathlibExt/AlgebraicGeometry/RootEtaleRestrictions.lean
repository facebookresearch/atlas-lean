/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DenominatorRootStacks
public import MathlibExt.AlgebraicGeometry.CartesianStackModules
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Literal étale restriction of a root stack and its cartesian modules

The restricted pseudofunctor is the native composition with Over.map.
Every affine point retains its actual parameter scheme, ring and fibre
object. Module restriction is literal precomposition along this view;
there is no independent purported coefficient restriction functor.

Generic stack restriction/descent is public source integration. The
root-specific fibre dictionary and the parabolic assembly are separate
normalized construction requests.

Source: Borne–Vistoli arXiv:1001.0466v2, Section4.3 and Theorem6.1.
Native pseudofunctor composition and module precomposition are Mathlib;
the cartesian source adapters retain AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b attribution.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootEtaleRestrictions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackFibreModels _root_.AlgebraicGeometry.StackAffineModules
open _root_.AlgebraicGeometry.CartesianStackModules

variable {X Y : Scheme.{0}} (b : Y ⟶ X) (R : RelativeStack X)

def pseudofunctor : Pseudofunctor (LocallyDiscrete (Over Y)ᵒᵖ) Cat.{0,1} :=
  Pseudofunctor.comp ((Over.map b).op.toPseudofunctor) R.toPseudofunctor

variable [(pseudofunctor b R).IsStack (Scheme.fppfTopology.over Y)]

def stack : RelativeStack Y :=
  ⟨pseudofunctor b R, fun T ↦ R.isGroupoid ((Over.map b).obj T), inferInstance⟩

/-- The entire view is the native change of the parameter base. -/
def totalView : Total (stack b R) ⥤ Total R where
  obj a := ⟨(Over.map b).obj a.base, a.fiber⟩
  map h := ⟨(Over.map b).map h.base, h.fiber⟩
  map_id a := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl)
    simp [pseudofunctor, stack, Pseudofunctor.comp, Functor.toPseudofunctor,
      Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, PrelaxFunctor.map₂_eqToHom]
    change (R.toPseudofunctor.mapId (.mk (op ((Over.map b).obj a.base)))).inv.toNatTrans.app a.fiber ≫ 𝟙 _ = _
    simp
  map_comp h k := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl)
    simp [pseudofunctor, stack, Pseudofunctor.comp, Functor.toPseudofunctor,
      Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber, PrelaxFunctor.map₂_eqToHom]
    change h.fiber ≫ (R.toPseudofunctor.map ((Over.map b).map h.base).op.toLoc).toFunctor.map k.fiber ≫
      (R.toPseudofunctor.mapComp ((Over.map b).map k.base).op.toLoc ((Over.map b).map h.base).op.toLoc).inv.toNatTrans.app _ ≫ 𝟙 _ = _
    simp

def affineView : AffinePoint (stack b R) ⥤ AffinePoint R where
  obj a := ⟨(totalView b R).obj a.obj, a.property⟩
  map h := ObjectProperty.homMk ((totalView b R).map h.hom)
  map_id _ := by apply ObjectProperty.hom_ext; exact (totalView b R).map_id _
  map_comp h k := by apply ObjectProperty.hom_ext; exact (totalView b R).map_comp _ _

/-- Original scalar rings and every original affine-scheme map are unchanged. -/
theorem rings_eq : (affineView b R).op ⋙ rings R = rings (stack b R) := rfl

def presheafRestriction : ModulePresheaf R ⥤ ModulePresheaf (stack b R) :=
  PresheafOfModulesOfCommRing.pushforward₀ (affineView b R) (rings R)

theorem restriction_cartesian (M : ModulePresheaf R) (hM : IsCartesian M) :
    IsCartesian ((presheafRestriction b R).obj M) := by
  intro a c f N
  exact hM ((affineView b R).op.map f) N

/-- The native cartesian-module inverse image, with its exact object and map recipe. -/
def restriction : QCoh R ⥤ QCoh (stack b R) where
  obj M := ⟨(presheafRestriction b R).obj M.obj, restriction_cartesian b R M.obj M.property⟩
  map f := ObjectProperty.homMk ((presheafRestriction b R).map f.hom)
  map_id _ := by apply ObjectProperty.hom_ext; exact (presheafRestriction b R).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (presheafRestriction b R).map_comp _ _

end MathlibExt.AlgebraicGeometry.RootEtaleRestrictions
