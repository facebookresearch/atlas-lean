/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Limits.Shapes.NaturalArrowColimit
public import MathlibExt.CategoryTheory.Action.Orbit
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Conj

/-!
# Whole Arrow actions and their actual endpoint functors

An action on a whole Arrow retains both endpoints, every action square and
all equivariant input maps. The functors also retain actual Arrow transport.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uj vj ug u v
open CategoryTheory CategoryTheory.Limits
namespace Action
variable {C : Type u} [Category.{v} C] {G : Type ug} [Monoid G]

/-- The source action retains the left component of every original action square. -/
def leftActionFunctor : Action (Arrow C) G ⥤ Action C G :=
  (Arrow.leftFunc : Arrow C ⥤ C).mapAction G

/-- The target action retains the right component of every original action square. -/
def rightActionFunctor : Action (Arrow C) G ⥤ Action C G :=
  (Arrow.rightFunc : Arrow C ⥤ C).mapAction G

/-- The original arrow of a whole-arrow action is an actual equivariant morphism. -/
def actionUnderlyingHom (A : Action (Arrow C) G) :
    leftActionFunctor.obj A ⟶ rightActionFunctor.obj A where
  hom := A.V.hom
  comm g := (A.ρ g).asHom.w

/-- Every whole action square retains both original source and target components. -/
def underlyingActionTransformation : leftActionFunctor (C := C) (G := G) ⟶
    rightActionFunctor where
  app := actionUnderlyingHom
  naturality _ _ f := Action.Hom.ext f.hom.w

/-- The checked whole Arrow iso transports the entire original group action. -/
def transportArrowAction (A : Action (Arrow C) G) {B : Arrow C} (e : A.V ≅ B) :
    Action (Arrow C) G :=
  Action.mk B (e.conj.toMonoidHom.comp A.ρ)

/-- The original complete Arrow iso is also the actual isomorphism of actions. -/
def transportArrowActionIso (A : Action (Arrow C) G) {B : Arrow C} (e : A.V ≅ B) :
    A ≅ transportArrowAction A e :=
  Action.mkIso e (by
    intro g
    change (A.ρ g).asHom ≫ e.hom = e.hom ≫ (e.conj (A.ρ g)).asHom
    rw [Iso.conj_apply_asHom]
    simp only [Iso.hom_inv_id_assoc])

/-- Transport retains both source and target action maps through the same whole Arrow iso. -/
theorem transportArrowAction_map (A : Action (Arrow C) G)
    {B : Arrow C} (e : A.V ≅ B) (g : G) :
    ((transportArrowAction A e).ρ g).asHom = e.inv ≫ (A.ρ g).asHom ≫ e.hom :=
  Iso.conj_apply_asHom e (A.ρ g)


section WholeArrows

variable {C : Type u} [Category.{v} C] {G : Type ug} [Monoid G]

/-- The original equivariant source and target actions form the entire
original Arrow in the action category. -/
def equivariantArrowFunctor : Action (Arrow C) G ⥤ Arrow (Action C G) :=
  CategoryTheory.naturalArrowFunctor underlyingActionTransformation

/-- The original coefficient morphism gives its whole-arrow action;
the two diagonal components are its original source and target actions. -/
def wholeArrowAction (a : Arrow (Action C G)) : Action (Arrow C) G where
  V := Arrow.mk a.hom.hom
  ρ :=
    { toFun g := .of (Arrow.homMk (a.left.ρ g).asHom (a.right.ρ g).asHom (a.hom.comm g))
      map_one' := by
        apply End.ext
        apply Arrow.hom_ext
        · change (a.left.ρ 1).asHom = 𝟙 a.left.V
          rw [map_one]
          rfl
        · change (a.right.ρ 1).asHom = 𝟙 a.right.V
          rw [map_one]
          rfl
      map_mul' g h := by
        apply End.ext
        apply Arrow.hom_ext
        · change (a.left.ρ (g * h)).asHom = (a.left.ρ h).asHom ≫ (a.left.ρ g).asHom
          rw [map_mul]
          rfl
        · change (a.right.ρ (g * h)).asHom = (a.right.ρ h).asHom ≫ (a.right.ρ g).asHom
          rw [map_mul]
          rfl }

/-- Every original square of equivariant arrows remains the same complete
square, including both endpoint action commutation equations. -/
def wholeArrowActionMap {a b : Arrow (Action C G)} (f : a ⟶ b) :
    wholeArrowAction a ⟶ wholeArrowAction b where
  hom := Arrow.homMk f.left.hom f.right.hom (congrArg Action.Hom.hom f.w)
  comm g := by
    apply Arrow.hom_ext
    · exact f.left.comm g
    · exact f.right.comm g

/-- Whole-arrow actions are functorial in every original coefficient
and input square, before any tensor product or orbit is taken. -/
def wholeArrowActionFunctor : Arrow (Action C G) ⥤ Action (Arrow C) G where
  obj := wholeArrowAction
  map := wholeArrowActionMap
  map_id a := by
    apply Action.Hom.ext
    apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Action.Hom.ext
    apply Arrow.hom_ext <;> rfl

/-- Both original endpoint maps are retained by the whole-arrow action functor. -/
theorem wholeArrowActionMap_components {a b : Arrow (Action C G)} (f : a ⟶ b) :
    (wholeArrowActionMap f).hom.left = f.left.hom ∧
      (wholeArrowActionMap f).hom.right = f.right.hom := ⟨rfl, rfl⟩

/-- The entire actual action square has the two original diagonal group maps. -/
theorem wholeArrowAction_rho (a : Arrow (Action C G)) (g : G) :
    ((wholeArrowAction a).ρ g).asHom.left = (a.left.ρ g).asHom ∧
      ((wholeArrowAction a).ρ g).asHom.right = (a.right.ρ g).asHom := ⟨rfl, rfl⟩

/-- The original whole-arrow action is recovered through the original
source and target action projections. -/
def wholeArrowActionComparison (A : Action (Arrow C) G) :
    A ≅ wholeArrowAction ((equivariantArrowFunctor (C := C) (G := G)).obj A) :=
  Action.mkIso (Iso.refl _) (by
    intro g
    have h : ((wholeArrowAction (equivariantArrowFunctor.obj A)).ρ g).asHom =
        (A.ρ g).asHom := by apply Arrow.hom_ext <;> rfl
    exact (Category.comp_id _).trans (h.symm.trans (Category.id_comp _).symm))

end WholeArrows

end Action

namespace Action

variable {C : Type u} [Category.{v} C] {G : Type ug} [Monoid G]
  [HasColimitsOfShape (SingleObj G) C]

/-- The complete equivariant arrow retains both actual coinvariant endpoint maps. -/
def orbitArrowFunctor : Action (Arrow C) G ⥤ Arrow C :=
  equivariantArrowFunctor ⋙ (coinvariantsFunctor (C := C) G).mapArrow

end Action

namespace CategoryTheory.OperadicOrbitCells.ProfileGeometry

variable {J : Type uj} [Category.{vj} J] {C : Type u} [Category.{v} C] {A B : J ⥤ C}

@[inherit_doc CategoryTheory.naturalArrowFunctor]
abbrev naturalArrowFunctor (a : A ⟶ B) : J ⥤ Arrow C := CategoryTheory.naturalArrowFunctor a

end CategoryTheory.OperadicOrbitCells.ProfileGeometry

namespace CategoryTheory.OperadicOrbitCells

variable {C : Type u} [Category.{v} C]

@[inherit_doc CategoryTheory.pointwiseArrowFunctor]
abbrev pointwiseArrowFunctor {J : Type uj} [Category.{vj} J] : Arrow (J ⥤ C) ⥤ J ⥤ Arrow C :=
  CategoryTheory.pointwiseArrowFunctor

section TransportArrowActions

variable {G : Type ug} [Group G]

@[inherit_doc Action.transportArrowAction]
abbrev transportArrowAction (A : Action (Arrow C) G) {B : Arrow C} (e : A.V ≅ B) :
    Action (Arrow C) G := Action.transportArrowAction A e

@[inherit_doc Action.transportArrowActionIso]
abbrev transportArrowActionIso (A : Action (Arrow C) G) {B : Arrow C} (e : A.V ≅ B) :
    A ≅ transportArrowAction A e := Action.transportArrowActionIso A e

@[inherit_doc Action.transportArrowAction_map]
theorem transportArrowAction_map (A : Action (Arrow C) G)
    {B : Arrow C} (e : A.V ≅ B) (g : G) :
    ((transportArrowAction A e).ρ g).asHom = e.inv ≫ (A.ρ g).asHom ≫ e.hom :=
  Action.transportArrowAction_map A e g

end TransportArrowActions

variable {G : Type ug} [Monoid G]

@[inherit_doc Action.leftActionFunctor]
abbrev leftActionFunctor : Action (Arrow C) G ⥤ Action C G := Action.leftActionFunctor

@[inherit_doc Action.rightActionFunctor]
abbrev rightActionFunctor : Action (Arrow C) G ⥤ Action C G := Action.rightActionFunctor

@[inherit_doc Action.actionUnderlyingHom]
abbrev actionUnderlyingHom (A : Action (Arrow C) G) :
    leftActionFunctor.obj A ⟶ rightActionFunctor.obj A := Action.actionUnderlyingHom A

@[inherit_doc Action.underlyingActionTransformation]
abbrev underlyingActionTransformation : leftActionFunctor (C := C) (G := G) ⟶ rightActionFunctor :=
  Action.underlyingActionTransformation

@[inherit_doc Action.equivariantArrowFunctor]
abbrev actionArrowFunctor : Action (Arrow C) G ⥤ Arrow (Action C G) := Action.equivariantArrowFunctor

@[inherit_doc Action.wholeArrowActionFunctor]
abbrev arrowActionFunctor : Arrow (Action C G) ⥤ Action (Arrow C) G := Action.wholeArrowActionFunctor

variable [HasColimitsOfShape (SingleObj G) C]

@[inherit_doc Action.coinvariantsFunctor]
abbrev actionOrbitFunctor : Action C G ⥤ C := Action.coinvariantsFunctor (C := C) G

@[inherit_doc Action.orbitArrowFunctor]
abbrev arrowActionOrbitFunctor : Action (Arrow C) G ⥤ Arrow C := Action.orbitArrowFunctor

end CategoryTheory.OperadicOrbitCells
