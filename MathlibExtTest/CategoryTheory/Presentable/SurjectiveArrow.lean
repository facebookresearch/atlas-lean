/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Presentable.SurjectiveArrow

/-!
The empty function and an infinite fold remain original surjective arrows.
The fiber-sensitive test exhibits a monomorphism with bijective source
component which every point square lifts through, but which is not an
isomorphism. The fold generator supplies the missing fiber constraint.
-/

set_option autoImplicit false
noncomputable section

universe w

open CategoryTheory CategoryTheory.Presentable TypeCat

attribute [local instance] Cardinal.fact_isRegular_aleph0

example : IsCardinalLocallyPresentable SurjectiveArrow.{w} Cardinal.aleph0.{w} :=
  inferInstance

example : IsAccessibleCategory.{w} SurjectiveArrow.{w} ∧
    Functor.IsAccessible.{w} surjectiveArrows.{w}.ι := surjectiveArrow_accessible

example : ∃ (P : ObjectProperty SurjectiveArrow.{w}) (_ : ObjectProperty.Small.{w} P),
    P.IsCardinalFilteredGenerator Cardinal.aleph0.{w} :=
  HasCardinalFilteredGenerator.exists_small_generator _ _

/-- The original empty surjection. -/
def emptyArrow : SurjectiveArrow.{w} :=
  ⟨Arrow.mk (𝟙 (PEmpty.{w + 1})), fun x => ⟨x, rfl⟩⟩

/-- The original fold from an infinite domain to a point. -/
def infiniteArrow : SurjectiveArrow.{w} :=
  ⟨Arrow.mk (ofHom (fun _ : ULift.{w} ℕ => (PUnit.unit : PUnit.{w + 1}))), by
    intro y
    cases y
    exact ⟨⟨0⟩, rfl⟩⟩

example : ∃ (J : Type w) (_ : SmallCategory J)
    (_ : IsCardinalFiltered J Cardinal.aleph0.{w}),
    compactGenerators.{w}.colimitsOfShape J infiniteArrow :=
  compactGenerators_isCardinalFilteredGenerator.exists_colimitsOfShape infiniteArrow

example : (pointMap infiniteArrow ⟨37⟩).hom.left PUnit.unit = ⟨37⟩ := rfl

example : (relationMap infiniteArrow ⟨37⟩ ⟨91⟩ rfl).hom.left ⟨false⟩ = ⟨37⟩ := rfl

example : (relationMap infiniteArrow ⟨37⟩ ⟨91⟩ rfl).hom.left ⟨true⟩ = ⟨91⟩ := rfl

/-- The identity surjection with two distinct fibers. -/
def discretePair : SurjectiveArrow.{w} :=
  ⟨Arrow.mk (𝟙 (ULift.{w} Bool)), fun x => ⟨x, rfl⟩⟩

/-- The source map is the identity, and the target map collapses the two fibers. -/
def forgetFiber : discretePair.{w} ⟶ relationArrow.{w} :=
  ObjectProperty.homMk (Arrow.homMk
    (𝟙 (ULift.{w} Bool))
    (ofHom (fun _ : ULift.{w} Bool => (PUnit.unit : PUnit.{w + 1}))) (by ext; rfl))

instance : Mono forgetFiber.{w} := by
  constructor
  intro Z g h hgh
  apply hom_ext_left
  exact congrArg (fun q : Z ⟶ relationArrow => q.hom.left) hgh

theorem forgetFiber_points_lift :
    Function.Surjective (fun k : pointArrow.{w} ⟶ discretePair => k ≫ forgetFiber) := by
  intro k
  refine ⟨pointMap discretePair (k.hom.left PUnit.unit), ?_⟩
  apply hom_ext_left
  ext t
  cases t
  rfl

theorem forgetFiber_not_isIso : ¬ IsIso forgetFiber.{w} := by
  intro h
  have : IsIso forgetFiber.{w}.hom := (ObjectProperty.isIso_hom_iff _).mpr h
  have : IsIso forgetFiber.{w}.hom.right := inferInstance
  have hi := ((isIso_iff_bijective forgetFiber.{w}.hom.right).mp inferInstance).1
  have hBool : false = true := congrArg ULift.down
    (hi (show forgetFiber.{w}.hom.right ⟨false⟩ =
      forgetFiber.{w}.hom.right ⟨true⟩ from rfl))
  cases hBool

/-- Point lifting alone is insufficient; actual fiber lifting fails on this map. -/
example : ¬ Function.Surjective
    (fun k : relationArrow.{w} ⟶ discretePair => k ≫ forgetFiber) := by
  intro h
  exact forgetFiber_not_isIso
    (isIso_of_point_relation_surjective _ forgetFiber_points_lift h)

example : emptyArrow.{w}.obj.hom = 𝟙 (PEmpty.{w + 1}) := rfl

example : infiniteArrow.{w}.obj.hom ⟨314⟩ = PUnit.unit := rfl
