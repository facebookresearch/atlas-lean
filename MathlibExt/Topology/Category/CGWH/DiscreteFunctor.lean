/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.DiscreteCoproduct
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Actual discrete CGWH index functors
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory

namespace CGWH

/-- The actual lifted continuous map between the named native discrete spaces. -/
def discreteMap {I J : Type w} (f : I → J) :
    discreteObj.{u, v, w} I ⟶ discreteObj.{u, v, w} J := by
  letI := discreteObj_discreteTopology.{u, v, w} I
  exact ConcreteCategory.ofHom
    (show C(discreteObj.{u, v, w} I, discreteObj.{u, v, w} J) from
      ⟨fun x => ULift.up (f (show ULift.{v} I from x).down),
        continuous_of_discreteTopology⟩)

@[simp]
theorem discreteMap_apply {I J : Type w} (f : I → J) (i : I) :
    discreteMap.{u, v, w} f (ULift.up i) = ULift.up (f i) :=
  rfl

@[simp]
theorem discreteMap_id (I : Type w) :
    discreteMap.{u, v, w} (_root_.id : I → I) = 𝟙 (discreteObj.{u, v, w} I) := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem discreteMap_comp {I J K : Type w} (f : I → J) (g : J → K) :
    discreteMap.{u, v, w} (g ∘ f) = discreteMap f ≫ discreteMap g := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

@[reassoc (attr := simp)]
theorem discreteObjIncl_naturality {I J : Type w} (f : I → J) (i : I) :
    discreteObjIncl.{u, v, w} I i ≫ discreteMap f = discreteObjIncl J (f i) := by
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- The actual universe-polymorphic native discrete-space functor. -/
def discreteFunctor : Type w ⥤ CGWH.{u, max v w} where
  obj I := discreteObj.{u, v, w} I
  map f := discreteMap (fun i => f i)
  map_id I := discreteMap_id I
  map_comp f g := discreteMap_comp (fun i => f i) (fun j => g j)

@[simp]
theorem discreteFunctor_obj (I : Type w) :
    discreteFunctor.{u, v, w}.obj I = discreteObj.{u, v, w} I :=
  rfl

@[simp]
theorem discreteFunctor_map {I J : Type w} (f : I → J) :
    discreteFunctor.{u, v, w}.map (↾f) = discreteMap.{u, v, w} f :=
  rfl

/-- The native discrete functor forgets to the existing lifted TopCat discrete functor. -/
def discreteFunctorToTopIso :
    discreteFunctor.{u, v, w} ⋙ cgwhToTop ≅
      uliftFunctor.{v, w} ⋙ TopCat.discrete :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro I J f
    rfl)

end CGWH
