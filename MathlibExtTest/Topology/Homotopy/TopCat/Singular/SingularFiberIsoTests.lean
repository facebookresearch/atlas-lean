/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularFiberIso

/-!
# Tests for strict-fiber isomorphisms

These clients pin the same-universe singular-fiber comparison, transport of
strict simplicial fibers across isomorphisms, both ambient inclusion laws,
their degreewise forms, inverse laws, and Type 0/1 elaboration.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SingularFiberIsoTests

section SingularFiber

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y)

example :
    TopCat.toSSet.obj (TopCat.of {x : X // f x = y}) ≅
      (SSet.Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u}) :=
  SSet.singularFiberIso f y

theorem singular_hom_inclusion_client :
    (SSet.singularFiberIso f y).hom ≫
        (SSet.Subcomplex.fiber
          (TopCat.toSSet.map (TopCat.ofHom f))
          (TopCat.toSSetObj₀Equiv.symm y)).ι =
      TopCat.toSSet.map
        (AlgebraicTopology.subspaceIncl
          (X := TopCat.of X) (Set.ofPred fun x : X => f x = y)) :=
  SSet.singularFiberIso_hom_ι f y

theorem singular_inv_inclusion_client :
    (SSet.singularFiberIso f y).inv ≫
        TopCat.toSSet.map
          (AlgebraicTopology.subspaceIncl
            (X := TopCat.of X) (Set.ofPred fun x : X => f x = y)) =
      (SSet.Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y)).ι :=
  SSet.singularFiberIso_inv_ι f y

theorem singular_hom_component_client
    (n : SimplexCategoryᵒᵖ)
    (sigma : (TopCat.toSSet.obj (TopCat.of {x : X // f x = y})).obj n) :
    ((SSet.singularFiberIso f y).hom.app n sigma).val =
      (TopCat.toSSet.map
        (AlgebraicTopology.subspaceIncl
          (X := TopCat.of X) (Set.ofPred fun x : X => f x = y))).app n sigma :=
  SSet.singularFiberIso_hom_app_val f y n sigma

theorem singular_inv_component_client
    (n : SimplexCategoryᵒᵖ)
    (sigma : (SSet.Subcomplex.fiber
      (TopCat.toSSet.map (TopCat.ofHom f))
      (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u}).obj n) :
    (TopCat.toSSet.map
      (AlgebraicTopology.subspaceIncl
        (X := TopCat.of X) (Set.ofPred fun x : X => f x = y))).app n
        ((SSet.singularFiberIso f y).inv.app n sigma) = sigma.val :=
  SSet.singularFiberIso_inv_app_inclusion f y n sigma

theorem singular_hom_inv_client :
    (SSet.singularFiberIso f y).hom ≫ (SSet.singularFiberIso f y).inv =
      𝟙 (TopCat.toSSet.obj (TopCat.of {x : X // f x = y})) :=
  (SSet.singularFiberIso f y).hom_inv_id

theorem singular_inv_hom_client :
    (SSet.singularFiberIso f y).inv ≫ (SSet.singularFiberIso f y).hom =
      𝟙 (SSet.Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y) : SSet.{u}) :=
  (SSet.singularFiberIso f y).inv_hom_id

end SingularFiber

section MapFiber

variable {X Y X' Y' : SSet.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
variable (eX : X ≅ X') (eY : Y ≅ Y')
variable (hc : eX.hom ≫ f' = f ≫ eY.hom)
variable {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
variable (hy : eY.hom.app _ y = y')

example :
    (SSet.Subcomplex.fiber f y : SSet.{u}) ≅
      (SSet.Subcomplex.fiber f' y' : SSet.{u}) :=
  SSet.Subcomplex.mapFiberIso eX eY hc hy

theorem mapFiber_hom_inclusion_client :
    (SSet.Subcomplex.mapFiberIso eX eY hc hy).hom ≫
        (SSet.Subcomplex.fiber f' y').ι =
      (SSet.Subcomplex.fiber f y).ι ≫ eX.hom :=
  SSet.Subcomplex.mapFiberIso_hom_ι eX eY hc hy

theorem mapFiber_inv_inclusion_client :
    (SSet.Subcomplex.mapFiberIso eX eY hc hy).inv ≫
        (SSet.Subcomplex.fiber f y).ι =
      (SSet.Subcomplex.fiber f' y').ι ≫ eX.inv :=
  SSet.Subcomplex.mapFiberIso_inv_ι eX eY hc hy

theorem mapFiber_hom_component_client
    (n : SimplexCategoryᵒᵖ)
    (sigma : (SSet.Subcomplex.fiber f y : SSet.{u}).obj n) :
    ((SSet.Subcomplex.mapFiberIso eX eY hc hy).hom.app n sigma).val =
      eX.hom.app n sigma.val :=
  SSet.Subcomplex.mapFiberIso_hom_app_val eX eY hc hy n sigma

theorem mapFiber_inv_component_client
    (n : SimplexCategoryᵒᵖ)
    (sigma : (SSet.Subcomplex.fiber f' y' : SSet.{u}).obj n) :
    ((SSet.Subcomplex.mapFiberIso eX eY hc hy).inv.app n sigma).val =
      eX.inv.app n sigma.val :=
  SSet.Subcomplex.mapFiberIso_inv_app_val eX eY hc hy n sigma

theorem mapFiber_hom_inv_client :
    (SSet.Subcomplex.mapFiberIso eX eY hc hy).hom ≫
        (SSet.Subcomplex.mapFiberIso eX eY hc hy).inv =
      𝟙 (SSet.Subcomplex.fiber f y : SSet.{u}) :=
  (SSet.Subcomplex.mapFiberIso eX eY hc hy).hom_inv_id

theorem mapFiber_inv_hom_client :
    (SSet.Subcomplex.mapFiberIso eX eY hc hy).inv ≫
        (SSet.Subcomplex.mapFiberIso eX eY hc hy).hom =
      𝟙 (SSet.Subcomplex.fiber f' y' : SSet.{u}) :=
  (SSet.Subcomplex.mapFiberIso eX eY hc hy).inv_hom_id

end MapFiber

section UniverseZero

noncomputable def singularFiberIso_type_zero
    {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) :
    TopCat.toSSet.obj (TopCat.of {x : X // f x = y}) ≅
      (SSet.Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y) : SSet.{0}) :=
  SSet.singularFiberIso f y

noncomputable def mapFiberIso_type_zero
    {X Y X' Y' : SSet.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') :
    (SSet.Subcomplex.fiber f y : SSet.{0}) ≅
      (SSet.Subcomplex.fiber f' y' : SSet.{0}) :=
  SSet.Subcomplex.mapFiberIso eX eY hc hy

end UniverseZero

section UniverseOne

noncomputable def singularFiberIso_type_one
    {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) :
    TopCat.toSSet.obj (TopCat.of {x : X // f x = y}) ≅
      (SSet.Subcomplex.fiber
        (TopCat.toSSet.map (TopCat.ofHom f))
        (TopCat.toSSetObj₀Equiv.symm y) : SSet.{1}) :=
  SSet.singularFiberIso f y

noncomputable def mapFiberIso_type_one
    {X Y X' Y' : SSet.{1}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (hc : eX.hom ≫ f' = f ≫ eY.hom)
    {y : Y _⦋0⦌} {y' : Y' _⦋0⦌}
    (hy : eY.hom.app _ y = y') :
    (SSet.Subcomplex.fiber f y : SSet.{1}) ≅
      (SSet.Subcomplex.fiber f' y' : SSet.{1}) :=
  SSet.Subcomplex.mapFiberIso eX eY hc hy

end UniverseOne

section Negative

/-- error: Unknown constant `SSet.toSSetObjEquiv_map_naturality` -/
#guard_msgs (error, substring := true) in
#check SSet.toSSetObjEquiv_map_naturality

/-- error: Unknown constant `SSet.mono_toSSetMap_subspaceIncl` -/
#guard_msgs (error, substring := true) in
#check SSet.mono_toSSetMap_subspaceIncl

/-- error: Unknown constant `SSet.singularSubspaceRange_eq_fiber` -/
#guard_msgs (error, substring := true) in
#check SSet.singularSubspaceRange_eq_fiber

/-- error: Unknown identifier `AlgebraicTopology.range_subspaceIncl_eq_subordinateSet` -/
#guard_msgs (error, substring := true) in
#check AlgebraicTopology.range_subspaceIncl_eq_subordinateSet

/-- error: Unknown constant `SSet.singularBasedPathIso` -/
#guard_msgs (error, substring := true) in
#check SSet.singularBasedPathIso

/-- error: Unknown constant `SSet.singularLoopIso` -/
#guard_msgs (error, substring := true) in
#check SSet.singularLoopIso

/-- error: Unknown constant `ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences` -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.WeaklyPointed.loopMap_mem_weakHomotopyEquivalences

end Negative

#print axioms SSet.singularFiberIso
#print axioms SSet.singularFiberIso_hom_ι
#print axioms SSet.singularFiberIso_inv_ι
#print axioms SSet.Subcomplex.mapFiberIso
#print axioms SSet.Subcomplex.mapFiberIso_hom_ι
#print axioms SSet.Subcomplex.mapFiberIso_inv_ι
#print axioms singular_hom_inv_client
#print axioms mapFiber_hom_inv_client

end MathlibExtTest.AlgebraicTopology.ModelCategory.SingularFiberIsoTests
