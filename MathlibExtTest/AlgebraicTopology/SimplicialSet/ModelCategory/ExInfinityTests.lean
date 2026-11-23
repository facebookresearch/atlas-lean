/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ExInfinity

import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import MathlibExt.AlgebraicTopology.ModelCategory.Replacement

/-!
# Owner tests for the explicit infinite Ex construction

The clients exercise the four public declarations, install the theorem-valued
Kan result only locally, and keep the finite tower, large-universe reindex,
one-step Kan, replacement equality, and property instances private.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace ExInfinityTests

section PublicSurface

example : CategoryTheory.Functor SSet.{u} SSet.{u} := SSet.exInfinity

example : Functor.id (SSet.{u}) ⟶ SSet.exInfinity :=
  SSet.exInfinityUnit

example (X : SSet.{u}) :
    SSet.KanComplex (SSet.exInfinity.obj X) :=
  SSet.exInfinity_kanComplex X

example (X : SSet.{1}) :
    SSet.KanComplex (SSet.exInfinity.obj X) := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  infer_instance

example (X : SSet.{0}) :
    SSet.KanComplex (SSet.exInfinity.obj X) := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  infer_instance

example (X : SSet.{u}) :
    SSet.realizationWeakEquivalences
      (SSet.exInfinityUnit.app X) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences X

example (X : SSet.{1}) :
    SSet.realizationWeakEquivalences
      (SSet.exInfinityUnit.app X) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences X

example (X : SSet.{0}) :
    SSet.realizationWeakEquivalences
      (SSet.exInfinityUnit.app X) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences X

end PublicSurface

section Functoriality

example (X : SSet.{u}) :
    SSet.exInfinity.map (𝟙 X) = 𝟙 (SSet.exInfinity.obj X) :=
  SSet.exInfinity.map_id X

example {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.exInfinity.map (f ≫ g) =
      SSet.exInfinity.map f ≫ SSet.exInfinity.map g :=
  SSet.exInfinity.map_comp f g

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ SSet.exInfinityUnit.app Y =
      SSet.exInfinityUnit.app X ≫ SSet.exInfinity.map f :=
  SSet.exInfinityUnit.naturality f

end Functoriality

section LocalKanClients

example (X : SSet.{u}) :
    SSet.KanComplex (SSet.exInfinity.obj X) := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  infer_instance

example (X : SSet.{1}) :
    SSet.KanComplex (SSet.exInfinity.obj X) := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  infer_instance

example (X : SSet.{0}) :
    SSet.KanComplex (SSet.exInfinity.obj X) := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  infer_instance

end LocalKanClients

section HornClients

example (X : SSet.{u}) (i : Fin 2)
    (f : (SSet.horn (n := 1) i : SSet.{u}) ⟶
      SSet.exInfinity.obj X) :
    ∃ g : (Δ[1] : SSet.{u}) ⟶ SSet.exInfinity.obj X,
      f = (SSet.horn (n := 1) i).ι ≫ g := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  exact SSet.KanComplex.hornFilling f

example (X : SSet.{u}) (i : Fin 3)
    (f : (SSet.horn (n := 2) i : SSet.{u}) ⟶
      SSet.exInfinity.obj X) :
    ∃ g : (Δ[2] : SSet.{u}) ⟶ SSet.exInfinity.obj X,
      f = (SSet.horn (n := 2) i).ι ≫ g := by
  let _ : SSet.KanComplex (SSet.exInfinity.obj X) :=
    SSet.exInfinity_kanComplex X
  exact SSet.KanComplex.hornFilling f

end HornClients

section BoundaryInputs

private abbrev emptySSet : SSet.{u} :=
  ((⊥ : SSet.Subcomplex (Δ[0] : SSet.{u})) : SSet.{u})

private abbrev twoPointSSet : SSet :=
  (Functor.const SimplexCategoryᵒᵖ).obj (Fin 2)

private noncomputable abbrev collapsedBoundaryTwoSphere : SSet.{u} :=
  pushout (SSet.boundary.{u} 2).ι
    (terminal.from (SSet.boundary.{u} 2 : SSet.{u}))

example : SSet.KanComplex
    (SSet.exInfinity.obj emptySSet.{u}) :=
  SSet.exInfinity_kanComplex _

example : SSet.realizationWeakEquivalences
    (SSet.exInfinityUnit.app emptySSet.{u}) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences _

example : SSet.KanComplex
    (SSet.exInfinity.obj (Δ[0] : SSet.{u})) :=
  SSet.exInfinity_kanComplex _

example : SSet.KanComplex
    (SSet.exInfinity.obj (Δ[1] : SSet.{u})) :=
  SSet.exInfinity_kanComplex _

example : SSet.realizationWeakEquivalences
    (SSet.exInfinityUnit.app (Δ[1] : SSet.{u})) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences _

example : SSet.KanComplex
    (SSet.exInfinity.obj twoPointSSet) :=
  SSet.exInfinity_kanComplex _

example : SSet.realizationWeakEquivalences
    (SSet.exInfinityUnit.app twoPointSSet) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences _

example : SSet.KanComplex
    (SSet.exInfinity.obj SSet.S1) :=
  SSet.exInfinity_kanComplex _

example : SSet.realizationWeakEquivalences
    (SSet.exInfinityUnit.app SSet.S1) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences _

example : SSet.KanComplex
    (SSet.exInfinity.obj collapsedBoundaryTwoSphere.{u}) :=
  SSet.exInfinity_kanComplex _

example : SSet.realizationWeakEquivalences
    (SSet.exInfinityUnit.app collapsedBoundaryTwoSphere.{u}) :=
  SSet.exInfinityUnit_mem_realizationWeakEquivalences _

end BoundaryInputs

section NegativeInstances

set_option linter.unreachableTactic false in
example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ : SSet.KanComplex (SSet.exInfinity.obj _X) := inferInstance
  fail_if_success
    let _ : SSet.KanComplex (SSet.ex.obj _X) := inferInstance
  fail_if_success
    let _ : Mono (SSet.exInfinityUnit.app _X) := inferInstance
  fail_if_success
    let _ : WeakEquivalence (SSet.exInfinityUnit.app _X) := inferInstance
  fail_if_success
    have _ : SSet.exInfinity.obj _X =
        (HomotopicalAlgebra.fibrantReplacement
          (C := SSet.{u})).obj _X := by
      rfl
  trivial

end NegativeInstances

section PrivateBoundary

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exIter

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exTower

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exSmallTower

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exTowerColimitIso

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.hornDoubleSubdivisionRetraction

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exists_exIter_horn_extension

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exInfinity_kanComplex_of_horn_extension

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exInfinity_eq_fibrantReplacement

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exInfinityULift

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.exInfinityAsSmall

end PrivateBoundary

#print axioms SSet.exInfinity
#print axioms SSet.exInfinityUnit
#print axioms SSet.exInfinity_kanComplex
#print axioms SSet.exInfinityUnit_mem_realizationWeakEquivalences

end ExInfinityTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory

end
