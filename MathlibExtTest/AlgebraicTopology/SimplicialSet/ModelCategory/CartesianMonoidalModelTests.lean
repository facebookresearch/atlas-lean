/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel

/-! Tests for the cartesian monoidal Kan--Quillen model structure. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped MonoidalCategory

namespace MathlibExtTest.SSet.CartesianMonoidalModel

section ScopeOff

#synth MonoidalCategory SSet.{u}
#synth SymmetricCategory SSet.{u}
#synth MonoidalClosed SSet.{u}
#synth CategoryTheory.SimplicialCategory SSet.{u}

example (X Y : SSet.{u}) :
    CategoryTheory.SimplicialCategory.sHom X Y = (ihom X).obj Y := rfl

example : True := by
  fail_if_success
    let _ : ModelCategory SSet.{u} := inferInstance
  let _ : ModelCategory SSet.{u} :=
    SSet.modelCategoryQuillen.instModelCategory
  fail_if_success
    let _ : IsClosedSymmetricMonoidalModelCategory SSet.{u} :=
      inferInstance
  trivial

end ScopeOff

section SelectedScope

open scoped SSet.modelCategoryQuillen

#synth ModelCategory SSet.{u}
#synth IsClosedSymmetricMonoidalModelCategory SSet.{u}
#synth IsClosedSymmetricMonoidalModelCategory SSet.{1}
#synth IsClosedSymmetricMonoidalModelCategory SSet.{0}

section Clauses

variable {A B K L : SSet.{u}}
variable (i : A ⟶ B) (j : K ⟶ L)

example (_hi : cofibrations SSet.{u} i)
    (_hj : cofibrations SSet.{u} j) :
    cofibrations SSet.{u} ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    i j _hi _hj

example (_hi : trivialCofibrations SSet.{u} i)
    (_hj : cofibrations SSet.{u} j) :
    trivialCofibrations SSet.{u}
      ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    i j _hi _hj

example (_hi : cofibrations SSet.{u} i)
    (_hj : trivialCofibrations SSet.{u} j) :
    trivialCofibrations SSet.{u}
      ((Arrow.mk i □ Arrow.mk j).hom) :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
    i j _hi _hj

end Clauses

section Unit

example : IsCofibrant (𝟙_ SSet.{u}) := inferInstance

example : Nonempty (MonoidalUnitAxiomWitness SSet.{u}) :=
  IsClosedSymmetricMonoidalModelCategory.unit_axiom

end Unit

section ParentReuse

example : CartesianMonoidalCategory SSet.{u} := inferInstance
example : MonoidalClosed SSet.{u} := inferInstance
example : CategoryTheory.SimplicialCategory SSet.{u} := inferInstance

example : True := by
  have hModel : (inferInstance : ModelCategory SSet.{u}) =
      SSet.modelCategoryQuillen.instModelCategory := rfl
  clear hModel
  trivial

end ParentReuse

section DeletedOrientationFalsifiers

variable
  (_hcof : ∀ {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L),
      cofibrations SSet.{u} i →
      cofibrations SSet.{u} j →
      cofibrations SSet.{u} ((Arrow.mk i □ Arrow.mk j).hom))
  (_hleft : ∀ {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L),
      trivialCofibrations SSet.{u} i →
      cofibrations SSet.{u} j →
      trivialCofibrations SSet.{u}
        ((Arrow.mk i □ Arrow.mk j).hom))
  (_hright : ∀ {A B K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L),
      cofibrations SSet.{u} i →
      trivialCofibrations SSet.{u} j →
      trivialCofibrations SSet.{u}
        ((Arrow.mk i □ Arrow.mk j).hom))
  (_hunit : Nonempty (MonoidalUnitAxiomWitness SSet.{u}))

example : True := by
  fail_if_success
    exact ({
      cofibration_pushoutProduct := _hcof
      trivial_pushoutProduct_right := _hright
      unit_axiom := _hunit } :
        IsClosedSymmetricMonoidalModelCategory SSet.{u})
  trivial

example : True := by
  fail_if_success
    exact ({
      cofibration_pushoutProduct := _hcof
      trivial_pushoutProduct_left := _hleft
      unit_axiom := _hunit } :
        IsClosedSymmetricMonoidalModelCategory SSet.{u})
  trivial

end DeletedOrientationFalsifiers

end SelectedScope

section ScopeTeardown

#synth MonoidalCategory SSet.{u}
#synth SymmetricCategory SSet.{u}
#synth MonoidalClosed SSet.{u}
#synth CategoryTheory.SimplicialCategory SSet.{u}

example : True := by
  fail_if_success
    let _ : ModelCategory SSet.{u} := inferInstance
  let _ : ModelCategory SSet.{u} :=
    SSet.modelCategoryQuillen.instModelCategory
  fail_if_success
    let _ : IsClosedSymmetricMonoidalModelCategory SSet.{u} :=
      inferInstance
  trivial

end ScopeTeardown

section Nonclaims

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.instCartesianMonoidalCategory

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.instSymmetricCategory

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.instMonoidalClosed

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.instSimplicialCategory

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.instCombinatorialModelCategory

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.monoidAxiom

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.instPointedSmashModelCategory

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.localizedModelCategory

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.spectraModelCategory

end Nonclaims

#print axioms
  SSet.modelCategoryQuillen.instIsClosedSymmetricMonoidalModelCategory

end MathlibExtTest.SSet.CartesianMonoidalModel
