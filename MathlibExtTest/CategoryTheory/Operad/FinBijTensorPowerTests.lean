/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Operad.FinBijTensorPower

set_option autoImplicit false

noncomputable section

namespace MathlibExtTest.FinBijTensorPowerTests

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower
open _root_.CategoryTheory.Operad
open _root_.CategoryTheory.Operad.SmallFinBijGroupoid
open scoped MonoidalCategory

universe v' u'

#check SmallFinBijGroupoid.tensorPowerFunctor
#check SmallFinBijGroupoid.tensorPowerFunctor_obj
#check SmallFinBijGroupoid.tensorPowerFunctor_map
#check SmallFinBijGroupoid.tensorPowerFunctorMonoidal
#check SmallFinBijGroupoid.tensorPowerFunctorBraided

#check @SmallFinBijGroupoid.tensorPowerFunctor.{0, 1}
#check @SmallFinBijGroupoid.tensorPowerFunctor_obj.{0, 1}
#check @SmallFinBijGroupoid.tensorPowerFunctor_map.{0, 1}
#check @SmallFinBijGroupoid.tensorPowerFunctorMonoidal.{0, 1}
#check @SmallFinBijGroupoid.tensorPowerFunctorBraided.{0, 1}

#check @SmallFinBijGroupoid.tensorPowerFunctor.{1, 2}
#check @SmallFinBijGroupoid.tensorPowerFunctor_obj.{1, 2}
#check @SmallFinBijGroupoid.tensorPowerFunctor_map.{1, 2}
#check @SmallFinBijGroupoid.tensorPowerFunctorMonoidal.{1, 2}
#check @SmallFinBijGroupoid.tensorPowerFunctorBraided.{1, 2}

section Symbolic

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory.{v'} C]
  [SymmetricCategory.{v'} C]
variable (X : C)

example (A : Operad.SmallFinBijGroupoid) :
    (tensorPowerFunctor X).obj A = tensorPowObj X A.of.len :=
  tensorPowerFunctor_obj X A

example {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    (tensorPowerFunctor X).map f =
      (permutationIso X
        ((Equiv.ulift.symm : Fin A.of.len ≃ ULift (Fin A.of.len)).trans
          ((Operad.FinBijGroupoid.equivOfHom
            (Operad.smallFinBijEquivalence.functor.map f)).trans
            (Equiv.ulift : ULift (Fin B.of.len) ≃ Fin B.of.len)))).hom :=
  tensorPowerFunctor_map X f

example : (tensorPowerFunctor X).Monoidal := tensorPowerFunctorMonoidal X

example : (tensorPowerFunctor X).Braided := tensorPowerFunctorBraided X

/-! The named structures are values, not global instances. -/

/-- error: failed to synthesize instance of type class -/
#guard_msgs (error, drop info, substring := true) in
example : (tensorPowerFunctor X).Monoidal := by infer_instance

/-- error: failed to synthesize instance of type class -/
#guard_msgs (error, drop info, substring := true) in
example : (tensorPowerFunctor X).Braided := by infer_instance

example (A B D : Operad.SmallFinBijGroupoid) : True := by
  have _ := (tensorPowerFunctorMonoidal X).toLaxMonoidal.associativity A B D
  have _ := (tensorPowerFunctorMonoidal X).toLaxMonoidal.left_unitality A
  have _ := (tensorPowerFunctorMonoidal X).toLaxMonoidal.right_unitality A
  trivial

example (A B : Operad.SmallFinBijGroupoid) : True := by
  have _ := (tensorPowerFunctorBraided X).toLaxBraided.braided A B
  trivial

attribute [local instance] tensorPowerFunctorMonoidal in
example (A B D : Operad.SmallFinBijGroupoid) : True := by
  have _ := Functor.LaxMonoidal.associativity
    (tensorPowerFunctor X) A B D
  have _ := Functor.LaxMonoidal.left_unitality
    (tensorPowerFunctor X) A
  have _ := Functor.LaxMonoidal.right_unitality
    (tensorPowerFunctor X) A
  trivial

attribute [local instance] tensorPowerFunctorBraided in
example : (tensorPowerFunctor X).Braided := inferInstance

end Symbolic

/-! Shared Operad implementation declarations remain publicly available. -/

#check CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom

#check CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorCoreMonoidal

#print axioms SmallFinBijGroupoid.tensorPowerFunctor
#print axioms SmallFinBijGroupoid.tensorPowerFunctor_obj
#print axioms SmallFinBijGroupoid.tensorPowerFunctor_map
#print axioms SmallFinBijGroupoid.tensorPowerFunctorMonoidal
#print axioms SmallFinBijGroupoid.tensorPowerFunctorBraided

end MathlibExtTest.FinBijTensorPowerTests
