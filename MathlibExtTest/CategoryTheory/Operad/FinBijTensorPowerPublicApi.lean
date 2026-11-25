/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Operad.FinBijTensorPower

/-!
# Focused O7E tensor-power functor public-contract packet

Pins the stable downstream-facing contracts for the tensor-power
functor on the small finite-bijection groupoid: the object formula
as an iterated tensor power of the skeleton length, the map
formula through the permutation iso, and the named strong-monoidal
and braided structures.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [SymmetricCategory.{v} C]

-- Tensor powers evaluate to iterated tensor powers of the length.
example (X : C) (A : CategoryTheory.Operad.SmallFinBijGroupoid) :
    (_root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor X).obj A =
      tensorPowObj X A.of.len :=
  _root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor_obj X A

-- Tensor-power maps go through the permutation iso.
example (X : C) {A B : CategoryTheory.Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    (_root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor X).map f =
      (permutationIso X
        ((Equiv.ulift.symm :
            Fin A.of.len ≃ ULift (Fin A.of.len)).trans
          ((CategoryTheory.Operad.FinBijGroupoid.equivOfHom
            (CategoryTheory.Operad.smallFinBijEquivalence.functor.map f)).trans
            (Equiv.ulift :
              ULift (Fin B.of.len) ≃ Fin B.of.len)))).hom :=
  _root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor_map X f

-- The tensor-power functor carries a strong-monoidal structure.
noncomputable example (X : C) : (_root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor X).Monoidal :=
  _root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorMonoidal X

-- The tensor-power functor carries a braided structure.
noncomputable example (X : C) : (_root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor X).Braided :=
  _root_.CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided X
