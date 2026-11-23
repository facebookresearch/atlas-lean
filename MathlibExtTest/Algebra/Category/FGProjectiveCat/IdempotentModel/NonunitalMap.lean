/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.NonunitalMap
import Mathlib.Data.Matrix.Basis
import Batteries.Tactic.Lint

open CategoryTheory
open FGProjectiveCat

noncomputable section
set_option autoImplicit false

universe u

namespace FGProjectiveCat.IdempotentModel.NonunitalMap.Tests

/-- The actual upper-left root inclusion fails to preserve the ambient matrix unit. -/
def singleEntry (R : Type u) [Ring R] : R →ₙ+* Matrix (Fin 2) (Fin 2) R where
  toFun n := Matrix.single 0 0 n
  map_zero' := Matrix.single_zero _ _
  map_add' n m := Matrix.single_add _ _ _ _
  map_mul' n m := by
    rw [Matrix.single_mul_single_same]

theorem singleEntry_not_unital : singleEntry ℤ 1 ≠ (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro h
  have hc := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1) h
  change (Matrix.single (0 : Fin 2) 0 (1 : ℤ)) 1 1 =
    (1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 at hc
  norm_num [Matrix.single] at hc

/-- This genuine nonunital map still acts on the original idempotent category. -/
example : IdempotentModel ℤ ⥤ IdempotentModel (Matrix (Fin 2) (Fin 2) ℤ) :=
  functor (singleEntry ℤ)

/-- The functor identity is the image idempotent, with no matrix-unit premise. -/
example (P : IdempotentModel ℤ) :
    (functor (singleEntry ℤ)).map (𝟙 P) = 𝟙 ((functor (singleEntry ℤ)).obj P) :=
  (functor (singleEntry ℤ)).map_id P

/-- Noncommutative source coefficients and complete rectangular morphisms are retained. -/
example {P Q : IdempotentModel (Matrix (Fin 2) (Fin 2) ℤ)} (g : P ⟶ Q) :
    rowHomEquiv (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ)) P.X Q.X
        (hom (singleEntry (Matrix (Fin 2) (Fin 2) ℤ)) g).f =
      (rowHomEquiv (Matrix (Fin 2) (Fin 2) ℤ) P.X Q.X g.f).map
        (singleEntry (Matrix (Fin 2) (Fin 2) ℤ)) :=
  hom_matrix _ _

/-- Coefficients can descend across independent universes. -/
example : IdempotentModel (ULift.{1} ℤ) ⥤ IdempotentModel ℤ :=
  functor (ULift.ringEquiv.toRingHom.toNonUnitalRingHom)

/-- Zero coefficients give actual zero projectives, rather than an assumed unit identity. -/
example (P : IdempotentModel ℤ) :
    Limits.IsZero (obj (0 : ℤ →ₙ+* Matrix (Fin 2) (Fin 2) ℤ) P) :=
  obj_zero_isZero P

#print axioms obj
#print axioms hom
#print axioms functor
#print axioms functorAdditive
#print axioms functorIsExact
#print axioms obj_id
#print axioms obj_comp
#print axioms obj_zero_isZero
#print axioms scalarExtensionNatIso
#print axioms singleEntry_not_unital

#lint only unusedArguments in
  MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel.NonunitalMap

end FGProjectiveCat.IdempotentModel.NonunitalMap.Tests
