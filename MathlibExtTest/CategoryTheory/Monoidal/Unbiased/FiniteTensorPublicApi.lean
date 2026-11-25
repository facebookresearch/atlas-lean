/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor

/-!
# Finite-tensor core — public contract

Compile-time clients for the `flattenAssocLaw` app equation with
its whisker-level unfolding, and the identity flatten/map
interchange component (universe-polymorphic in the target).
-/

@[expose] public section

open CategoryTheory

namespace MathlibExtTest.CategoryTheory.Monoidal.Unbiased.FiniteTensorPublicApi

universe u v uW vW

noncomputable section

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

-- The `flattenAssocLaw` morphism equation at a triple-nested family.
example (N : FiniteFamily (FiniteFamily (FiniteFamily V))) :
    (Functor.isoWhiskerLeft
          (FiniteFamily.map (FiniteFamily.flatten (C := V)))
          (FiniteTensor.flattenIso (V := V)) ≪≫
        Functor.isoWhiskerRight
          (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := V)))
          (FiniteTensor.tensor (V := V))).hom.app N =
      (Functor.isoWhiskerRight FiniteFamily.flattenAssocIso
          (FiniteTensor.tensor (V := V)) ≪≫
        Functor.isoWhiskerLeft
          (FiniteFamily.flatten (C := FiniteFamily V))
          (FiniteTensor.flattenIso (V := V)) ≪≫
        Functor.isoWhiskerRight
          (FiniteFamily.flattenMapIso (FiniteTensor.tensor (V := V)))
          (FiniteTensor.tensor (V := V)) ≪≫
        Functor.isoWhiskerLeft
          (FiniteFamily.map
            (FiniteFamily.map (FiniteTensor.tensor (V := V))))
          (FiniteTensor.flattenIso (V := V))).hom.app N :=
  by exact FiniteTensor.flattenAssocLaw_app N

-- Whisker-level unfolding of the `flattenAssocLaw` app equation.
example (N : FiniteFamily (FiniteFamily (FiniteFamily V))) :
    (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map (FiniteFamily.flatten (C := V))).obj N) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIso
            (FiniteTensor.flattenIso (V := V))).hom.app N) =
      (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flattenAssocIso (C := V)).hom.app N) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.flatten (C := FiniteFamily V)).obj N) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flattenMapIso
            (FiniteTensor.tensor (V := V))).hom.app N) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map
            (FiniteFamily.map
              (FiniteTensor.tensor (V := V)))).obj N) :=
  by exact FiniteTensor.flattenAssocLaw_app_unfold N

-- The flatten/map interchange iso is the identity, across universes.
example {W : Type uW} [Category.{vW} W] (F : V ⥤ W)
    (X : FiniteFamily (FiniteFamily V)) :
    (FiniteFamily.flattenMapIso F).hom.app X = 𝟙 _ :=
  by exact FiniteTensor.flattenMapIso_hom_app_eq_id F X

end

end MathlibExtTest.CategoryTheory.Monoidal.Unbiased.FiniteTensorPublicApi
